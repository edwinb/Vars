import Network.Socket
import Control.Vars

import Network
import Async

{- A random number server.

This receives requests from a client, as a number, and sends a reply
which is a random number within the requested bound.

There are two states: one for the server, and one for a connection session.
The server repeatedly listens for requests and creats a session for each
incoming request.
-}

-- States of a connected session
data SessionState = Waiting -- waiting for the client to send
                  | Processing -- calculating a response to send back
                  | Done -- received message and replied to it

interface RandomSession (m : Type -> Type) where
  -- A connected session
  Connection : SessionState -> Type
  -- A server listening for connections
  Server : Type

  -- Receive a request on a Waiting connection. If there is a request
  -- available, move to the Processing state
  recvReq : (conn : Var) ->
            Vars m (Maybe Integer) 
                 [conn ::: Connection Waiting :->
                           \res => Connection (case res of
                                                    Nothing => Done
                                                    Just _ => Processing)]
  -- Send a reply, and move the connection to the Done state
  sendResp : (conn : Var) -> Integer ->
             Vars m () [conn ::: Connection Processing :-> Connection Done]

  -- Create a server
  start : Vars m (Maybe Var) [Add (maybe [] (\srv => [srv ::: Server]))]
  -- Close a server
  quit : (srv : Var) -> Vars m () [Remove srv Server]

  -- Listen for an incoming connection. If there is one, create a session
  -- with a connection in the Waiting state
  accept : (srv : Var) ->
           Vars m (Maybe Var) 
                [Add (maybe [] (\conn => [conn ::: Connection Waiting])), 
                 srv ::: Server]

rndSession : (ConsoleIO io, RandomSession io) =>
             (srv : Var) -> Integer -> 
             Vars io () [srv ::: Server {m=io}]
rndSession srv seed
  = do Just conn <- accept srv
            | Nothing => lift (putStr "accept failed\n")
       Just bound <- call (recvReq conn)
            | Nothing => do lift (putStr "Nothing received\n")
                            delete conn
       let seed' = (1664525 * seed + 1013904223) 
                           `prim__sremBigInt` (pow 2 32)
       call (sendResp conn (seed' `mod` (bound + 1)))
       delete conn
       rndSession srv seed'

rndServer : (ConsoleIO io, RandomSession io) =>
            Integer -> Vars io () []
rndServer seed 
  = do Just srv <- start
            | Nothing => lift (putStr "Can't start server\n")
       call (rndSession srv seed)
       quit srv

(ConsoleIO io, Sockets io) => RandomSession io where
  
  Connection Waiting = Sock {m=io} (Open Server)
  Connection Processing = Sock {m=io} (Open Server)
  Connection Done = Sock {m=io} Closed

  Server = Sock {m=io} Listening

  recvReq conn = do Right msg <- recv conn
                          | Left err => pure Nothing
                    lift $ putStr ("Incoming " ++ show msg ++ "\n")
                    pure (Just (cast msg))

  sendResp conn val = do Right () <- send conn (cast val)
                               | Left err => pure ()
                         close conn
  
  start = do Right sock <- socket Stream
                   | Left err => pure Nothing
             Right () <- bind sock Nothing 9442
                   | Left err => do delete sock
                                    pure Nothing
             Right () <- listen sock
                   | Left err => do delete sock
                                    pure Nothing
             lift $ putStr "Started server\n"
             pure (Just sock)
  
  quit srv = delete srv
  
  accept srv = do Right conn <- accept srv
                        | Left err => pure Nothing -- no incoming message
                  pure (Just conn)

main : IO ()
main = run (rndServer 12345)

