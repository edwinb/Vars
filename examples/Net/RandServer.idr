import Network.Socket
import Control.ST
import System

import Network
import Threads

{- A random number server.

This receives requests from a client, as a number, and sends a reply
which is a random number within the requested bound.

There are two states: one for the server, and one for a connected session.
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
            ST m (Maybe Integer) 
                 [conn ::: Connection Waiting :->
                           \res => Connection (case res of
                                                    Nothing => Done
                                                    Just _ => Processing)]
  -- Send a reply, and move the connection to the Done state
  sendResp : (conn : Var) -> Integer ->
             ST m () [conn ::: Connection Processing :-> Connection Done]

  -- Create a server
  start : ST m (Maybe Var) [Add (maybe [] (\srv => [srv ::: Server]))]
  -- Close a server
  quit : (srv : Var) -> ST m () [Remove srv Server]

  -- Listen for an incoming connection. If there is one, create a session
  -- with a connection in the Waiting state
  accept : (srv : Var) ->
           ST m (Maybe Var) 
                [Add (maybe [] (\conn => [conn ::: Connection Waiting])), 
                 srv ::: Server]

interface Sleep (m : Type -> Type) where
  usleep : Int -> m ()

Sleep IO where
  usleep = System.usleep


using (Sleep io, ConsoleIO io, RandomSession io, Conc io)
  rndSession : (conn : Var) -> Integer ->
               ST io () [Remove conn (Connection {m=io} Waiting)]
  rndSession conn seed =
         do Just bound <- call (recvReq conn)
              | Nothing => do lift (putStr "Nothing received\n")
                              delete conn
            lift (putStr "Calculating reply...\n")
            lift (usleep 6000000)
            sendResp conn (seed `mod` (bound + 1))
            delete conn

  rndLoop : (srv : Var) -> Integer -> 
               ST io () [srv ::: Server {m=io}]
  rndLoop srv seed
    = do Just conn <- accept srv
              | Nothing => lift (putStr "accept failed\n")
         lift (putStr "Connection received\n")
         let seed' = (1664525 * seed + 1013904223) 
                             `prim__sremBigInt` (pow 2 32)
         fork {main_res = [srv ::: _]} 
              {thread_res = [conn ::: _]}
              (rndSession conn seed')
         rndLoop srv seed'

  rndServer : Integer -> ST io () []
  rndServer seed 
    = do Just srv <- start
              | Nothing => lift (putStr "Can't start server\n")
         call (rndLoop srv seed)
         quit srv

implementation (ConsoleIO io, Sockets io) => RandomSession io where
  
  Connection Waiting = Sock {m=io} (Open Server)
  Connection Processing = Sock {m=io} (Open Server)
  Connection Done = Sock {m=io} Closed

  Server = Sock {m=io} Listening

  recvReq conn = do Right msg <- recv conn
                          | Left err => pure Nothing
                    lift $ putStr ("Incoming " ++ show msg ++ "\n")
                    pure (Just (cast msg))

  sendResp conn val = do Right () <- send conn (cast val ++ "\n")
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
  
  quit srv = do close srv
                delete srv
  
  accept srv = do Right conn <- accept srv
                        | Left err => pure Nothing -- no incoming message
                  pure (Just conn)

main : IO ()
main = run (rndServer 12345)

