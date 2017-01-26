module Network

import Control.Vars
import Network.Socket

data Role = Client | Server

data SocketState = Closed
                 | Ready 
                 | Bound 
                 | Listening
                 | Open Role

data CloseOK : SocketState -> Type where
     CloseOpen : CloseOK (Open role)
     CloseListening : CloseOK Listening

interface Sockets (m : Type -> Type) where
  Sock : SocketState -> Type

  socket : SocketType ->
           Vars m (Either () Var)
                  []
                  (either (const []) (\sock => [sock ::: Sock Closed]))

  bind : (sock : Var) -> (addr : Maybe SocketAddress) -> (port : Port) ->
         Vars m (Either () ()) 
                [sock ::: Sock Closed]
                (either (const [sock ::: Sock Closed]) 
                        (const [sock ::: Sock Bound]))
  listen : (sock : Var) ->
           Vars m (Either () ())
                  [sock ::: Sock Bound]
                  (either (const [sock ::: Sock Closed]) 
                          (const [sock ::: Sock Listening]))
  accept : (sock : Var) ->
           Vars m (Either () Var)
                  [sock ::: Sock Listening]
                  (either (const [sock ::: Sock Listening])
                          (\new => [new ::: Sock (Open Server),
                                    sock ::: Sock Listening]))

  connect : (sock : Var) -> SocketAddress -> Port ->
            Vars m (Either () ())
                   [sock ::: Sock Closed]
                   (either (const [sock ::: Sock Closed]) 
                           (const [sock ::: Sock (Open Client)]))
  
  close : (sock : Var) ->
          {auto prf : CloseOK st} ->
          Vars m () [sock ::: Sock st] 
                    (const [sock ::: Sock Closed])

  send : (sock : Var) -> String -> 
         Vars m (Either () ())
                   [sock ::: Sock (Open x)]
                   (either (const [sock ::: Sock (Closed)])
                           (const [sock ::: Sock (Open x)]))
  recv : (sock : Var) ->
         Vars m (Either () String)
                   [sock ::: Sock (Open x)]
                   (either (const [sock ::: Sock Closed])
                           (const [sock ::: Sock (Open x)]))

interface Monad m => ConsoleIO (m : Type -> Type) where
  putStr : String -> m ()
  getStr : m String

rndServer : (ConsoleIO io, Sockets io) =>
            (sock : Var) -> (seed : Integer) ->
            Vars io () [sock ::: Sock {m=io} Listening] 
                (const [sock ::: Sock {m=io} Closed])
rndServer sock seed = 
  do Right new <- accept sock
           | Left err => close sock
     Right msg <- call (recv new)
           | Left err => do delete new; close sock 
     lift (putStr (msg ++ "\n"))
     -- Send reply here
     Right ok <- call (send new ("You said " ++ msg))
           | Left err => do delete new; close sock
     call (close new)
     delete new
     rndServer sock seed

startServer : (ConsoleIO io, Sockets io) =>
              Vars io () [] (const [])
startServer = 
  do Right sock <- socket Stream
           | Left err => pure () -- give up
     Right ok <- bind sock Nothing 9442
           | Left err => delete sock
     Right ok <- listen sock
           | Left err => delete sock
     rndServer sock 123456789
     delete sock

Sockets IO where
  Sock _ = Socket

  socket ty = do Right sock <- lift $ Socket.socket AF_INET ty 0
                      | Left err => pure (Left ())
                 lbl <- new sock
                 pure (Right lbl)
                
  bind sock addr port = do ok <- lift $ bind !(get sock) addr port
                           if ok /= 0
                              then pure (Left ())
                              else pure (Right ())
  listen sock = do ok <- lift $ listen !(get sock)
                   if ok /= 0
                      then pure (Left ())
                      else pure (Right ())
  accept sock = do Right (conn, addr) <- lift $ accept !(get sock)
                         | Left err => pure (Left ())
                   lbl <- new conn
                   pure (Right lbl)

  connect sock addr port 
       = do ok <- lift $ connect !(get sock) addr port
            if ok /= 0
               then pure (Left ())
               else pure (Right ())
  close sock = do lift $ close !(get sock)
                  pure ()
  send sock msg = do Right _ <- lift $ send !(get sock) msg
                           | Left _ => pure (Left ())
                     pure (Right ())
  recv sock = do Right (msg, len) <- lift $ recv !(get sock) 1024 -- Yes, yes...
                       | Left _ => pure (Left ())
                 pure (Right msg)

ConsoleIO IO where
  putStr x = Interactive.putStr x
  getStr = Interactive.getLine

main : IO ()
main = run startServer

