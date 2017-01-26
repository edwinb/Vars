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
     Right msg <- Call (recv new)
           | Left err => do Delete new; close sock 
     Lift (putStr (msg ++ "\n"))
     -- Send reply here
     Right ok <- Call (send new ("You said " ++ msg))
           | Left err => do Delete new; close sock
     Call (close new)
     Delete new
     rndServer sock seed

startServer : (ConsoleIO io, Sockets io) =>
              Vars io () [] (const [])
startServer = 
  do Right sock <- socket Stream
           | Left err => Pure () -- give up
     Right ok <- bind sock Nothing 9442
           | Left err => Delete sock
     Right ok <- listen sock
           | Left err => Delete sock
     rndServer sock 123456789
     Delete sock

Sockets IO where
  Sock _ = Socket

  socket ty = do Right sock <- Lift $ Socket.socket AF_INET ty 0
                      | Left err => Pure (Left ())
                 lbl <- New sock
                 Pure (Right lbl)
                
  bind sock addr port = do ok <- Lift $ bind !(Get sock) addr port
                           if ok /= 0
                              then Pure (Left ())
                              else Pure (Right ())
  listen sock = do ok <- Lift $ listen !(Get sock)
                   if ok /= 0
                      then Pure (Left ())
                      else Pure (Right ())
  accept sock = do Right (conn, addr) <- Lift $ accept !(Get sock)
                         | Left err => Pure (Left ())
                   lbl <- New conn
                   Pure (Right lbl)

  connect sock addr port 
       = do ok <- Lift $ connect !(Get sock) addr port
            if ok /= 0
               then Pure (Left ())
               else Pure (Right ())
  close sock = do Lift $ close !(Get sock)
                  Pure ()
  send sock msg = do Right _ <- Lift $ send !(Get sock) msg
                           | Left _ => Pure (Left ())
                     Pure (Right ())
  recv sock = do Right (msg, len) <- Lift $ recv !(Get sock) 1024 -- Yes, yes...
                       | Left _ => Pure (Left ())
                 Pure (Right msg)

ConsoleIO IO where
  putStr x = Interactive.putStr x
  getStr = Interactive.getLine

main : IO ()
main = run startServer

