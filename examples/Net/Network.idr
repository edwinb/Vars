module Network

import Control.Vars
import Network.Socket

public export
data Role = Client | Server

public export
data SocketState = Closed
                 | Ready 
                 | Bound 
                 | Listening
                 | Open Role

public export
data CloseOK : SocketState -> Type where
     CloseOpen : CloseOK (Open role)
     CloseListening : CloseOK Listening

public export
interface Sockets (m : Type -> Type) where
  Sock : SocketState -> Type

  socket : SocketType ->
           Vs m (Either () Var)
                [Add (either (const []) (\sock => [sock ::: Sock Closed]))]

  bind : (sock : Var) -> (addr : Maybe SocketAddress) -> (port : Port) ->
         Vs m (Either () ()) 
              [sock ::: Sock Closed :->
                        either (const (Sock Closed)) (const (Sock Bound))]
  listen : (sock : Var) ->
           Vs m (Either () ())
              [sock ::: Sock Bound :-> 
                        either (const (Sock Closed)) (const (Sock Listening))]
  accept : (sock : Var) ->
           Vs m (Either () Var)
                [Add (either (const []) 
                      (\new => [new ::: Sock (Open Server)])),
                 sock ::: Sock Listening]

  connect : (sock : Var) -> SocketAddress -> Port ->
            Vs m (Either () ())
               [sock ::: Sock Closed :->
                     either (const (Sock Closed)) (const (Sock (Open Client)))]
  
  close : (sock : Var) ->
          {auto prf : CloseOK st} ->
          Vs m () [sock ::: Sock st :-> Sock Closed] 

  send : (sock : Var) -> String -> 
         Vs m (Either () ())
              [sock ::: Sock (Open x) :->
                        either (const (Sock Closed))
                               (const (Sock (Open x)))]
  recv : (sock : Var) ->
         Vs m (Either () String)
              [sock ::: Sock (Open x) :->
                        either (const (Sock Closed))
                               (const (Sock (Open x)))]

public export
interface Monad m => ConsoleIO (m : Type -> Type) where
  putStr : String -> m ()
  getStr : m String

export
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

export
ConsoleIO IO where
  putStr x = Interactive.putStr x
  getStr = Interactive.getLine


