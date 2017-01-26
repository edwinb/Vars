import Network.Socket
import Network
import Control.Vars

data SessionState = Waiting
                  | Processing
                  | Done

interface RandomSession (m : Type -> Type) where
  Connection : SessionState -> Type
  Server : Type

  recvReq : (conn : Var) ->
            Vars m (Maybe Integer) [conn ::: Connection Waiting]
                   (\res => [conn ::: Connection (case res of
                                                    Nothing => Done
                                                    Just _ => Processing)])
  sendResp : (conn : Var) -> Integer ->
             Vars m () [conn ::: Connection Processing]
              (\res => [conn ::: Connection Done])

  start : Vars m (Maybe Var) [] (maybe [] (\srv => [srv ::: Server]))
  quit : (srv : Var) -> Vars m () [srv ::: Server] (const [])

  accept : (srv : Var) ->
           Vars m (Maybe Var) [srv ::: Server]
                  (maybe [srv ::: Server] 
                         (\conn => [conn ::: Connection Waiting,
                                    srv ::: Server]))

rndSession : (ConsoleIO io, RandomSession io) =>
             (srv : Var) -> Integer -> 
             Vars io () [srv ::: Server {m=io}]
                 (const [srv ::: Server {m=io}])
rndSession srv seed
  = do Just conn <- accept srv
            | Nothing => lift (putStr "accept failed\n")
       Just val <- call (recvReq conn)
            | Nothing => do lift (putStr "Nothing received\n")
                            delete conn
       -- TODO: Send a random number from the seed here
       call (sendResp conn val)
       delete conn
       rndSession srv seed

rndServer : (ConsoleIO io, RandomSession io) =>
            Integer -> Vars io () [] (const [])
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

