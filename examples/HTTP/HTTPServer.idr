import Network.Socket
import Control.ST
import Control.ST.ImplicitCall

import Network
import Threads
import HTTPMessage

%default covering

-- States of a connected session. 
data SessionState = Waiting -- waiting for the client to send
                  | Processing Connection -- calculating a response to send back
                        -- 'Connection' is either 'Close' or 'KeepAlive' and notes whether the
                        -- session should continue waiting for client requests after the response
                        -- is sent
                  | Done -- received message, replied to it, no more requests expected

onResponse : Connection -> SessionState
onResponse KeepAlive = Waiting -- keep alive, so go back to the start
onResponse Close = Done -- not keep alive, so don't accept any more requests

interface HTTPSession (m : Type -> Type) where
  -- A connected session
  Session : SessionState -> Type
  -- A server listening for connections
  Server : Type

  -- Receive an HTTP request. If nothing is received (timeout) move to the
  -- 'Done' state. Otherwise move to the 'Processing' state and note whether
  -- the request wanted to keep the connection alive
  recvReq : (conn : Var) -> (timeout : Int) ->
            ST m (Maybe HTTPRequest)
                 [conn ::: Session Waiting :->
                           \res => Session (case res of
                                                 Nothing => Done -- timeout
                                                 Just req => Processing (keep (content req)))]

  -- Send a response. Move to the 'Done' state if keep-alive is not set,
  -- otherwise move back to the Waiting state. (See 'onResponse')
  sendResp : (conn : Var) -> (resp : HTTPResponse) ->
             ST m ()
                [conn ::: Session (Processing keepalive) :->
                          Session (onResponse (keep (content resp)))]

  -- Create a server
  start : (port : Int) -> ST m (Maybe Var) [addIfJust Server]
  -- Close a server
  quit : (srv : Var) -> ST m () [remove srv Server]
  -- Finish a connection
  done : (conn : Var) -> ST m () [remove conn (Session Done)]

  -- Listen for an incoming connection. If there is one, create a session
  -- with a connection in the Waiting state
  accept : (srv : Var) ->
           ST m (Maybe Var) 
                [srv ::: Server, addIfJust (Session Waiting)]

using (ConsoleIO io, HTTPSession io, Conc io)
  httpSession : (conn : Var) -> 
                HTTPProc io -> -- Function to process request
                ST io () [remove conn (Session {m=io} Waiting)]
  httpSession conn proc = 
     do Just req <- recvReq conn 30
             | Nothing => done conn -- Nothing received/timeout
        response <- proc req
        sendResp conn response
        continue (keep (content response)) proc -- continue if keep-alive is set in response
    where continue : (keep : _) -> HTTPProc io ->
                     ST io () [remove conn (Session {m=io} (onResponse keep))]
          continue KeepAlive proc = httpSession conn proc
          continue Close proc = done conn

  httpLoop : (srv : Var) -> HTTPProc io -> ST io () [srv ::: Server {m=io}]
  httpLoop srv proc
    = do Just conn <- accept srv
              | Nothing => putStr "accept failed\n"
         putStr "Connection received\n"
         fork (httpSession conn proc)
         httpLoop srv proc

  httpServer : HTTPProc io -> ST io () []
  httpServer proc
    = do Just srv <- start 8080
              | Nothing => putStr "Can't start server\n"
         httpLoop srv proc
         quit srv

implementation (ConsoleIO io, BufferedSocket io) => HTTPSession io where
  Session st = OpenSocket {m=io} 
  Server = Sock {m=io} Listening

  recvReq conn timeout = ?recvReq_rhs

  sendResp conn resp = sendLine conn (show resp)

  start port = do Right sock <- socket Stream
                       | Left err => pure Nothing
                  Right () <- bind sock Nothing port
                       | Left err => do remove sock; pure Nothing
                  Right () <- listen sock
                       | Left err => do remove sock; pure Nothing
                  putStrLn "Off we go!"
                  pure (Just sock)

  quit sock = do close sock; remove sock
  done conn = closeBuffered conn
  accept sock = do Right conn <- accept sock
                        | Left err => pure Nothing
                   bsock <- makeBuffered conn
                   pure (Just bsock)

-- A dummy response, for a hello world web server
dummyResp : HTTPProc io
dummyResp req
   = pure $ MkResponse (MkCode 200) "HTTP/1.1"
            (MkContent (keep (content req))
                       [("Content-type", "text/html")] "Hello!")

main : IO ()
main = run (httpServer dummyResp)

