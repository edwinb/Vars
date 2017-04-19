module Network

import Control.ST
import Control.ST.ImplicitCall
import Network.Socket

public export
data SocketState = Ready
                 | Bound 
                 | Listening
                 | Open 
                 | Closed

public export
data CloseOK : SocketState -> Type where
     CloseOpen : CloseOK Open
     CloseListening : CloseOK Listening

-- Sockets API. By convention, the methods return 'Left' on failure or
-- 'Right' on success (even if the error/result is merely unit).
public export
interface Sockets (m : Type -> Type) where
  Sock : SocketState -> Type

  -- Create a new socket. If successful, it's in the Closed state
  socket : SocketType ->
           ST m (Either () Var) [addIfRight (Sock Ready)]

  -- Bind a socket to a port. If successful, it's moved to the Bound state.
  bind : (sock : Var) -> (addr : Maybe SocketAddress) -> (port : Port) ->
         ST m (Either () ()) 
              [sock ::: Sock Ready :-> (Sock Closed `or` Sock Bound)]
  -- Listen for connections on a socket. If successful, it's moved to the
  -- Listening state
  listen : (sock : Var) ->
           ST m (Either () ())
              [sock ::: Sock Bound :-> (Sock Closed `or` Sock Listening)]
  -- Accept an incoming connection on a Listening socket. If successful, 
  -- creates a new socket in the Open Server state, and keeps the existing
  -- socket in the Listening state
  accept : (sock : Var) ->
           ST m (Either () Var)
                [sock ::: Sock Listening, addIfRight (Sock Open)]

  -- Connect to a remote address on a socket. If successful, moves to the
  -- Open Client state
  connect : (sock : Var) -> SocketAddress -> Port ->
            ST m (Either () ())
               [sock ::: Sock Ready :-> (Sock Closed `or` Sock Open)]
  
  -- Close an Open or Listening socket
  close : (sock : Var) ->
          {auto prf : CloseOK st} ->
          ST m () [sock ::: Sock st :-> Sock Closed]

  remove : (sock : Var) ->
           ST m () [Remove sock (Sock Closed)]

  -- Send a message on a connected socket.
  send : (sock : Var) -> String -> 
         ST m (Either () ()) [sock ::: Sock Open]
  -- Receive a message on a connected socket
  recv : (sock : Var) ->
         ST m (Either () String) [sock ::: Sock Open] 
export
implementation Sockets IO where
  Sock _ = State Socket

  socket ty = do Right sock <- lift $ Socket.socket AF_INET ty 0
                      | Left err => pure (Left ())
                 lbl <- new sock
                 pure (Right lbl)
                
  bind sock addr port = do ok <- lift $ bind !(read sock) addr port
                           if ok /= 0
                              then pure (Left ())
                              else pure (Right ())
  listen sock = do ok <- lift $ listen !(read sock)
                   if ok /= 0
                      then pure (Left ())
                      else pure (Right ())
  accept sock = do Right (conn, addr) <- lift $ accept !(read sock)
                         | Left err => pure (Left ())
                   lbl <- new conn
                   returning (Right lbl) (toEnd lbl)

  connect sock addr port 
       = do ok <- lift $ connect !(read sock) addr port
            if ok /= 0
               then pure (Left ())
               else pure (Right ())
  close sock = do lift $ close !(read sock)
                  pure ()
  remove sock = delete sock

  send sock msg = do Right _ <- lift $ send !(read sock) msg
                           | Left _ => pure (Left ())
                     pure (Right ())
  recv sock = do Right (msg, len) <- lift $ recv !(read sock) 1024 -- Yes, yes...
                       | Left _ => pure (Left ())
                 pure (Right msg)

-- A socket which buffers what has been read so far, and allows access to
-- data received line by line rather than chunk by chunk.
public export
interface Sockets m => BufferedSocket (m : Type -> Type) where
  OpenSocket : Type

  makeBuffered : (sock : Var) -> 
                 ST m Var [remove sock (Sock {m} Open), add OpenSocket]
  closeBuffered : (sock : Var) -> ST m () [remove sock OpenSocket]

  -- Get the next line from a socket, if any
  readLine : (sock : Var) -> ST m (Maybe String) [sock ::: OpenSocket]

  sendLine : (sock : Var) -> String -> ST m () [sock ::: OpenSocket]

  -- Receive all the messages from a socket and buffer them
  bufferedRecv : (sock : Var) -> ST m () [sock ::: OpenSocket]

getFirstLine : String -> Maybe (String, String)
getFirstLine "" = Nothing
getFirstLine str = case span (/='\n') str of
                        (str', "") => Just (str', "")
                        (str', rest) => Just (str', assert_total (strTail rest))

-- Receive until something received has a '\n' in it
keepRecv : Sockets m => (sock : Var) -> (acc : String) ->
                        ST m String [sock ::: Sock {m} Open]
keepRecv sock acc = if elem '\n' (unpack acc)
                       then pure acc
                       else do Right dat <- recv sock
                                    | Left () => pure acc
                               keepRecv sock (acc ++ dat)

export
implementation Sockets m => BufferedSocket m where
  OpenSocket = Composite [Sock {m} Open, -- underlying socket
                          State String]  -- data so far

  makeBuffered sock = do str <- new ""
                         buf <- new ()
                         combine buf [sock, str]
                         pure buf

  closeBuffered rec = do [sock, buf] <- split rec
                         delete rec; delete buf; close sock; remove sock

  readLine rec = do bufferedRecv rec
                    [sock, buf] <- split rec
                    str <- read buf
                    case getFirstLine str of
                         Nothing => do combine rec [sock, buf]
                                       pure Nothing
                         Just (str', rest) =>
                                    do write buf rest
                                       combine rec [sock, buf]
                                       pure (Just str')

  sendLine rec msg = do [sock, buf] <- split rec
                        send sock msg
                        combine rec [sock, buf]

  bufferedRecv rec = do [sock, buf] <- split rec
                        str <- read buf
                        dat <- keepRecv sock str
                        write buf dat
                        combine rec [sock, buf]

