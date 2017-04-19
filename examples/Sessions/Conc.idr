import Control.ST
import Control.ST.ImplicitCall
import System.Concurrency.Channels

data Actions : Type where
     Send : (a : Type) -> (a -> Actions) -> Actions
     Recv : (a : Type) -> (a -> Actions) -> Actions
     Done : Actions

dual : Actions -> Actions
dual (Send a f) = Recv a (\x => dual (f x))
dual (Recv a f) = Send a (\x => dual (f x))
dual Done = Done

data ServerState = Ready | Processed

interface Conc (m : Type -> Type) where
  data Channel : Actions -> Type
  data Server : Actions -> Type
  Accepting : ServerState -> Actions -> Type

  -- Fork a child thread. Share current resources (all) between child
  -- thread (thread_res) and parent thread (kept tprf).
  -- The child thread has a channel with the 'child' protocol, and the parent
  -- thread has its dual
  fork : (thread : (chan : Var) ->
                   STrans m () ((chan ::: Channel child) :: thread_res) 
                               (const [])) -> 
         {auto tprf : SubRes thread_res all} ->
         STrans m Var all (\chan => 
                          ((chan ::: Channel (dual child)) :: kept tprf))

  -- Start a server running, ready to accept connections to create a channel
  -- which runs 'proto'. We don't provide a way to delete 'Accepting', so
  -- this has to run forever... (or crash...)
  -- Returns a reference to the server which we can connect to as many
  -- times as we like.
  -- (TODO: Make this work as a total, productive function)
  start : (server : (acc : Var) ->
             STrans m () ((acc ::: Accepting Ready proto) :: thread_res)
                 (const ((acc ::: Accepting Processed proto) :: thread_res))) ->
          {auto tprf : SubRes thread_res all} ->
          STrans m (Server proto) all (const (kept tprf))

  -- Listen for a connection on acc, making a new channel
  listen : (acc : Var) -> (timeout : Int) ->
           ST m (Maybe Var) [acc ::: Accepting Ready proto :->
                                     Accepting Processed proto,
                             addIfJust (Channel proto)]
  -- Connect to a server and make a new channel for talking to it with
  -- the appropriate protocol
  connect : Server proto -> ST m Var [add (Channel (dual proto))]

  -- Can only 'send' if the channel is ready to send a ty
  send : (chan : Var) -> (val : ty) ->
         ST m () [chan ::: Channel (Send ty f) :-> Channel (f val)]
  -- Can only 'recv' if the channel is ready to receive a ty
  recv : (chan : Var) -> 
         ST m ty [chan ::: Channel (Recv ty f) :-> (\res => Channel (f res))]

  -- Can only 'close' when a protocol is Done
  close : (chan : Var) -> ST m () [Remove chan (Channel Done)]

ChildProc : Var -> (m : Type -> Type) -> Conc m => Actions -> Action ()
ChildProc chan m proto = Remove chan (Channel {m} proto)

ServerProc : Var -> (m : Type -> Type) -> Conc m => Actions -> Action ()
ServerProc chan m proto = chan ::: Accepting {m} Ready proto :->
                                   Accepting {m} Processed proto

-- A server which receives two Ints then sends an Int back
AddServer : Actions
AddServer = Recv Int (const (Recv Int (const (Send Int (const Done)))))

-- addServer sits there waiting for connections. When they arrive, talk
-- to the client using the 'AddServer' protocol.
-- The type says that we start ready to receive connections on the
-- 'server' resource, and by the end we've deleted the 'server' resource.

-- Since there's no way to delete the 'server' resource, we'll have to
-- keep looping... (TODO: We don't actually guarantee that we'll respond
-- to any requests either... so when we work out how to make this total,
-- make sure we do that as well.)
addServer : (ConsoleIO m, Conc m) => 
            (counter : Var) ->
            (server : Var) -> 
            ST m () [ServerProc server m AddServer,
                     counter ::: State Int]
addServer counter server = with ST do
        Just chan <- listen server 1
             | Nothing => pure ()
        val <- read counter
        putStr $ "Request number " ++ show val ++ "\n"
        write counter (val + 1)
        num1 <- recv chan
        num2 <- recv chan
        send chan (num1 + num2)
        close chan


-- Connect to a server which is using the 'AddServer' protocol and ask
-- it to add things
callAdd : (ConsoleIO m, Conc m) => 
          Server {m} AddServer -> Int -> Int -> ST m () []
callAdd server x y = with ST do
        chan <- connect server
        send chan x
        send chan y
        putStr "Adding is happening\n"
        ans <- recv chan
        close chan 
        putStr $ "Result: " ++ show ans ++ "\n"

-- Start up an addition server, and ask it a couple of questions
runAddServer : (ConsoleIO m, Conc m) => ST m () []
runAddServer = with ST do
     putStr "Starting server\n"
     counter <- new 0
     serverID <- start (addServer counter)
     callAdd serverID 20 22
     callAdd serverID 40 54

%hint
inStateEnd : InState lbl st (xs ++ [lbl ::: st])
inStateEnd {xs = []} = Here
inStateEnd {xs = (x :: xs)} = There inStateEnd

-- To run our programs, we need to implement the 'Conc' interface under IO
-- This is really hacky and involves lots of unsafe primitives. Fortunately,
-- we only have to get this right once... but we do have to get it right.

-- So. Move along. Nothing to see here :).

-- If any of the believe_mes in here get executed, we have a disastrous
-- failure caused by being out of memory (or other similar problem). 
-- Nevertheless, TODO: clean them up. (It can be done with proper error 
-- handling)
Conc IO where
  Channel x = State Channels.Channel
  Server x = PID
  Accepting _ _ = ()

  fork thread {tprf} = do
         threadEnv <- dropSub {prf=tprf}
          -- Need to create a dummy resource to feed to the new
          -- thread, to stand for the 'Channel' variable which
          -- we'll create a proper value for when we spawn.
         dummy <- new ()
         Just pid <- lift $ spawn (do Just chan <- listen 1
                                      runWith (Value chan :: threadEnv)
                                              (thread dummy)
                                      pure ())
              | Nothing => believe_me () -- Disastrous failure...
         delete dummy
         Just ch <- lift $ connect pid
              | Nothing => believe_me () -- Disastrous failure...
         new ch

  start server {thread_res} {tprf} = do
         threadEnv <- dropSub {prf=tprf}
         -- Need to create a dummy resource to feed to the new
         -- thread, to stand for the 'Accepting' resource which
         -- is only there to say what kind of protocols it will
         -- work with
         dummy <- new ()
         Just pid <- lift $ spawn (do runWithLoop
                                          (() :: threadEnv) 
                                          forever
                                          (serverLoop server dummy)
                                      pure ())
             | Nothing => believe_me () -- Disastrous failure...
         delete dummy
         pure pid
    where serverLoop : ((acc : Var) -> 
             STrans IO () ((acc ::: ()) :: thread_res)
                   (const ((acc ::: ()) :: thread_res))) ->
             (acc : Var) -> STransLoop IO () ((acc ::: ()) :: thread_res)
                                      (const ((acc ::: ()) :: thread_res))
          serverLoop f acc = do f acc
                                serverLoop f acc

  listen acc timeout = do Just ch <- lift $ listen timeout
                               | Nothing => pure Nothing
                          chvar <- new ch
                          toEnd chvar
                          pure (Just chvar)
  connect pid = do Just ch <- lift $ connect pid
                        | Nothing => believe_me () -- Disastrous failure...
                   new ch
  send chan val = do ch <- read chan
                     lift $ unsafeSend ch val
                     pure ()
  recv {ty} chan = do ch <- read chan
                      Just val <- lift $ unsafeRecv ty ch
                           | Nothing => believe_me () -- Can't happen!
                      pure val
  close chan = delete chan

-- Finally, run the thing
main : IO ()
main = run runAddServer

-- Local Variables:
-- idris-packages: ("contrib")
-- End:
