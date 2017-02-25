import System
import Control.ST
import System.Concurrency.Channels

-- Simple asynchronous calls
interface Async (m : Type -> Type) where
  Promise : Type -> Type

  -- Run an asynchronous action in another thread. Creates a 'promise' as
  -- a variable which will contain the result when it's done
  async : (action : ST m a []) -> 
          ST m (Maybe Var) [Add (maybe [] (\p => [p ::: Promise a]))]

  -- Get the result from a promise, and delete it
  getResult : (p : Var) -> ST m (Maybe a) [Remove p (Promise a)]
     
-- A channel for transmitting a specific type
data TChannel : Type -> Type where
     MkTChannel : Channel -> TChannel a

{- Asynchronous programming using channels in IO. The error checking here
leaves something to be desired... if creating a channel fails between
the caller and the callee then getResult will block. However, if creating
a channel has failed, it's probably a more disastrous RTS problem like
running out of memory... -}
Async IO where
  Promise ty = State (TChannel ty)

  -- In IO, spawn a thread and create a channel for communicating with it
  -- Store the channel in the Promise
  async prog = do Just pid <- lift $ spawn (do Just chan <- listen 10
                                                     | Nothing => pure ()
                                               res <- run prog
                                               unsafeSend chan res
                                               pure ())
                       | Nothing => pure Nothing
                  Just chan <- lift $ connect pid
                       | Nothing => pure Nothing
                  promise <- new (MkTChannel chan)
                  pure (Just promise)
  -- Receive a message on the channel in the promise. unsafeRecv will block
  -- until it's there
  getResult {a} p = do MkTChannel chan <- read p
                       delete p
                       lift $ unsafeRecv a chan

calcThread : Nat -> IO Nat
calcThread Z = pure Z
calcThread (S k) = do putStrLn "Counting"
                      usleep 1000000
                      v <- calcThread k
                      pure (v + k)

asyncMain : ST IO () []
asyncMain = do Just promise <- async (lift (calcThread 10))
                    | Nothing => lift (putStrLn "Async call failed")
               lift (putStrLn "Main thread")
               lift (putStr "What's your name? ")
               name <- lift getLine 
               lift (putStrLn ("Hello " ++ name))
               lift (putStrLn "Waiting for the answer")
               Just result <- getResult promise
                    | Nothing => lift (putStrLn "Getting result failed")
               lift (printLn result)

main : IO ()
main = run asyncMain

