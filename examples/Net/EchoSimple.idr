import Network.Socket
import Network
import Control.ST

echoServer : (ConsoleIO io, Sockets io) =>
             (sock : Var) -> 
             ST io () [Remove sock (Sock {m=io} Listening)]
echoServer sock = 
  do Right new <- accept sock
           | Left err => do close sock
                            remove sock
     Right msg <- call (recv new)
           | Left err => do call (close sock); call (remove sock)
                            call (remove new)
     lift (putStr (msg ++ "\n"))
     Right ok <- call (send new ("You said " ++ msg))
           | Left err => do call (remove new); close sock; remove sock
     call (close new)
     call (remove new)
     echoServer sock

startServer : (ConsoleIO io, Sockets io) =>
              ST io () [] 
startServer = 
  do Right sock <- socket Stream
           | Left err => pure () -- give up
     Right ok <- bind sock Nothing 9442
           | Left err => call (remove sock)
     Right ok <- listen sock
           | Left err => call (remove sock)
     echoServer sock

main : IO ()
main = run startServer

