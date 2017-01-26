import Network.Socket
import Network
import Control.Vars

echoServer : (ConsoleIO io, Sockets io) =>
             (sock : Var) -> 
             Vars io () [sock ::: Sock {m=io} Listening] 
                 (const [sock ::: Sock {m=io} Closed])
echoServer sock = 
  do Right new <- accept sock
           | Left err => close sock
     Right msg <- call (recv new)
           | Left err => do delete new; close sock 
     lift (putStr (msg ++ "\n"))
     Right ok <- call (send new ("You said " ++ msg))
           | Left err => do delete new; close sock
     call (close new)
     delete new
     echoServer sock

startServer : (ConsoleIO io, Sockets io) =>
              Vars io () [] (const [])
startServer = 
  do Right sock <- socket Stream
           | Left err => pure () -- give up
     Right ok <- bind sock Nothing 9442
           | Left err => delete sock
     Right ok <- listen sock
           | Left err => delete sock
     echoServer sock
     delete sock

main : IO ()
main = run startServer
