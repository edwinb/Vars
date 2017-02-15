import Control.ST

data Access = LoggedOut | LoggedIn
data LoginResult = OK | BadPassword

interface DataStore (m : Type -> Type) where

  Store : Access -> Type

  connect : ST m Var [Add (\store => [store ::: Store LoggedOut])]
  disconnect : (store : Var) ->
               ST m () [Remove store (Store LoggedOut)]
  login : (store : Var) ->
          ST m LoginResult [store ::: Store LoggedOut :->
                             (\res => Store (case res of
                                                  OK => LoggedIn
                                                  BadPassword => LoggedOut))]
  logout : (store : Var) ->
           ST m () [store ::: Store LoggedIn :-> Store LoggedOut]
  readSecret : (store : Var) ->
               ST m String [store ::: Store LoggedIn]

getData : (ConsoleIO m, DataStore m) => ST m () []
getData = do st <- connect
             success <- login st
             case success of
                  OK => do secret <- readSecret st
                           lift (putStr ("Secret is: " ++ show secret ++ "\n"))
                           logout st
                           disconnect st
                  BadPassword => do lift (putStr "Failure\n")
                                    disconnect st

DataStore IO where
  Store x = Abstract String -- represents secret data

  connect = do store <- new "Secret Data"
               pure store

  disconnect store = delete store

  login store = do lift (putStr "Enter password: ")
                   p <- lift getLine
                   if p == "Mornington Crescent"
                      then pure OK
                      else pure BadPassword
  logout store = pure ()

  readSecret store = do secret <- read store
                        pure secret

main : IO ()
main = run getData

