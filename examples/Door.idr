import Control.Vars

data DoorState = DoorOpen | DoorClosed
data Result = Jam | OK

interface Door (m : Type -> Type) where
    DoorType : DoorState -> Type
    
    newDoor : Vs m Var [Add (\d => [d ::: DoorType DoorClosed])]
    doorOpen : (d : Var) -> 
               Vs m Result 
                    [d ::: DoorType DoorClosed :->
                           (\res => DoorType (case res of
                                                 Jam => DoorClosed
                                                 OK => DoorOpen))]
    doorClose : (d : Var) -> 
                Vs m Result [d ::: DoorType DoorOpen :-> 
                                   DoorType DoorClosed]

doorProg : Door m => Vs m () []
doorProg = do d <- newDoor
              ok <- doorOpen d
              case ok of
                   Jam => delete d
                   OK => do doorClose d
                            delete d

