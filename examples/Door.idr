import Control.Vars

data DoorState = DoorOpen | DoorClosed
data Result = Jam | OK

interface Door (m : Type -> Type) where
    DoorType : DoorState -> Type
    
    newDoor : Vars m Label [] (\d => [d ::: DoorType DoorClosed])
    doorOpen : (d : Label) -> 
                  Vars m Result 
                         [d ::: DoorType DoorClosed] 
                (\res => [d ::: DoorType (case res of
                                               Jam => DoorClosed
                                               OK => DoorOpen)])
    doorClose : (d : Label) -> Vars m Result [d ::: DoorType DoorOpen]
                                      (const [d ::: DoorType DoorClosed])

doorProg : Door m => Vars m () [] (const [])
doorProg = do d <- newDoor
              ok <- doorOpen d
              case ok of
                   Jam => Delete d
                   OK => do doorClose d
                            Delete d

