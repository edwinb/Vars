import Control.ST

data DoorState = DoorOpen | DoorClosed
data Result = Jam | OK

interface Door (m : Type -> Type) where
    DoorType : DoorState -> Type
   
    -- Create a new door in the closed state
    newDoor : ST m Var [Add (\d => [d ::: DoorType DoorClosed])]

    -- Attempt to open a door. If it jams, the door remains DoorClosed,
    -- if successful it becomes DoorOpen
    doorOpen : (d : Var) -> 
               ST m Result 
                    [d ::: DoorType DoorClosed :->
                           (\res => DoorType (case res of
                                                 Jam => DoorClosed
                                                 OK => DoorOpen))]
    -- Close an open door
    doorClose : (d : Var) -> 
                ST m Result [d ::: DoorType DoorOpen :-> 
                                   DoorType DoorClosed]

doorProg : Door m => ST m () []
doorProg = do d <- newDoor
              OK <- doorOpen d
                 | Jam => delete d
              doorClose d
              delete d

