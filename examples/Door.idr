import Control.ST

data DoorState = DoorOpen | DoorClosed
data Result = Jammed | OK

interface Door (m : Type -> Type) where
    DoorType : DoorState -> Type
   
    -- Create a new door in the closed state
    newDoor : ST m Var [Add (\d => [d ::: DoorType DoorClosed])]

    -- Ring the bell on a closed door
    ringBell : (d : Var) -> ST m () [d ::: DoorType DoorClosed]

    -- Attempt to open a door. If it jams, the door remains DoorClosed,
    -- if successful it becomes DoorOpen
    doorOpen : (d : Var) -> 
               ST m Result 
                    [d ::: DoorType DoorClosed :->
                           (\res => DoorType (case res of
                                                 Jammed => DoorClosed
                                                 OK => DoorOpen))]
    -- Close an open door
    doorClose : (d : Var) -> 
                ST m () [d ::: DoorType DoorOpen :-> 
                               DoorType DoorClosed]

doorProg : Door m => ST m () []
doorProg = do d <- newDoor
              ringBell d
              OK <- doorOpen d
                 | Jammed => delete d
              doorClose d
              delete d

