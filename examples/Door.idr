import Control.Vars

data DoorState = DoorOpen | DoorClosed
data Result = Jam | OK

interface Door (m : Type -> Type) where
    DoorType : DoorState -> Type
   
    -- Create a new door in the closed state
    newDoor : Vs m Var [Add (\d => [d ::: DoorType DoorClosed])]

    -- Attempt to open a door. If it jams, the door remains DoorClosed,
    -- if successful it becomes DoorOpen
    doorOpen : (d : Var) -> 
               Vs m Result 
                    [d ::: DoorType DoorClosed :->
                           (\res => DoorType (case res of
                                                 Jam => DoorClosed
                                                 OK => DoorOpen))]
    -- Close an open door
    doorClose : (d : Var) -> 
                Vs m Result [d ::: DoorType DoorOpen :-> 
                                   DoorType DoorClosed]

doorProg : Door m => Vs m () []
doorProg = do d <- newDoor
              OK <- doorOpen d
                 | Jam => delete d
              doorClose d
              delete d

