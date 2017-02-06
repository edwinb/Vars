module State

import Control.ST

export
State : Type -> Type
State t = Abstract t

export
get : (x : Var) -> ST m t [x ::: State t]
get x = read x

export
put : (x : Var) -> t' -> ST m () [x ::: State t :-> State t']
put x = write x 
