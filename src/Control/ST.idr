module Control.ST

%default total

infix 5 :::

{- A resource is a pair of a label and the current type stored there -}
public export
data Resource : Type where
     MkRes : label -> state -> Resource

%error_reverse
public export
(:::) : label -> state -> Resource
(:::) = MkRes

public export
data Var = MkVar -- Phantom, just for labelling purposes

{- Contexts for holding current resources states -}
namespace Context
  public export
  data Context : Type where
       Nil : Context
       (::) : Resource -> Context -> Context

  public export
  (++) : Context -> Context -> Context
  (++) [] ys = ys
  (++) (x :: xs) ys = x :: xs ++ ys

{- Proof that a label has a particular type in a given context -}
public export
data InState : lbl -> state -> Context -> Type where
     Here : InState lbl st (MkRes lbl st :: rs)
     There : InState lbl st rs -> InState lbl st (r :: rs)

{- Update an entry in a context with a new state -}
public export
updateCtxt : (ctxt : Context) -> 
             InState lbl st ctxt -> state -> Context
updateCtxt (MkRes lbl _ :: rs) Here val = (MkRes lbl val :: rs)
updateCtxt (r :: rs) (There x) ty = r :: updateCtxt rs x ty

{- Remove an entry from a context -}
public export
drop : (ctxt : Context) -> (prf : InState lbl st ctxt) -> 
       Context
drop (MkRes lbl st :: rs) Here = rs
drop (r :: rs) (There p) = r :: drop rs p

{- Proof that a resource state (label/type) is in a context -}
public export
data ElemCtxt : Resource -> Context -> Type where
     HereCtxt : ElemCtxt a (a :: as)
     ThereCtxt : ElemCtxt a as -> ElemCtxt a (b :: as)

{- Proof that a context is a subset of another context -}
public export
data SubCtxt : Context -> Context -> Type where
  SubNil : SubCtxt [] xs
  InCtxt : ElemCtxt x ys -> SubCtxt xs ys -> SubCtxt (x :: xs) ys

public export
Uninhabited (ElemCtxt x []) where
  uninhabited HereCtxt impossible
  uninhabited (ThereCtxt _) impossible

public export
updateAt : -- {xs : Context} ->
           -- {val : ty} ->
           (idx : ElemCtxt (MkRes lbl val) xs) -> 
           (a : ty) -> Context -> Context
updateAt HereCtxt a ((MkRes lbl val) :: xs) = (MkRes lbl a) :: xs
updateAt (ThereCtxt p) a (x :: xs) = x :: updateAt p a xs
updateAt HereCtxt _ [] = []
updateAt (ThereCtxt x) _ [] = []

public export 
updateWith : {ys : Context} ->
             (ys' : Context) -> (xs : Context) ->
             SubCtxt ys xs -> Context
updateWith [] xs prf = xs
updateWith (y :: ys) xs SubNil = xs
updateWith ((MkRes lbl a) :: ys) xs (InCtxt {x = MkRes _ _} idx rest) 
     = updateAt idx a (updateWith ys xs rest)

export
data STrans : (m : Type -> Type) ->
            (ty : Type) ->
            Context -> (ty -> Context) ->
            Type where
     Pure : (result : val) -> STrans m val (out_fn result) out_fn
     Bind : STrans m a st1 st2_fn ->
            ((result : a) -> STrans m b (st2_fn result) st3_fn) ->
            STrans m b st1 st3_fn
     Lift : Monad m => m t -> STrans m t ctxt (const ctxt)

     New : (val : state) -> 
           STrans m Var ctxt (\lbl => (MkRes lbl state) :: ctxt)
     Delete : (lbl : Var) ->
              {auto prf : InState lbl st ctxt} ->
              STrans m () ctxt (const (drop ctxt prf))
     Call : STrans m t ys ys' ->
            {auto ctxt_prf : SubCtxt ys xs} ->
            STrans m t xs (\res => updateWith (ys' res) xs ctxt_prf)

     Get : (lbl : Var) ->
           {auto prf : InState lbl ty ctxt} ->
           STrans m ty ctxt (const ctxt)
     Put : (lbl : Var) ->
           {auto prf : InState lbl ty ctxt} ->
           (val : ty') ->
           STrans m () ctxt (const (updateCtxt ctxt prf ty'))

namespace Env
  public export
  data Env : Context -> Type where
       Nil : Env []
       (::) : ty -> Env xs -> Env ((MkRes lbl ty) :: xs)

lookupEnv : InState lbl ty ctxt -> Env ctxt -> ty
lookupEnv Here (x :: xs) = x
lookupEnv (There p) (x :: xs) = lookupEnv p xs

updateEnv : (prf : InState lbl ty ctxt) -> Env ctxt -> ty' -> 
            Env (updateCtxt ctxt prf ty')
updateEnv Here (x :: xs) val = val :: xs
updateEnv (There p) (x :: xs) val = x :: updateEnv p xs val

dropVal : (prf : InState lbl st ctxt) -> Env ctxt -> Env (drop ctxt prf)
dropVal Here (x :: xs) = xs
dropVal (There p) (x :: xs) = x :: dropVal p xs

envElem : ElemCtxt x xs -> Env xs -> Env [x]
envElem HereCtxt (x :: xs) = [x]
envElem (ThereCtxt p) (x :: xs) = envElem p xs

dropEnv : Env ys -> SubCtxt xs ys -> Env xs
dropEnv [] SubNil = []
dropEnv [] (InCtxt idx rest) = absurd idx
dropEnv (x :: xs) SubNil = []
dropEnv (x :: xs) (InCtxt idx rest) 
    = let [e] = envElem idx (x :: xs) in
          e :: dropEnv (x :: xs) rest

replaceEnvAt : (idx : ElemCtxt (MkRes lbl val) xs) ->
               (env : Env ys) -> res -> Env (updateAt idx res ys)
replaceEnvAt HereCtxt [] x = []
replaceEnvAt HereCtxt (x :: xs) val = val :: xs
replaceEnvAt (ThereCtxt p) [] x = []
replaceEnvAt (ThereCtxt p) (x :: xs) val = x :: replaceEnvAt p xs val

rebuildEnv : Env ys' -> (prf : SubCtxt ys invars) -> Env invars ->
             Env (updateWith ys' invars prf)
rebuildEnv [] SubNil env = env
rebuildEnv [] (InCtxt {x = MkRes lbl val} idx rest) env = env
rebuildEnv (x :: xs) SubNil env = env
rebuildEnv (x :: xs) (InCtxt {x = MkRes lbl val} idx rest) env 
    = replaceEnvAt idx (rebuildEnv xs rest env) x

runST : Env invars -> STrans m a invars outfn ->
          ((x : a) -> Env (outfn x) -> m b) -> m b
runST env (Pure result) k = k result env
runST env (Bind prog next) k 
   = runST env prog (\prog', env' => runST env' (next prog') k)
runST env (Lift action) k 
   = do res <- action
        k res env
runST env (New val) k = k MkVar (val :: env)
runST env (Delete {prf} lbl) k = k () (dropVal prf env)
runST env (Call {ctxt_prf} prog) k 
   = let env' = dropEnv env ctxt_prf in
         runST env' prog
                 (\prog', envk => k prog' (rebuildEnv envk ctxt_prf env))
runST env (Get {prf} lbl) k = k (lookupEnv prf env) env
runST env (Put {prf} lbl val) k = k () (updateEnv prf env val)

export
run : Applicative m => STrans m a [] (const []) -> m a
run prog = runST [] prog (\res, env' => pure res)

export
runPure : STrans Basics.id a [] (const []) -> a
runPure prog = runST [] prog (\res, env' => res)

     
export 
pure : (result : val) -> STrans m val (out_fn result) out_fn
pure = Pure

export 
(>>=) : STrans m a st1 st2_fn ->
        ((result : a) -> STrans m b (st2_fn result) st3_fn) ->
        STrans m b st1 st3_fn
(>>=) = Bind

export
lift : Monad m => m t -> STrans m t ctxt (const ctxt)
lift = Lift

export
new : (val : state) -> 
      STrans m Var ctxt (\lbl => (MkRes lbl state) :: ctxt)
new = New

export
delete : (lbl : Var) ->
         {auto prf : InState lbl st ctxt} ->
         STrans m () ctxt (const (drop ctxt prf))
delete = Delete

export
call : STrans m t ys ys' ->
       {auto ctxt_prf : SubCtxt ys xs} ->
       STrans m t xs (\res => updateWith (ys' res) xs ctxt_prf)
call = Call
     
export
get : (lbl : Var) ->
      {auto prf : InState lbl ty ctxt} ->
      STrans m ty ctxt (const ctxt)
get = Get

export
put : (lbl : Var) ->
      {auto prf : InState lbl ty ctxt} ->
      (val : ty') ->
      STrans m () ctxt (const (updateCtxt ctxt prf ty'))
put = Put

infix 6 :->
          
public export
data Action : Type -> Type where
     Stable : lbl -> Type -> Action ty
     Trans : lbl -> Type -> (ty -> Type) -> Action ty
     Remove : lbl -> Type -> Action ty
     Add : (ty -> Context) -> Action ty

namespace Stable
  public export
  (:::) : lbl -> Type -> Action ty
  (:::) = Stable

namespace Trans
  public export
  data Trans ty = (:->) Type Type

  public export
  (:::) : lbl -> Trans ty -> Action ty
  (:::) lbl (st :-> st') = Trans lbl st (const st')

namespace DepTrans
  public export
  data DepTrans ty = (:->) Type (ty -> Type)

  public export
  (:::) : lbl -> DepTrans ty -> Action ty
  (:::) lbl (st :-> st') = Trans lbl st st'

public export
ST : (m : Type -> Type) ->
     (ty : Type) -> 
     List (Action ty) -> Type
ST m ty xs = STrans m ty (in_res xs) (\result : ty => out_res result xs)
  where
    out_res : ty -> (as : List (Action ty)) -> Context
    out_res x [] = []
    out_res x ((Stable lbl inr) :: xs) = (lbl ::: inr) :: out_res x xs
    out_res x ((Trans lbl inr outr) :: xs) 
        = (lbl ::: outr x) :: out_res x xs
    out_res x ((Remove lbl inr) :: xs) = out_res x xs
    out_res x (Add outf :: xs) = outf x ++ out_res x xs

    in_res : (as : List (Action ty)) -> Context
    in_res [] = []
    in_res ((Stable lbl inr) :: xs) = (lbl ::: inr) :: in_res xs
    in_res ((Trans lbl inr outr) :: xs) = (lbl ::: inr) :: in_res xs
    in_res ((Remove lbl inr) :: xs) = (lbl ::: inr) :: in_res xs
    in_res (Add outf :: xs) = in_res xs

