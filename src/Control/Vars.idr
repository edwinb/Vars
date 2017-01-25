module Control.Vars

%default total

infix 5 :::

{- A resource is a pair of a label and the current type stored there -}
public export
data Resource : Type where
     (:::) : label -> state -> Resource

public export
data Label = MkLabel -- Phantom, just for labelling purposes

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
     Here : InState lbl st ((lbl ::: st) :: rs)
     There : InState lbl st rs -> InState lbl st (r :: rs)

{- Update an entry in a context with a new state -}
public export
updateCtxt : (ctxt : Context) -> 
             InState lbl st ctxt -> state -> Context
updateCtxt ((lbl ::: _) :: rs) Here val = ((lbl ::: val) :: rs)
updateCtxt (r :: rs) (There x) ty = r :: updateCtxt rs x ty

{- Remove an entry from a context -}
public export
drop : (ctxt : Context) -> (prf : InState lbl st ctxt) -> 
       Context
drop ((lbl ::: st) :: rs) Here = rs
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
           (idx : ElemCtxt (lbl ::: val) xs) -> 
           (a : ty) -> Context -> Context
updateAt HereCtxt a ((lbl ::: val) :: xs) = (lbl ::: a) :: xs
updateAt (ThereCtxt p) a (x :: xs) = x :: updateAt p a xs
updateAt HereCtxt _ [] = []
updateAt (ThereCtxt x) _ [] = []

public export 
updateWith : {ys : Context} ->
             (ys' : Context) -> (xs : Context) ->
             SubCtxt ys xs -> Context
updateWith [] xs prf = xs
updateWith (y :: ys) xs SubNil = xs
updateWith ((lbl ::: a) :: ys) xs (InCtxt {x = _ ::: _} idx rest) 
     = updateAt idx a (updateWith ys xs rest)

public export
data Vars : (m : Type -> Type) ->
            (ty : Type) ->
            Context -> (ty -> Context) ->
            Type where
     Pure : (result : val) -> Vars m val (out_fn result) out_fn
     (>>=) : Vars m a st1 st2_fn ->
            ((result : a) -> Vars m b (st2_fn result) st3_fn) ->
            Vars m b st1 st3_fn
     Lift : Monad m => m t -> Vars m t ctxt (const ctxt)

     New : (val : state) -> 
           Vars m Label ctxt (\lbl => (lbl ::: state) :: ctxt)
     Delete : (lbl : Label) ->
              {auto prf : InState lbl st ctxt} ->
              Vars m () ctxt (const (drop ctxt prf))
     Call : Vars m t ys ys' ->
            {auto ctxt_prf : SubCtxt ys xs} ->
            Vars m t xs (\res => updateWith (ys' res) xs ctxt_prf)

     Get : (lbl : Label) ->
           {auto prf : InState lbl ty ctxt} ->
           Vars m ty ctxt (const ctxt)
     Put : (lbl : Label) ->
           {auto prf : InState lbl ty ctxt} ->
           (val : ty') ->
           Vars m () ctxt (const (updateCtxt ctxt prf ty'))

namespace Env
  public export
  data Env : Context -> Type where
       Nil : Env []
       (::) : ty -> Env xs -> Env ((lbl ::: ty) :: xs)

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

replaceEnvAt : (idx : ElemCtxt (lbl ::: val) xs) ->
               (env : Env ys) -> res -> Env (updateAt idx res ys)
replaceEnvAt HereCtxt [] x = []
replaceEnvAt HereCtxt (x :: xs) val = val :: xs
replaceEnvAt (ThereCtxt p) [] x = []
replaceEnvAt (ThereCtxt p) (x :: xs) val = x :: replaceEnvAt p xs val

rebuildEnv : Env ys' -> (prf : SubCtxt ys invars) -> Env invars ->
             Env (updateWith ys' invars prf)
rebuildEnv [] SubNil env = env
rebuildEnv [] (InCtxt {x = lbl ::: val} idx rest) env = env
rebuildEnv (x :: xs) SubNil env = env
rebuildEnv (x :: xs) (InCtxt {x = lbl ::: val} idx rest) env 
    = replaceEnvAt idx (rebuildEnv xs rest env) x

runVars : Env invars -> Vars m a invars outfn ->
          ((x : a) -> Env (outfn x) -> m b) -> m b
runVars env (Pure result) k = k result env
runVars env (prog >>= next) k 
   = runVars env prog (\prog', env' => runVars env' (next prog') k)
runVars env (Lift action) k 
   = do res <- action
        k res env
runVars env (New val) k = k MkLabel (val :: env)
runVars env (Delete {prf} lbl) k = k () (dropVal prf env)
runVars env (Call {ctxt_prf} prog) k 
   = let env' = dropEnv env ctxt_prf in
         runVars env' prog
                 (\prog', envk => k prog' (rebuildEnv envk ctxt_prf env))
runVars env (Get {prf} lbl) k = k (lookupEnv prf env) env
runVars env (Put {prf} lbl val) k = k () (updateEnv prf env val)

export
run : Applicative m => Vars m a [] (const []) -> m a
run prog = runVars [] prog (\res, env' => pure res)

export
runPure : Vars Basics.id a [] (const []) -> a
runPure prog = runVars [] prog (\res, env' => res)

