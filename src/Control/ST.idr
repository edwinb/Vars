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

public export
dropEl : (ys: _) -> ElemCtxt x ys -> Context
dropEl (x :: as) HereCtxt = as
dropEl (x :: as) (ThereCtxt p) = x :: dropEl as p

{- Proof that a context is a subset of another context -}
public export
data SubCtxt : Context -> Context -> Type where
     SubNil : SubCtxt [] []
     InCtxt : (el : ElemCtxt x ys) -> SubCtxt xs (dropEl ys el) ->
              SubCtxt (x :: xs) ys
     Skip : SubCtxt xs ys -> SubCtxt xs (y :: ys)

%hint
public export
subCtxtId : SubCtxt xs xs
subCtxtId {xs = []} = SubNil
subCtxtId {xs = (x :: xs)} = InCtxt HereCtxt subCtxtId

public export
subCtxtNil : SubCtxt [] xs
subCtxtNil {xs = []} = SubNil
subCtxtNil {xs = (x :: xs)} = Skip subCtxtNil

public export
Uninhabited (ElemCtxt x []) where
  uninhabited HereCtxt impossible
  uninhabited (ThereCtxt _) impossible

public export
updateWith : (new : Context) -> (xs : Context) ->
             SubCtxt ys xs -> Context
-- At the end, add the ones which were updated by the subctxt
updateWith new [] SubNil = new
updateWith new [] (InCtxt el z) = absurd el
-- Don't add the ones which were consumed by the subctxt
updateWith [] (x :: xs) (InCtxt el p) 
    = updateWith [] (dropEl _ el) p
updateWith (n :: ns) (x :: xs) (InCtxt el p) 
    = n :: updateWith ns (dropEl _ el) p
-- Do add the ones we didn't use in the subctxt
updateWith new (x :: xs) (Skip p) = x :: updateWith new xs p

namespace Env
  public export
  data Env : Context -> Type where
       Nil : Env []
       (::) : ty -> Env xs -> Env ((lbl ::: ty) :: xs)

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
kept : SubCtxt xs ys -> Context
kept SubNil = []
kept (InCtxt el p) = kept p
kept (Skip {y} p) = y :: kept p

-- Need an instance to be able to 'put' or create with 'new'.
-- This allows us to restrict 'put' and 'new' to only functions which know
-- the concrete type of what is being created.
-- Even though you can make implementations arbitrarily (because there's no
-- methods) you still need to know the *specific* instance to be able to
-- create it.
public export
interface Creatable a where

export
data STrans : (m : Type -> Type) ->
            (ty : Type) ->
            Context -> (ty -> Context) ->
            Type where
     Pure : (result : ty) -> 
            STrans m ty (out_fn result) out_fn
     Bind : STrans m a st1 st2_fn ->
            ((result : a) -> 
                STrans m b (st2_fn result) st3_fn) ->
            STrans m b st1 st3_fn
     Lift : Monad m => m t -> STrans m t ctxt (const ctxt)

     New : Creatable state =>
           (val : state) -> 
           STrans m Var ctxt (\lbl => (lbl ::: state) :: ctxt)
     Delete : (lbl : Var) ->
              {auto prf : InState lbl st ctxt} ->
              STrans m () ctxt (const (drop ctxt prf))
     DropSubCtxt : {auto prf : SubCtxt ys xs} ->
                   STrans m () xs (const (kept prf))

     Call : STrans m t ys ys' ->
            {auto ctxt_prf : SubCtxt ys xs} ->
            STrans m t xs (\res => updateWith (ys' res) xs ctxt_prf)

     Get : (lbl : Var) ->
           {auto prf : InState lbl ty ctxt} ->
           STrans m ty ctxt (const ctxt)
     GetAll : STrans m (Env ctxt) ctxt (const ctxt)
     Put : Creatable ty' =>
           (lbl : Var) ->
           {auto prf : InState lbl ty ctxt} ->
           (val : ty') ->
           STrans m () ctxt (const (updateCtxt ctxt prf ty'))

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

dropDups : Env xs -> (el : ElemCtxt x xs) -> Env (dropEl xs el)
dropDups (y :: ys) HereCtxt = ys
dropDups (y :: ys) (ThereCtxt p) = y :: dropDups ys p

export
dropEnv : Env ys -> SubCtxt xs ys -> Env xs
dropEnv [] SubNil = []
dropEnv [] (InCtxt idx rest) = absurd idx
dropEnv (z :: zs) (InCtxt idx rest) 
    = let [e] = envElem idx (z :: zs) in
          e :: dropEnv (dropDups (z :: zs) idx) rest
dropEnv (z :: zs) (Skip p) = dropEnv zs p

keepEnv : Env ys -> (prf : SubCtxt xs ys) -> Env (kept prf)
keepEnv env SubNil = env
keepEnv env (InCtxt el prf) = keepEnv (dropDups env el) prf
keepEnv (z :: zs) (Skip prf) = z :: keepEnv zs prf

-- Corresponds pretty much exactly to 'updateWith'
rebuildEnv : Env ys' -> Env invars -> (prf : SubCtxt ys invars) ->
             Env (updateWith ys' invars prf)
rebuildEnv new [] SubNil = new
rebuildEnv new [] (InCtxt el p) = absurd el
rebuildEnv [] (x :: xs) (InCtxt el p) 
    = rebuildEnv [] (dropDups (x :: xs) el) p
rebuildEnv (e :: es) (x :: xs) (InCtxt el p) 
    = e :: rebuildEnv es (dropDups (x :: xs) el) p
rebuildEnv new (x :: xs) (Skip p) = x :: rebuildEnv new xs p

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
runST env (DropSubCtxt {prf}) k = k () (keepEnv env prf)
runST env (Call {ctxt_prf} prog) k 
   = let env' = dropEnv env ctxt_prf in
         runST env' prog
                 (\prog', envk => k prog' (rebuildEnv envk env ctxt_prf))
runST env (Get {prf} lbl) k = k (lookupEnv prf env) env
runST env GetAll k = k env env
runST env (Put {prf} lbl val) k = k () (updateEnv prf env val)


export 
pure : (result : ty) -> STrans m ty (out_fn result) out_fn
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
new : Creatable state =>
      (val : state) -> 
      STrans m Var ctxt (\lbl => (lbl ::: state) :: ctxt)
new = New

export
delete : (lbl : Var) ->
         {auto prf : InState lbl st ctxt} ->
         STrans m () ctxt (const (drop ctxt prf))
delete = Delete

-- Keep only a subset of the current set of resources 
export
dropSubCtxt : {auto prf : SubCtxt ys xs} ->
              STrans m () xs (const (kept prf))
dropSubCtxt = DropSubCtxt

export -- implicit ???
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
getAll : STrans m (Env ctxt) ctxt (const ctxt)
getAll = GetAll

export
put : Creatable ty' =>
      (lbl : Var) ->
      {auto prf : InState lbl ty ctxt} ->
      (val : ty') ->
      STrans m () ctxt (const (updateCtxt ctxt prf ty'))
put = Put

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

export
run : Applicative m => ST m a [] -> m a
run prog = runST [] prog (\res, env' => pure res)

export
runWith : Applicative m => Env ctxt -> STrans m a ctxt (const []) -> m a
runWith env prog = runST env prog (\res, env' => pure res)

export
runPure : ST Basics.id a [] -> a
runPure prog = runST [] prog (\res, env' => res)

