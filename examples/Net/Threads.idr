module Threads

import Control.ST
import System.Concurrency.Channels
import System

public export
interface Conc (m : Type -> Type) where
  -- 'Fork' divides the resources between the spawned thread and the
  -- parent, and the proofs show that they are distinct
  -- TODO: Note that there is nothing here yet about how the threads
  -- communicate with each other...
  fork : (thread : STrans m () thread_res (const [])) ->
         {auto aprf : SubCtxt (main_res ++ thread_res) all} ->
         {auto mprf : SubCtxt main_res all} ->
         {auto tprf : SubCtxt thread_res all} ->
         STrans m () all (const main_res) 

export
implementation Conc IO where
  fork thread {tprf} 
      = do threadEnv <- getAll
           lift $ spawn (runWith (dropEnv threadEnv tprf) thread) 
           keepSubCtxt
