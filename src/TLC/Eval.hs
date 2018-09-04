-- {hide}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Werror #-}
{-# OPTIONS -Wincomplete-patterns #-}
{-# OPTIONS -Wunused-imports #-}


----------------------------------------------------------------
-- |
-- Module               : TLC.Eval
-- Description          : Evaluation strategies for STLC
-- Copyright            : (c) Galois, Inc. 2017
-- Maintainer           : Robert Dockins <rdockins@galois.com>
--
-- This module defines several different evaluation strategies
-- for the STLC.  Each takes advantage of the GADT indices
-- on the term language to ensure that evaluation is well typed.
--
-- Sometimes this requires a very particular way to set up the
-- evaluation definitions.  In particular, the substituion algorithm
-- is most easily expressed using "multi-substitution", which may
-- be less famlilar than single variable substituion.
-------------------------------------------------------------------
-- {show}

-- # Evaluation

module TLC.Eval where


-- # Imports

-- ## Fixed points
import Control.Monad.Fix

-- ## Updatable References
import Control.Monad.ST
import Data.STRef

-- ## Parameterized-utils
import Data.Parameterized.Classes
import Data.Parameterized.Context as Ctx hiding ((++))
import Data.Parameterized.TraversableFC

-- ## The AST
import TLC.AST


-- # Call-by-Value Evaluation

-- Closures in CBV contain values directly

newtype CBV t = CBV { unCBV :: Value CBV t }

instance ShowF CBV
instance Show (CBV t) where
  show (CBV x) = show x


-- # CBV

cbvEval ::
   -- Given an assignment of values to free variables
   Assignment CBV ctx ->
   -- And a term with those variables
   Term ctx t ->
   -- Find a value of the right type
   Value CBV t


-- # CBV: Variables and Literals

cbvEval env (TmVar i) = unCBV (env!i)
cbvEval env (TmWeak x) = cbvEval (Ctx.init env) x
cbvEval env (TmBool b) = VBool b
cbvEval env (TmInt n) = VInt n


-- # CBV: Comparisons and Arithmetic

-- GHC knows that there are no other value possibilities.
cbvEval env (TmLe x y) =
  case (cbvEval env x, cbvEval env y) of
    (VInt a, VInt b) -> VBool $! a <= b
cbvEval env (TmAdd x y) =
  case (cbvEval env x, cbvEval env y) of
    (VInt a, VInt b) -> VInt $! a + b
cbvEval env (TmNeg x) =
  case cbvEval env x of
    VInt a -> VInt $! negate a


-- # CBV: Conditionals

cbvEval env (TmIte c x y) =
  case cbvEval env c of
    VBool True  -> cbvEval env x
    VBool False -> cbvEval env y

-- # CBV: Functions

-- Lexical scope demands the construction of a closure
cbvEval env (TmAbs _ t x) =
  VAbs env t x

-- A seq is needed to force GHC to evaluate in CBV order
cbvEval env (TmApp x y) =
  case cbvEval env x of
    VAbs env' _ body ->
      let y' = CBV (cbvEval env y)
      in seq y' (cbvEval (env' :> y') body)


-- # CBV: Recursion

cbvEval env (TmFix _ _ x) =
      fix $ \x' -> cbvEval (env :> CBV x') x


-- # Call-by-Need Evaluation

-- Variables in CBN range over shared thunks.

-- Thunks contain monadic actions in ST that compute their values, so
-- that they can update other memoized results and be memoized
-- themselves.

-- If there were side effects, IO or StateT x (ST s) might be more
-- appropriate.

newtype Thunk s t = Thunk (STRef s (ST s (CBN s t)))

type CBN s t = Value (Thunk s) t


-- # Operations on CBN Values

instance Show (Thunk s t) where
  show _ = "<thunk>"
instance ShowF (Thunk s)

-- Given a computation that computes a value,
-- produce a thunk that delays the relevant computation.
delay :: ST s (CBN s t) -> ST s (Thunk s t)
delay x = Thunk <$> newSTRef x

-- Given a delayed evaluation thunk, force and
-- memoize its value.
force :: Thunk s t -> ST s (CBN s t)
force (Thunk ref) =
   do x <- readSTRef ref
      val <- x
      writeSTRef ref (return val)
      return val


-- # CBN Evaluation

cbnEval ::
  -- Given an assigment of evaluation thunks to the free variables
  Assignment (Thunk s) ctx ->
  -- And a term with those free variables
  Term ctx t ->
  -- Produce an action that will find the final value
  ST s (CBN s t)


-- # CBN: Variables and Literals
cbnEval env (TmVar i) = force (env ! i)
cbnEval env (TmWeak x) = cbnEval (Ctx.init env) x
cbnEval env (TmBool b) = return $ VBool b
cbnEval env (TmInt n) = return $ VInt n


-- # CBN: Comparisons and Arithmetic
cbnEval env (TmLe x y) =
  do VInt a <- cbnEval env x
     VInt b <- cbnEval env y
     return . VBool $! a <= b
cbnEval env (TmAdd x y) =
  do VInt a <- cbnEval env x
     VInt b <- cbnEval env y
     return . VInt $! a + b
cbnEval env (TmNeg x) =
  do VInt a <- cbnEval env x
     return . VInt $! negate a


-- # CBN: Conditionals

cbnEval env (TmIte c x y) =
  do VBool c' <- cbnEval env c
     if c'
       then cbnEval env x
       else cbnEval env y


-- # CBN: Functions

cbnEval env (TmAbs _ t x) =
        return $ VAbs env t x
cbnEval env (TmApp x y) =
     do VAbs env' _ body <- cbnEval env x
        y' <- delay (cbnEval env y)
        cbnEval (env' :> y') body

-- # CBN: Recursion

cbnEval env (TmFix _ _ x) =
  mfix $ \result ->
    do resultThunk <- delay (return result)
       cbnEval (env :> resultThunk) x



-- # Substitution and full-β evaluation

-- | A @Subst@ assigns to each free variable in @ctx2@
--   a term with free variables in @ctx1@.
type Subst ctx1 ctx2  = Assignment (Term ctx1) ctx2

-- | This is a utility operation that extends a
--   substitution with a fresh variable that will
--   be unchanged.
extend_sub ::
  Size ctx1 ->
  Subst ctx1 ctx2 ->
  Subst (ctx1 ::> t) (ctx2 ::> t)
extend_sub sz sub =
  fmapFC TmWeak sub :> TmVar (nextIndex sz)

-- | Given a substition and a term, apply the substituion to
--   all the free variables in the term.
subst ::
  Size ctx1 ->
  Subst ctx1 ctx2 ->
  Term ctx2 t -> Term ctx1 t
subst sz sub tm = case tm of
  TmVar i     -> sub ! i
  TmWeak x    -> subst sz (Ctx.init sub) x
  TmBool b    -> TmBool b
  TmInt n     -> TmInt n
  TmLe x y    -> TmLe (subst sz sub x) (subst sz sub y)
  TmAdd x y   -> TmAdd (subst sz sub x) (subst sz sub y)
  TmNeg x     -> TmNeg (subst sz sub x)
  TmIte c x y -> TmIte (subst sz sub c) (subst sz sub x) (subst sz sub y)
  TmApp x y   -> TmApp (subst sz sub x) (subst sz sub y)
  TmAbs nm t x -> TmAbs nm t (subst (incSize sz) (extend_sub sz sub) x)
  TmFix nm t x -> TmFix nm t (subst (incSize sz) (extend_sub sz sub) x)

-- | Substitute a term for a single open variable, leaving all other
--   variables unchanged.
singleSubst ::
  Size ctx ->
  Term ctx t          {- ^ The term to substitute -} ->
  Term (ctx ::> t) t' {- ^ The term being substituted into -} ->
  Term ctx t'
singleSubst sz tm body = subst sz (generate sz TmVar :> tm) body

-- | Perform full-β normalization on a λ term.
substEval :: Size ctx -> Term ctx t -> Term ctx t
substEval sz tm = case tm of
  TmVar i  -> TmVar i
  TmWeak x -> TmWeak (substEval (decSize sz) x)
  TmBool x -> TmBool x
  TmInt n  -> TmInt n
  TmLe x y ->
     case (substEval sz x, substEval sz y) of
       (TmInt a, TmInt b) -> TmBool $! a <= b
       (x',y') -> TmLe x' y'
  TmNeg x ->
     case substEval sz x of
       TmInt a -> TmInt $! negate a
       x' -> TmNeg x'
  TmAdd x y ->
     case (substEval sz x, substEval sz y) of
       (TmInt a, TmInt b) -> TmInt $! a + b
       (x',y') -> TmAdd x' y'
  TmAbs nm t x  -> TmAbs nm t (substEval (incSize sz) x)
  TmIte c x y ->
     case substEval sz c of
       TmBool True  -> substEval sz x
       TmBool False -> substEval sz y
       c' -> TmIte c' x y
  TmApp x y ->
     case substEval sz x of
       TmAbs _ _ body -> substEval sz (singleSubst sz y body)
       x' -> TmApp x' y
  TmFix _ _ x ->
     substEval sz (singleSubst sz tm x)




-- {hide}
-- Local Variables:
-- eval: (eldoc-mode -1)
-- eval: (display-line-numbers-mode -1)
-- eval: (flycheck-mode 1)
-- eval: (make-variable-buffer-local 'face-remapping-alist)
-- eval: (add-to-list 'face-remapping-alist '(live-code-talks-title-face (:height 2.0
--                                                                        :slant normal
--                                                                        :foreground "black" :family "Overpass Heavy" :weight bold)))
-- eval: (add-to-list 'face-remapping-alist '(live-code-talks-subtitle-face (:height 1.5
--                                                                           :slant normal
--                                                                           :foreground "black" :family "Overpass Heavy" :weight semibold)))
-- eval: (add-to-list 'face-remapping-alist '(live-code-talks-subsubtitle-face (:height 1.3
--                                                                              :slant normal
--                                                                              :foreground "black" :family "Overpass Heavy")))
-- eval: (add-to-list 'face-remapping-alist
--                    '(live-code-talks-comment-face (:slant normal
--                                                    :foreground "black"
--                                                    :family "Overpass")))
-- eval: (add-to-list 'face-remapping-alist
--                    '(idris-loaded-region-face (:background nil)))
-- End:
-- {show}
