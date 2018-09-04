-- {hide}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Werror #-}
{-# OPTIONS -Wincomplete-patterns #-}
{-# OPTIONS -Wunused-imports #-}
----------------------------------------------------------------
-- |
-- Module               : TLC.SimpleTerm
-- Description          : Strongly-typed abstract syntax
--                         a simple term language
-- Copyright            : (c) Galois, Inc.  2018
-- Maintainter          : Robert Dockins <rdockins@galois.com>
--
-- This module defines a simple first-order term syntax operating
-- on booleans an integers to introduce the main ideas of
-- GADTs, data kinds, type representatives, and typed evaluation.
-------------------------------------------------------------------

-- {show}
-- # Singletons and Typed Expressions

-- • GADTs allow us to represent only well-typed expressions

-- • Singletons allow compile-time types to have unique
--   run-time representatives

module TLC.SimpleTerm where


-- # Singletons and Typed Expressions

import Data.Parameterized.Classes

-- This is intended for use as a data kind.

data Type = BoolT | IntT

-- When a run-time representative is needed,
-- use this data type whose structure precisely
-- mirrors Type.

data TypeRepr :: Type -> * where
  BoolRepr  :: TypeRepr BoolT
  IntRepr   :: TypeRepr IntT

-- >>> :t BoolT
-- >>> :t BoolRepr


-- # Useful Instances

instance Show (TypeRepr t) where
  showsPrec _ IntRepr  = showString "IntT"
  showsPrec _ BoolRepr = showString "BoolT"

instance ShowF TypeRepr

instance KnownRepr TypeRepr IntT where knownRepr = IntRepr
instance KnownRepr TypeRepr BoolT where knownRepr = BoolRepr

instance TestEquality TypeRepr where
  testEquality BoolRepr BoolRepr = return Refl
  testEquality IntRepr  IntRepr  = return Refl
  testEquality _ _ = Nothing


-- # Terms

-- The parameter 't' is the result type of the term.
data Term (t :: Type) :: * where
  TmInt  :: Int -> Term IntT
  TmLe   :: Term IntT -> Term IntT -> Term BoolT
  TmAdd  :: Term IntT -> Term IntT -> Term IntT
  TmNeg  :: Term IntT -> Term IntT
  TmBool :: Bool -> Term BoolT
  TmIte  :: forall a. Term BoolT -> Term a -> Term a -> Term a

deriving instance Show (Term a)

-- >>> TmIte (TmLe (TmInt 2) (TmInt 5)) (TmBool True) (TmBool False)


-- # Printing Terms

printTerm :: Int
          -> Term t
          -> ShowS
printTerm prec tm =
  case tm of
    TmInt n -> shows n
    TmBool b -> shows b
    TmLe x y -> showParen (prec > 6) (printTerm 7 x . showString " <= " . printTerm 7 y)
    TmAdd x y -> showParen (prec > 5) (printTerm 6 x . showString " + " . printTerm 6 y)
    TmNeg x -> showParen (prec > 10) (showString "negate " . printTerm 11 x)
    TmIte c x y -> showParen (prec > 3) $
                   showString "if " . printTerm 0 c .
                   showString " then " . printTerm 4 x .
                   showString " else " . printTerm 4 y

-- >>> let tm = TmIte (TmLe (TmInt 2) (TmInt 5)) (TmBool True) (TmBool False)
-- >>> printTerm 0 tm ""



-- # Finding types

-- A TypeRepr is a run-time representative of a compile-time Type.

computeType :: Term t -> TypeRepr t
computeType tm =
  case tm of
    TmInt _ -> IntRepr
    TmBool _ -> BoolRepr
    TmLe _ _ -> BoolRepr
    TmAdd _ _ -> IntRepr
    TmNeg _ -> IntRepr
    TmIte _ x _ -> computeType x

-- >>> let tm = TmIte (TmLe (TmInt 2) (TmInt 5)) (TmBool True) (TmBool False)
-- >>> computeType tm


-- # Values

data Value (t :: Type) :: * where
  VInt   :: Int -> Value IntT
  VBool  :: Bool -> Value BoolT

instance ShowF Value
instance Show (Value t) where
  show (VInt i) = show i
  show (VBool b) = show b


-- # Evaluation

-- GHC knows that these pattern matches are exhaustive.

eval :: Term t -> Value t
eval tm =
  case tm of
    TmBool b -> VBool b
    TmInt n  -> VInt n
    TmLe x y ->
      case (eval x, eval y) of
        (VInt a, VInt b) -> VBool $! a <= b
    TmAdd x y ->
      case (eval x, eval y) of
        (VInt a, VInt b) -> VInt $! a + b
    TmNeg x ->
       case eval x of
         VInt a -> VInt $! negate a
    TmIte c x y ->
      case eval c of
        VBool True  -> eval x
        VBool False -> eval y

-- >>> let tm1 = TmIte (TmLe (TmInt 2) (TmInt 5)) (TmBool True) (TmBool False)
-- >>> eval tm1
-- >>> let tm2 = TmIte (TmLe (TmInt 2) (TmInt 5)) (TmInt 2) (TmInt 5)
-- >>> eval tm2


-- # Exercises

-- 0. Add multiplication

-- 1. Add strings to the language, with literals,
--    concatenation, and lexicographic ordering.

-- 2. Add integer division, catching division by
--    zero.

-- ## Next Step

-- The Simply Typed λ-Calculus, illustrating
-- variable binding, type checking, and evaluation





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
