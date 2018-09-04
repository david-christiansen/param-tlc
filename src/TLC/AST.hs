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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Werror #-}
{-# OPTIONS -Wincomplete-patterns #-}
{-# OPTIONS -Wunused-imports #-}
----------------------------------------------------------------
-- |
-- Module               : TLC.AST
-- Description          : Strongly-typed abstract syntax for a λ-calculus
-- Copyright            : (c) Galois, Inc.  2017
-- Maintainer           : Robert Dockins <rdockins@galois.com>
--
-- This module defines a strongly-typed abstract syntax for a typed
-- λ-calculus, using a host of fancy GHC extensions (in particular
-- Generalized Algebraic Data Types, GADTs) to directly embed the
-- simple type discipline of λ-terms directly into GHC's type system.
--
-- The major purpose of this module is to demonstrate the techniques
-- required to successfully work in this atmosphere of rich types.
-- Special data structures, generalizations of existing programming
-- patterns and programming techniques are often required; many of
-- these useful patterns and utilities have been captured in the
-- 'parameterized-utils' package.  This module demonstrates the
-- use of quite a few of these.
-------------------------------------------------------------------

-- {show}
-- # Simply-Typed λ-Calculus

-- • Programming with rich types requires new techniques
--   and generalizations of old ones.

-- • Galois developed the parameterized-utils library to
--   collect these useful patterns and utilities.

module TLC.AST where


-- # Useful Imports

-- The constant functor
import Data.Functor.Const

-- Generalizations of common type classes at higher kinds
import Data.Parameterized.Classes

-- Type-level lists and run-time lists indexed by them
import Data.Parameterized.Context as Ctx

-- A version of Traversable generalized to higher kinds
import Data.Parameterized.TraversableFC

-- Quantified constraints in GHC 8.6 will render many of
-- these classes redundant.


-- # STLC types

-- A data kind for λ-calculus types

data Type where
  (:->) :: Type -> Type -> Type
  BoolT :: Type
  IntT  :: Type

infixr 5 :->


-- A singleton for run-time witnesses of STLC types

data TypeRepr :: Type -> * where
  ArrowRepr :: TypeRepr t1 -> TypeRepr t2 -> TypeRepr (t1 :-> t2)
  BoolRepr  :: TypeRepr BoolT
  IntRepr   :: TypeRepr IntT


-- # Showing Types

instance Show (TypeRepr t) where
  showsPrec _ IntRepr  = showString "IntT"
  showsPrec _ BoolRepr = showString "BoolT"
  showsPrec d (ArrowRepr x y) =
     showParen (d > 5) $
       showsPrec 6 x . showString " :-> " . showsPrec 5 y

instance ShowF TypeRepr


-- # Recovering a Witness
-- # for a Statically Known Type

instance KnownRepr TypeRepr IntT where
  knownRepr = IntRepr

instance KnownRepr TypeRepr BoolT where
  knownRepr = BoolRepr

instance (KnownRepr TypeRepr t1, KnownRepr TypeRepr t2) =>
         KnownRepr TypeRepr (t1 :-> t2)
  where
    knownRepr = ArrowRepr knownRepr knownRepr


-- # Equality of STLC Types

instance TestEquality TypeRepr where
  testEquality BoolRepr BoolRepr = return Refl
  testEquality IntRepr  IntRepr  = return Refl
  testEquality (ArrowRepr x1 x2) (ArrowRepr y1 y2) =
    do Refl <- testEquality x1 y1
       Refl <- testEquality x2 y2
       return Refl
  testEquality _ _ = Nothing

-- >>> :t testEquality BoolRepr BoolRepr


-- # STLC Terms

-- Parameters to Term:

-- • ctx gives the types of free variables that may occur

-- • t gives the term's type

data Term (ctx :: Ctx Type) (t :: Type) :: * where
  TmVar  :: Index ctx t -> Term ctx t
  TmWeak :: Term ctx t -> Term (ctx ::> t') t
  TmInt  :: Int -> Term ctx IntT
  TmLe   :: Term ctx IntT -> Term ctx IntT -> Term ctx BoolT
  TmAdd  :: Term ctx IntT -> Term ctx IntT -> Term ctx IntT
  TmNeg  :: Term ctx IntT -> Term ctx IntT
  TmBool :: Bool -> Term ctx BoolT
  TmIte  :: Term ctx BoolT -> Term ctx t -> Term ctx t -> Term ctx t
  TmApp  :: Term ctx (t1 :-> t2) ->
            Term ctx t1 ->
            Term ctx t2
  TmAbs  :: String -> TypeRepr t1 ->
            Term (ctx ::> t1) t2 ->
            Term ctx (t1 :-> t2)
  TmFix  :: String -> TypeRepr t ->
            Term (ctx ::> t) t ->
            Term ctx t

-- >>> :t TmAdd (TmInt 3) (TmInt 2)
-- TmAdd (TmInt 3) (TmInt 2) :: Term ctx 'IntT
-- >>> :t TmAdd (TmInt 2) (TmVar 0)
-- TmAdd (TmInt 2) (TmVar 0)
--   :: Num (Data.Parameterized.Context.Unsafe.Index ctx 'IntT) =>
--      Term ctx 'IntT



-- # Some Syntactic Sugar

infixl 5 :@

instance Num (Term ctx IntT) where
  fromInteger n = TmInt (fromInteger n)
  x + y = TmAdd x y
  negate (TmInt x) = TmInt (negate x)
  negate x = TmNeg x
  x * y = error "multiplication not defined"
  abs = error "Abs not defined"
  signum = error "signum not defined"

pattern (:@) :: Term ctx (t1 :-> t2) -> Term ctx t1 -> Term ctx t2
pattern x :@ y = TmApp x y



-- # Some Syntactic Sugar

λ ::
  KnownRepr TypeRepr t1 =>
  String ->
  Term (ctx ::> t1) t2 ->
  Term ctx (t1 :-> t2)
λ nm x = TmAbs nm knownRepr x

μ ::
  KnownRepr TypeRepr t =>
  String ->
  Term (ctx ::> t) t ->
  Term ctx t
μ nm x = TmFix nm knownRepr x


-- # Syntactic Sugar

--  Variables, intended to be used with explicit
--  type applications, e.g. Var @2.
pattern Var :: forall n ctx t. Idx n ctx t => Term ctx t
pattern Var <- TmVar (testEquality (natIndex @n) -> Just Refl)
 where Var = TmVar (natIndex @n)

pattern (:<=) :: Term ctx IntT -> Term ctx IntT -> Term ctx BoolT
pattern x :<= y = TmLe x y


-- # Printing Expressions

printTerm :: Assignment (Const (Int -> ShowS)) ctx
          -> Int
          -> Term ctx t
          -> ShowS
printTerm pvar prec tm =
  case tm of
    TmVar i -> getConst (pvar!i) prec
    TmWeak x -> printTerm (Ctx.init pvar) prec x
    TmInt n -> shows n
    TmBool b -> shows b
    TmLe x y ->
      showParen (prec > 6) $
      printTerm pvar 7 x . showString " <= " . printTerm pvar 7 y
    TmAdd x y ->
      showParen (prec > 5) $
      printTerm pvar 6 x . showString " + " . printTerm pvar 6 y
    TmNeg x ->
      showParen (prec > 10) $
      showString "negate " . printTerm pvar 11 x
    TmIte c x y ->
      showParen (prec > 3) $
      showString "if " . printTerm pvar 0 c .
      showString " then " . printTerm pvar 4 x .
      showString " else " . printTerm pvar 4 y
    TmApp x y ->
      showParen (prec > 10) $
      printTerm pvar 10 x . showString " " . printTerm pvar 11 y
    TmFix nm tp x ->
      let nm' = if Prelude.null nm then "v" else nm
          vnm _prec = showString nm' . shows (sizeInt (size pvar)) in
      showParen (prec > 0) $
        showString "μ " . vnm 0 .
        showString " : " . showsPrec 0 tp .
        showString ". " . printTerm (pvar :> Const vnm) 0 x
    TmAbs nm tp x ->
      let nm' = if Prelude.null nm then "v" else nm
          vnm _prec = showString nm' . shows (sizeInt (size pvar)) in
      showParen (prec > 0) $
        showString "λ " . vnm 0 .
        showString " : " . showsPrec 0 tp .
        showString ". " . printTerm (pvar :> Const vnm) 0 x

-- >>> :set -XDataKinds -XTypeApplications -XPartialTypeSignatures -Wno-partial-type-signatures
-- >>> :module +Data.Parameterized.Context
-- >>> printTerm empty 0 (λ "x" (Var @ 0 :: Term _ 'BoolT)) ""



-- # Showing Terms

instance KnownContext ctx => Show (Term ctx t) where
  showsPrec =
    printTerm $
    generate knownSize $
    \i ->
      Const (\_ -> shows (indexVal i))


-- # Computing Types

computeType ::
  Assignment TypeRepr ctx ->
  Term ctx t ->
  TypeRepr t
computeType env (TmVar i) = env ! i
computeType env (TmWeak x) = computeType (Ctx.init env) x
computeType env (TmInt _) = IntRepr
computeType env (TmBool _) = BoolRepr
computeType env (TmLe _ _) = BoolRepr
computeType env (TmAdd _ _) = IntRepr
computeType env (TmNeg _) = IntRepr
computeType env (TmIte _ x _) = computeType env x
computeType env (TmApp x y) =
  case computeType env x of
    ArrowRepr _ t -> t
computeType env (TmAbs _ t1 x) =
  let t2 = computeType (env :> t1) x
  in ArrowRepr t1 t2
computeType env (TmFix _ t _) = t


-- # Values

-- The parameter f controls the values pointed to by variables in
-- closures, and will change based on evaluation strategy.

data Value (f :: Type -> *) (t :: Type) :: * where
  VInt   :: Int -> Value f IntT
  VBool  :: Bool -> Value f BoolT
  VAbs   :: Assignment f ctx ->
            TypeRepr t1 ->
            Term (ctx ::> t1) t2 ->
            Value f (t1 :-> t2)


instance ShowFC Value where
  showsPrecFC _sh _prec (VInt n) = shows n
  showsPrecFC _sh _prec (VBool b) = shows b
  showsPrecFC sh prec (VAbs env t tm) =
     printTerm (fmapFC (\x -> Const (\p -> sh p x)) env)
       prec
       (TmAbs [] t tm)
instance ShowF f => ShowF (Value f)
instance ShowF f => Show (Value f t) where
  show = showFC showF

-- {{{Next: Type Checker|||(lambda (_) (find-file "TypeCheck.hs"))}}}



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
