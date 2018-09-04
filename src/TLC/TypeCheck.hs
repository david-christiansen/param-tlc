-- {hide}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Werror #-}
{-# OPTIONS -Wincomplete-patterns #-}
{-# OPTIONS -Wno-unused-imports #-}

----------------------------------------------------------------
-- |
-- Module               : TLC.TypeCheck
-- Description          : Typechecking to produce strongly-typed STLC
-- Copyright            : (c) Galois, Inc.  2017
-- Maintainer           : Robert Dockins <rdockins@galois.com>
--
-- This module defines an untyped AST for the STLC and demonstrates
-- how to use runtime type representations to do computations on
-- types sufficent to convince GHC that we can produce a strongly-typed
-- term from untyped input data.
-------------------------------------------------------------------
-- {show}

-- # The Type Checker


-- This module implements a type checker. It must prove to the
-- compiler that it produces only well-typed expressions.


module TLC.TypeCheck where


-- # Imports

import Prelude
import Control.Monad.Except

import Data.List
import Data.Type.Equality

import Data.Parameterized.Classes
import Data.Parameterized.Context
import Data.Parameterized.Some


import qualified TLC.AST as AST


-- # Input to the Type Checker

data Term where
  TmVar  :: String -> Term
  TmInt  :: Int -> Term
  TmBool :: Bool -> Term
  TmLe   :: Term -> Term -> Term
  TmAdd  :: Term -> Term -> Term
  TmNeg  :: Term -> Term
  TmIte  :: Term -> Term -> Term -> Term
  TmApp  :: Term -> Term -> Term
  TmAbs  :: String -> Type -> Term -> Term
  TmFix  :: String -> Type -> Term -> Term
 deriving (Show, Read, Eq, Ord)

data Type where
  IntT :: Type
  BoolT :: Type
  ArrowT :: Type -> Type -> Type
 deriving (Show, Read, Eq, Ord)


-- # Existential Types

data Inty (a :: *) :: * where
  Int :: Int -> Inty Int
  Integer :: Integer -> Inty Integer

intFun :: Int -> String
intFun = show

deriving instance Show (Inty a)
instance ShowF Inty

someDemo :: Some Inty
someDemo = Some (Int 5)

-- >>> :module +Data.Parameterized.Some
-- >>> :set -XGADTs
-- >>> someDemo
-- Int 5
-- >>> (case someDemo of { Some (Int x) -> intFun x }) :: String
-- "5"



-- # From Types to TypeReprs

typeToRepr :: Type -> Some AST.TypeRepr
typeToRepr IntT = Some AST.IntRepr
typeToRepr BoolT = Some AST.BoolRepr
typeToRepr (ArrowT x y) =
  case (typeToRepr x, typeToRepr y) of
    (Some x', Some y') -> Some (AST.ArrowRepr x' y')


-- # The Result of Type Checking

-- The result of type checking in some context is a type
-- and a term with that type.

data TCResult (ctx :: Ctx AST.Type) where
  TCResult :: AST.TypeRepr t -> AST.Term ctx t -> TCResult ctx

deriving instance KnownContext ctx => Show (TCResult ctx)


-- # An Aside: Rebindable Syntax

-- Rebindable syntax allows local bindings to be used for
-- desugaring. The type checker rebinds "fail" to capture
-- GHC pattern match failure errors.

attempt :: Either String ()
attempt =
  do Nothing <- return $ Just 3
     return ()
  where fail msg = Left msg

-- >>> attempt
-- Left "Pattern match failure in do expression at /tmp/dantedaw47o.hs:130:6-12"


-- # The Type Checker

verifyTyping ::
  -- Given a stack of free variable names,
  [String] ->
  -- the type of each name,
  Assignment AST.TypeRepr ctx ->
  -- and a term to check,
  Term ->
  -- either return an error or a type checking result.
  Except String (TCResult ctx)

verifyTyping scope env tm =
  case tm of


-- # The Type Checker: Variables

    TmVar nm ->
      case elemIndex nm scope of
        Just i ->
          case intIndex (length scope - 1 - i) (size env) of
            Just (Some idx) ->
              return $ TCResult (env!idx) (AST.TmVar idx)
            Nothing ->
              throwError $
              unwords ["Unable to resolve variable:", nm]
        Nothing ->
          throwError $
          unwords ["Variable not in scope:", nm]


-- # The Type Checker: Literals

    TmInt n ->
      return $ TCResult AST.IntRepr (AST.TmInt n)

-- >>> verifyTyping [] empty $ TmInt 8

    TmBool b ->
      return $ TCResult AST.BoolRepr (AST.TmBool b)

-- >>> verifyTyping [] empty $ TmBool False


-- # The Type Checker: Comparisons and Arithmetic

    TmLe x y ->
      do TCResult AST.IntRepr x' <- verifyTyping scope env x
         TCResult AST.IntRepr y' <- verifyTyping scope env y
         return $ TCResult AST.BoolRepr (AST.TmLe x' y')

-- >>> verifyTyping [] empty $ TmLe (TmInt 3) (TmInt 2)
-- >>> verifyTyping [] empty $ TmLe (TmInt 3) (TmBool False)

    TmAdd x y ->
      do TCResult AST.IntRepr x' <- verifyTyping scope env x
         TCResult AST.IntRepr y' <- verifyTyping scope env y
         return $ TCResult AST.IntRepr (AST.TmAdd x' y')

    TmNeg x ->
      do TCResult AST.IntRepr x' <- verifyTyping scope env x
         return $ TCResult AST.IntRepr (AST.TmNeg x')


-- # The Type Checker: Conditionals

-- testEquality is used to convince the type checker that
-- both xtp and ytp are in fact the same type.

    TmIte c x y ->
      do TCResult AST.BoolRepr c' <- verifyTyping scope env c
         TCResult xtp x' <- verifyTyping scope env x
         TCResult ytp y' <- verifyTyping scope env y
         Just Refl <- return $ testEquality xtp ytp
         return $ TCResult xtp (AST.TmIte c' x' y')

-- >>> verifyTyping [] empty $ TmIte (TmBool False) (TmInt 2) (TmInt 3)
-- >>> verifyTyping [] empty $ TmIte (TmBool False) (TmInt 2) (TmBool True)



-- # The Type Checker: Functions

    TmAbs nm tp x ->
      do Some argTy
           <- return $ typeToRepr tp
         TCResult xtp x'
           <- verifyTyping (nm:scope) (env :> argTy) x
         return $
           TCResult (AST.ArrowRepr argTy xtp)
                    (AST.TmAbs nm argTy x')


    TmApp rator rand ->
      do TCResult (AST.ArrowRepr argTy outTy) rator'
           <- verifyTyping scope env rator
         TCResult rtp rand'
           <- verifyTyping scope env rand
         Just Refl <- return $ testEquality rtp argTy
         return $ TCResult outTy (AST.TmApp rator' rand')



-- # The Type Checker: Recursion

    TmFix nm tp x ->
      do Some argTy <- return $ typeToRepr tp
         TCResult xtp x' <- verifyTyping (nm:scope) (env :> argTy) x
         Just Refl <- return $ testEquality argTy xtp
         return $ TCResult xtp (AST.TmFix nm argTy x')

 where
   fail msg = throwError $ unlines
               [ "Error during typechecking"
               , show tm
               , msg
               ]

-- # Running the Type Checker

-- Check a type in the empty context
checkTerm :: Term -> Except String (TCResult EmptyCtx)
checkTerm = verifyTyping [] Empty


factBody = TmIte (TmLe (TmVar "x") (TmInt 1))
                 (TmInt 1)
                 (TmApp (TmVar "fact")
                        (TmAdd (TmVar "x") (TmInt (-1))))

fact = TmFix "fact" (ArrowT IntT IntT) (TmAbs "x" IntT factBody)

-- >>> checkTerm fact


-- {{{Next: Evaluator|||(lambda (_) (find-file "TypeCheck.hs"))}}}




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
