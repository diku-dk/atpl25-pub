{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Renamed as requested.
module HQP.QOp.Semantics
  ( Outcomes, RNG
  , SemanticsBackend(..)
  ) where

import HQP.QOp.Syntax
import HQP.QOp.HelperFunctions
import HQP.PrettyPrint.PrettyOp
import Data.Bits(shiftL,xor)
import Data.Array(accumArray,elems)
import Data.Complex (Complex, realPart)
  
--------------------------------------------------------------------------------
-- Shared types
--------------------------------------------------------------------------------
type Outcomes = [Bool]     -- head = most recent
{-| Measurements require random numbers, which are non-deterministic by nature. Everything here is kept purely functional except, with side effects restricted to program mains, so random numbers are simply given as a list of Doubles between 0 and 1. -}
type RNG      = [Double]   -- infinite steam in [0,1)
--------------------------------------------------------------------------------

-- | Semantics backend API. Tensor product, direct sum, adjoint are inherited from Hasxxx classes.
class ( HilbertSpace (StateT b)
      , Operator (OpT b)
      ) => SemanticsBackend b where
  type StateT b
  type OpT    b

  stateQubits :: StateT b -> Int
  opQubits    :: OpT    b -> Int  

  apply :: OpT b -> StateT b -> StateT b

  -- | Computational basis ket for bits, e.g. ket [0,1,1] = |011⟩.

  -- Convention: list head is qubit 0 (MSB / “front” qubit).
  ket :: [Int] -> StateT b

  evalOp :: QOp -> OpT b

  opTensor    :: OpT b -> OpT b -> OpT b
  opDirectSum :: OpT b -> OpT b -> OpT b
  opAdj       :: OpT b -> OpT b

  measure1 :: (StateT b, Outcomes, RNG) -> Int -> (StateT b, Outcomes, RNG)
  
  -- | evalStep and evalProg can be defined independently of the backend,
  --   given measure1, stateQubits, and evalOp.
  evalStep :: (StateT b, Outcomes, RNG) -> Step -> (StateT b, Outcomes, RNG)
  evalStep (st, outs, rng) step = let n = stateQubits @b st in case step of
    Unitary op | (op_qubits op == n) -> (apply (evalOp @b op) st, outs, rng)
               | otherwise -> error $ "Dim-mismatch between " ++ showOp op ++ " and n="++show n

    -- outcomes are latest-first, so ks is reversed on input
    Measure ks -> foldl (measure1 @b) (st, outs, rng) (reverse ks)

    Initialize ks vs ->
      let
        (st', os, rng') = (evalStep @b) (st, [], rng) (Measure ks)
        -- List of outcomes xor values for each initialized qubit
        corrections     = zipWith xor os vs
        -- Now we build the full list, including unaffected qubits        
        corrFull        = accumArray xor False (0,n-1) (zip ks corrections)
        corrOp          = foldl (⊗) One [ if c then X else I | c <- elems corrFull ]
      in (evalStep @b) (st', outs, rng') (Unitary corrOp)

  -- | evalProg simply executes a program step by step
  evalProg :: Program -> StateT b -> RNG -> (StateT b, Outcomes, RNG)
  evalProg steps psi0 rng0 = foldl (evalStep @b) (psi0, [], rng0) steps
