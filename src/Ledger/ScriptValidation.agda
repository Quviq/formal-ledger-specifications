{-# OPTIONS --safe #-}
{-# OPTIONS --overlapping-instances #-}

open import Ledger.Transaction

module Ledger.ScriptValidation (txs : TransactionStructure) where

open import Ledger.Prelude hiding (Dec₁)

open import Algebra using (CommutativeMonoid)
open import Algebra.Structures
open import Data.Integer using (ℤ; _⊖_)
open import Data.Integer.Ext
open import Data.List as List
open import Data.Nat using (_≤?_; _≤_)
open import Data.Nat.Properties using (+-0-monoid ; +-0-commutativeMonoid)
open import Data.Sign using (Sign)
open import Interface.Decidable.Instance

open TransactionStructure txs
open TxBody
open TxWitnesses
open Tx

open import Ledger.Crypto
open import Ledger.PParams crypto epochStructure ss
open import Ledger.TokenAlgebra using (TokenAlgebra)

open import MyDebugOptions
--open import Tactic.Defaults
open import Tactic.DeriveComp
open import Tactic.Derive.DecEq

open import Ledger.Script
open import Relation.Nullary.Decidable using (⌊_⌋; isNo)
open import Data.Bool using (_∧_)

-- Global Constants

-- Abstract Types

-- Derived Types

data ScriptPurpose : Set where
  Cert  : DCert → ScriptPurpose
  Rewrd : RwdAddr → ScriptPurpose
  Mint  : PolicyId → ScriptPurpose
  Spend : TxIn → ScriptPurpose

-- Abstract Functions

record indexOf : Set where
  field
    indexOfDCert    : DCert → List DCert → Maybe Ix
    indexOfRwdAddr  : RwdAddr → Wdrl → Maybe Ix
    indexOfTxIn     : TxIn → ℙ TxIn → Maybe Ix
    indexOfPolicyId : PolicyId → ℙ PolicyId → Maybe Ix


indexOfImplementation : indexOf
indexOfImplementation = {!!}

open indexOf indexOfImplementation

ixToPtr : Maybe Ix → Maybe RdmrPtr
ixToPtr ix = {!!}

rdptr : TxBody → ScriptPurpose → Maybe RdmrPtr
rdptr txb (Cert h) = ixToPtr (indexOfDCert {!!} {!!})
rdptr txb (Rewrd h) = ixToPtr (indexOfRwdAddr {!!} {!!})
rdptr txb (Mint h) = ixToPtr (indexOfTxIn {!!} {!!})
rdptr txb (Spend h) = ixToPtr (indexOfPolicyId {!!} {!!})

indexedRdmrs : Tx → ScriptPurpose → Maybe (Redeemer × ExUnits)
indexedRdmrs tx sp = {!!}


-- Abstract Script Validation Functions

-- Notation
