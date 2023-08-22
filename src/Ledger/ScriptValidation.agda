{-# OPTIONS --safe #-}
{-# OPTIONS --overlapping-instances #-}

open import Ledger.Transaction
open import Ledger.Abstract

module Ledger.ScriptValidation (txs : TransactionStructure)(abs : AbstractFunctions txs)where

open import Ledger.Prelude hiding (Dec₁) renaming (map to mapSet)

open import Algebra using (CommutativeMonoid)
open import Algebra.Structures
open import Data.Integer using (ℤ; _⊖_)
open import Data.Integer.Ext
open import Data.List as List hiding (map)
open import Data.Maybe
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

open AbstractFunctions abs
open indexOf indexOfImp

open Properties

open import Tactic.AnyOf
open import Tactic.Assumption
open import Tactic.Defaults
open import Tactic.Helpers

-- Because of missing macro hygiene, we have to copy&paste this. https://github.com/agda/agda/issues/3819
private macro
  ∈⇒P = anyOfⁿᵗ (quote ∈-filter⁻' ∷ quote ∈-∪⁻ ∷ quote ∈-map⁻' ∷ quote ∈-fromList⁻ ∷ [])
  P⇒∈ = anyOfⁿᵗ (quote ∈-filter⁺' ∷ quote ∈-∪⁺ ∷ quote ∈-map⁺' ∷ quote ∈-fromList⁺ ∷ [])
  ∈⇔P = anyOfⁿᵗ (quote ∈-filter⁻' ∷ quote ∈-∪⁻ ∷ quote ∈-map⁻' ∷ quote ∈-fromList⁻ ∷ quote ∈-filter⁺' ∷ quote ∈-∪⁺ ∷ quote ∈-map⁺' ∷ quote ∈-fromList⁺ ∷ [])

data ScriptPurpose : Set where
  Cert  : DCert → ScriptPurpose
  Rwrd : RwdAddr → ScriptPurpose
  Mint  : ScriptHash → ScriptPurpose
  Spend : TxIn → ScriptPurpose

rdptr : TxBody → ScriptPurpose → Maybe RdmrPtr
rdptr txb (Cert h) = map (λ x → Cert , x) (indexOfDCert h (txcerts txb))
rdptr txb (Rwrd h) = map (λ x → Rewrd , x) (indexOfRwdAddr h (txwdrls txb))
rdptr txb (Mint h) = map (λ x → Mint , x) (indexOfPolicyId h (policies (mint txb)))
rdptr txb (Spend h) = map (λ x → Spend , x) (indexOfTxIn h (txins txb))

indexedRdmrs : Tx → ScriptPurpose → Maybe (Redeemer × ExUnits)
indexedRdmrs tx sp = maybe (λ x → lookupᵐ? (txrdmrs (wits tx)) x ⦃ _ ∈? _ ⦄)
                            nothing
                            (rdptr (body tx) sp)

-- Abstract Script Validation Functions

-- epochInfoSlotToUTCTime : EpochInfo → SystemStart → Slot → -- UTCTime? Translate slot number to system time or fail

-- runPLCScript : CostModel → Scriptplc → ExUnits → Data∗ → IsValid
-- Validate a Plutus script, taking resource limits into account

-- Notation

getDatum : Tx → UTxO → ScriptPurpose → List Datum
getDatum tx utxo (Spend txin) = maybe (λ { (_ , _ , just x) → maybe (λ x₁ → [ x₁ ])
                                                              []
                                                              (lookupᵐ? (txdats (wits tx)) x ⦃ _ ∈? _ ⦄)
                                          ; (_ , _ , nothing) → []})
                                          []
                                          ((lookupᵐ? utxo txin ⦃ _ ∈? _ ⦄))
getDatum tx utxo _ = []


record TxInfo : Set where
  field realizedInputs : UTxO
        txouts  : Ix ⇀ TxOut
        fee     : Value
        mint    : Value
        txcerts : List DCert
        txwdrls : Wdrl
        txvldt  : Maybe Slot × Maybe Slot
        vkKey   : ℙ KeyHash
        txdats  : DataHash ⇀ Datum
        txid    : TxId

txInfo : Language → PParams
                  → UTxO
                  → Tx
                  → TxInfo
txInfo l pp utxo tx = record
                        { realizedInputs = utxo ∣ (txins txb)
                        ; txouts = txouts txb
                        ; fee = inject (txfee txb)
                        ; mint = mint txb
                        ; txcerts = txcerts txb
                        ; txwdrls = txwdrls txb
                        ; txvldt = txvldt txb
                        ; vkKey = reqSigHash txb
                        ; txdats = txdats (wits tx)
                        ; txid = txid txb
                        }
  where
    txb = body tx

DelegateOrDeReg : DCert → Set
DelegateOrDeReg (delegate x x₁ x₂ x₃) = ⊤
DelegateOrDeReg (regpool x x₁) = ⊥
DelegateOrDeReg (retirepool x x₁) = ⊥
DelegateOrDeReg (regdrep x x₁ x₂) = ⊥
DelegateOrDeReg (deregdrep x) = ⊤
DelegateOrDeReg (ccreghot x x₁) = ⊥

DelegateOrDeReg? : ∀ x → Dec (DelegateOrDeReg x)
DelegateOrDeReg? (delegate x x₁ x₂ x₃) = yes tt
DelegateOrDeReg? (regpool x x₁) = no (λ { ()})
DelegateOrDeReg? (retirepool x x₁) = no (λ { ()})
DelegateOrDeReg? (regdrep x x₁ x₂) = no (λ { ()})
DelegateOrDeReg? (deregdrep x) = yes tt
DelegateOrDeReg? (ccreghot x x₁) = no (λ { ()})

UTxOSH  = TxIn ⇀ (TxOut × ScriptHash)

scriptOutWithHash : TxIn → TxOut → Maybe (TxOut × ScriptHash)
scriptOutWithHash txin (addr , snd) with isScriptAddr? addr
... | no ¬p = nothing
... | yes p = just ((addr , snd) , (getScriptHash addr p))

scriptOutsWithHash : UTxO → UTxOSH
scriptOutsWithHash utxo = mapMaybeWithKeyᵐ scriptOutWithHash utxo

spendScripts : TxIn → UTxOSH → Maybe (ScriptPurpose × ScriptHash)
spendScripts txin utxo with txin ∈? dom (utxo ˢ)
... | no ¬p = nothing
... | yes p = just ((Spend txin) , (proj₂ (lookupMap utxo p)))

rwdScripts : RwdAddr → Maybe (ScriptPurpose × ScriptHash)
rwdScripts a with isScriptRwdAddr? a
... | no ¬p = nothing
... | yes (SHisScript sh) = just (Rwrd a , sh)

certScripts : DCert → Maybe (ScriptPurpose × ScriptHash)
certScripts d with DelegateOrDeReg? d
... | no ¬p = nothing
certScripts (delegate (inj₁ x) x₁ x₂ x₃) | yes p = nothing
certScripts (delegate (inj₂ y) x₁ x₂ x₃) | yes p = just (Cert (delegate (inj₂ y) x₁ x₂ x₃) , y)
certScripts (deregdrep (inj₁ x)) | yes p = nothing
certScripts (deregdrep (inj₂ y)) | yes p = just (Cert (deregdrep (inj₂ y)) , y)

scriptsNeeded : UTxO → TxBody → ℙ (ScriptPurpose × ScriptHash)
scriptsNeeded utxo txb = mapPartial (λ x → spendScripts x (scriptOutsWithHash utxo)) (txins txb)
                         ∪ mapPartial (λ x → rwdScripts x) (dom $ proj₁ $ (txwdrls txb))
                         ∪ mapPartial (λ x → certScripts x) (setFromList $ txcerts txb)
                         ∪ mapSet (λ x → (Mint x) , x) (policies (mint txb))

toData : ∀{A : Set} → A → Data
toData = {!!}

-- We need to add toData to define this
valContext : TxInfo → ScriptPurpose → Data
valContext txinfo sp = toData (txinfo , sp)

scriptHashInTx : ScriptHash → Tx → Bool
scriptHashInTx sh tx = ⌊ sh ∈? (Ledger.Prelude.map proj₁ $ m ˢ) ⌋
  where
    m = setToHashMap $ TxWitnesses.scripts (Tx.wits tx)

collectPhaseTwoScriptInputs' : PParams → Tx
                                      → UTxO
                                      → (ScriptPurpose × ScriptHash)
                                      → Maybe (Script × List Data × ExUnits × CostModel)
collectPhaseTwoScriptInputs' pp tx utxo (sp , sh) with lookupScriptHash sh tx
... | nothing = nothing
... | just s with isP2Script s
... | false = nothing
... | true = just (s , (((getDatum tx utxo sp) ++ {!!}) , {!!} , {!cm!}))

collectPhaseTwoScriptInputs : PParams → Tx
                                      → UTxO
                                      → List (Script × List Data × ExUnits × CostModel)
collectPhaseTwoScriptInputs pp tx utxo with scriptsNeeded utxo (body tx)
... | ans with mapSet (λ { (sp , sh) → getDatum tx utxo sp}) ans
... | ans2 = {!!}
