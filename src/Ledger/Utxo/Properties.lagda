\subsection{UTxO}
\label{sec:utxo-properties}

\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Ledger.Transaction

module Ledger.Utxo.Properties (txs : TransactionStructure) where

open import Prelude hiding (_+_)
open import Ledger.Prelude renaming (_+_ to _+ℕ_)

open import Algebra              using     (CommutativeMonoid ; Monoid)
open import Algebra.Morphism     using     (module MonoidMorphisms ; IsMagmaHomomorphism)
open import Data.Integer         using     (ℤ; _⊖_ ; _-_ ; 0ℤ)
                                 renaming  (_+_ to _+ℤ_ ; +_ to _⁺ ; -_ to _⁻)
open import Data.Integer.Ext     using     (posPart ; negPart)
open import Data.Nat.Properties  hiding    (_≟_)
open import Data.Sign            using     (Sign)
open import Relation.Binary      using     (IsEquivalence)

open import Tactic.Cong
open import Tactic.EquationalReasoning
open import Tactic.MonoidSolver

import Data.Nat as ℕ
import Data.Integer.Properties as ℤ

open TransactionStructure txs

open import Ledger.PParams epochStructure
open import Ledger.TokenAlgebra ScriptHash
open import Ledger.Utxo txs renaming (Computational-UTXO to Computational-UTXO')

open TxBody
open TxWitnesses
open Tx

open Equivalence
open Properties

open Tactic.EquationalReasoning.≡-Reasoning {A = ℕ} (solve-macro (quoteTerm +-0-monoid))

instance
  _ = TokenAlgebra.Value-CommutativeMonoid tokenAlgebra
  _ = +-0-monoid

record Add (A : Set) : Set where
  infixl 7 _+_
  field _+_ : A → A → A

open Add ⦃ ... ⦄ public

instance
  addInt : Add ℤ
  addInt = record { _+_ = _+ℤ_ }

  addNat : Add ℕ
  addNat = record { _+_ = _+ℕ_ }

  addCommMon : Add (TokenAlgebra.Value tokenAlgebra)
  addCommMon = record { _+_ = _+ᵛ_ }

private variable
  tx                               : TxBody
  utxo utxo'                       : UTxO
  Γ                                : UTxOEnv
  utxoState utxoState'             : UTxOState
  fees fees' donations donations'  : Coin
  deposits deposits'               : DepositPurpose ⇀ Coin

abstract
  Computational-UTXO : Computational _⊢_⇀⦇_,UTXO⦈_
  Computational-UTXO = Computational-UTXO'

balance-cong : proj₁ utxo ≡ᵉ proj₁ utxo' → balance utxo ≈ balance utxo'
balance-cong {utxo} {utxo'} = indexedSumᵐ-cong {x = utxo ᶠᵐ} {utxo' ᶠᵐ}

balance-cong-coin : proj₁ utxo ≡ᵉ proj₁ utxo' → cbalance utxo ≡ cbalance utxo'
balance-cong-coin {utxo} {utxo'} x = coinIsMonoidHomomorphism .⟦⟧-cong (balance-cong {utxo} {utxo'} x)
  where open MonoidMorphisms.IsMonoidHomomorphism

open MonoidMorphisms.IsMonoidHomomorphism
private
  ∙-homo-Coin = IsMagmaHomomorphism.homo (isMagmaHomomorphism coinIsMonoidHomomorphism)

balance-∪ : disjoint (dom (utxo ˢ)) (dom (utxo' ˢ))
                     → cbalance (utxo ∪ᵐˡ utxo') ≡ cbalance utxo + cbalance utxo'
balance-∪ {utxo} {utxo'} h = begin
  cbalance (utxo ∪ᵐˡ utxo')
    ≡⟨ ⟦⟧-cong coinIsMonoidHomomorphism (indexedSumᵐ-cong {x = (utxo ∪ᵐˡ utxo') ᶠᵐ} {(utxo ᶠᵐ) ∪ᵐˡᶠ (utxo' ᶠᵐ)} (id , id)) ⟩
  coin (indexedSumᵐ _ ((utxo ᶠᵐ) ∪ᵐˡᶠ (utxo' ᶠᵐ)))
    ≡⟨ ⟦⟧-cong coinIsMonoidHomomorphism (indexedSumᵐ-∪ {X = utxo ᶠᵐ} {utxo' ᶠᵐ} h) ⟩
  coin (balance utxo + balance utxo')
    ≡⟨ ∙-homo-Coin  _ _ ⟩
  cbalance utxo + cbalance utxo' ∎

newTxid⇒disj : txid tx ∉ map proj₁ (dom (utxo ˢ)) → disjoint' (dom (utxo ˢ)) (dom ((outs tx) ˢ))
newTxid⇒disj id∉utxo = disjoint⇒disjoint' λ h h' → id∉utxo $ to ∈-map
  (-, (case from ∈-map h' of λ where (_ , refl , h'') → case from ∈-map h'' of λ where (_ , refl , _) → refl) , h)

consumedCoinEquality : ∀ {pp} → coin (mint tx) ≡ 0
                     → coin (consumed pp utxoState tx)
                     ≡ cbalance ((UTxOState.utxo utxoState) ∣ txins tx) + depositRefunds pp utxoState tx
consumedCoinEquality {tx} {utxoState} {pp} h = let utxo = UTxOState.utxo utxoState in begin
  coin (balance (utxo ∣ txins tx) + mint tx + inject (depositRefunds pp utxoState tx))
    ≡⟨ ∙-homo-Coin _ _ ⟩
  coin (balance (utxo ∣ txins tx) + mint tx) + coin (inject $ depositRefunds pp utxoState tx)
    ≡⟨ cong (coin (balance (utxo ∣ txins tx) + mint tx) +_) (property _) ⟩
  coin (balance (utxo ∣ txins tx) + mint tx) + depositRefunds pp utxoState tx
    ≡⟨ cong (_+ depositRefunds pp utxoState tx) (∙-homo-Coin _ _) ⟩
  coin (balance (utxo ∣ txins tx)) + coin (mint tx) + depositRefunds pp utxoState tx
    ≡⟨ cong (λ x → cbalance (utxo ∣ txins tx) + x + depositRefunds pp utxoState tx) h ⟩
  cbalance (utxo ∣ txins tx) + 0 + depositRefunds pp utxoState tx
    ≡⟨ cong (_+ depositRefunds pp utxoState tx) (+-identityʳ (cbalance (utxo ∣ txins tx))) ⟩
  cbalance (utxo ∣ txins tx) + depositRefunds pp utxoState tx                        ∎


producedCoinEquality : ∀ {pp}
  → coin (produced pp utxoState tx) ≡ cbalance (outs tx) + txfee tx + newDeposits pp utxoState tx + txdonation tx

producedCoinEquality {utxoState} {tx} {pp} = begin
  coin (balOut + inject (txfee tx) + inject newDep + inject don)         ≡⟨ ∙-homo-Coin _ _ ⟩
  coin (balOut + inject (txfee tx) + inject newDep) + coin (inject don)  ≡⟨ cong (_+ coin (inject don)) γ ⟩
  coin balOut + txfee tx + newDep + coin (inject don)                    ≡⟨ cong (coin balOut + txfee tx + newDep +_)(property _) ⟩
  coin balOut + txfee tx + newDep + don                                  ∎
    where
    newDep don : Coin
    newDep = newDeposits pp utxoState tx
    don = txdonation tx

    balOut : Value
    balOut = balance (outs tx)

    γ : coin (balOut + inject (txfee tx) + inject newDep) ≡ cbalance (outs tx) + txfee tx + newDep
    γ = begin
      coin (balOut + inject (txfee tx) + inject newDep)              ≡⟨ ∙-homo-Coin _ _ ⟩
      coin (balOut + inject (txfee tx)) + coin (inject newDep)       ≡⟨ cong (_+ coin (inject newDep)) (∙-homo-Coin _ _)  ⟩
      coin balOut + coin (inject (txfee tx)) + coin (inject newDep)  ≡⟨ cong (coin balOut + coin (inject (txfee tx)) +_)(property _) ⟩
      coin balOut + coin (inject (txfee tx)) + newDep                ≡⟨ cong (λ x → coin balOut + x + newDep) (property _) ⟩
      coin balOut + txfee tx + newDep                                ∎

balValueToCoin : ∀ {pp} → coin (mint tx) ≡ 0 → consumed pp utxoState tx ≡ produced pp utxoState tx
               → cbalance ((UTxOState.utxo utxoState) ∣ txins tx) + depositRefunds pp utxoState tx
               ≡ cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx + txdonation tx
balValueToCoin {tx} {utxoState} {pp} h h' = begin
  cbalance ((UTxOState.utxo utxoState) ∣ txins tx) + depositRefunds pp utxoState tx
    ≡˘⟨ consumedCoinEquality {tx} {utxoState} {pp} h ⟩
  coin (consumed pp utxoState tx) ≡⟨ cong! h' ⟩
  coin (produced pp utxoState tx) ≡⟨ producedCoinEquality {utxoState} {tx} {pp} ⟩
  cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx + txdonation tx ∎


posPart-negPart≡x : ∀ {x} → posPart x ⊖ negPart x ≡ x
posPart-negPart≡x {n ⁺}     = refl
posPart-negPart≡x {ℤ.negsuc n} = refl

module DepositHelpers
  {utxo utxo' : UTxO}
  {fees fees' : Coin}
  {deposits deposits' : DepositPurpose ⇀ Coin}
  {donations donations' : Coin}
  {tx : TxBody}
  {Γ : UTxOEnv}
  (step : Γ ⊢ ⟦ utxo , fees , deposits , donations ⟧ᵘ ⇀⦇ tx ,UTXO⦈ ⟦ utxo' , fees' , deposits' , donations' ⟧ᵘ)
  (h' : txid tx ∉ map proj₁ (dom (utxo ˢ)))
  where

  private
    pp : PParams
    pp = UTxOEnv.pparams Γ

    utxoSt : UTxOState
    utxoSt = ⟦ utxo , fees , deposits , donations ⟧ᵘ

    utxoIns utxoInsᶜ : UTxO
    utxoInsᶜ = utxo ∣ txins tx ᶜ
    utxoIns = utxo ∣ txins tx

    dep uDep ref tot remDepTot don tot+remDep : Coin
    dep         = getCoin deposits
    uDep        = getCoin (updateDeposits pp tx deposits)
    ref         = depositRefunds pp utxoSt tx
    tot         = newDeposits pp utxoSt tx
    remDepTot   = getCoin deposits ∸ ref
    don         = txdonation tx
    tot+remDep  = tot + remDepTot

    Δdep : ℤ
    Δdep = depositsChange pp tx deposits

    h : disjoint (dom (utxoInsᶜ ˢ)) (dom (outs tx ˢ))
    h = λ h₁ h₂ → ∉-∅ $ proj₁ (newTxid⇒disj {tx = tx} {utxo} h') $ to ∈-∩ (res-comp-domᵐ h₁ , h₂)

    newBal'  : Γ ⊢ ⟦ utxo , fees , deposits , donations ⟧ᵘ ⇀⦇ tx ,UTXO⦈ ⟦ utxo' , fees' , deposits' , donations' ⟧ᵘ
             → consumed pp utxoSt tx ≡ produced pp utxoSt tx
    newBal' (UTXO-inductive _ _ _ _ x _ _) = x

    newBal : consumed pp utxoSt tx ≡ produced pp utxoSt tx
    newBal = newBal' step

    noMintAda'  : Γ ⊢ ⟦ utxo , fees , deposits , donations ⟧ᵘ ⇀⦇ tx ,UTXO⦈ ⟦ utxo' , fees' , deposits' , donations' ⟧ᵘ
                → coin (mint tx) ≡ 0
    noMintAda' (UTXO-inductive _ _ _ _ _ x _) = x

    noMintAda : coin (mint tx) ≡ 0
    noMintAda = noMintAda' step


  uDep≡
    : Γ ⊢ ⟦ utxo , fees , deposits , donations ⟧ᵘ ⇀⦇ tx ,UTXO⦈ ⟦ utxo' , fees' , deposits' , donations' ⟧ᵘ
    → deposits' ≡ updateDeposits pp tx deposits
  uDep≡ (UTXO-inductive _ _ _ _ _ _ _) = refl

  deposits-change' : Δdep ≡ tot ⊖ ref
  deposits-change' = sym posPart-negPart≡x

  dep-ref : tot ≡ 0 → uDep + ref ≡ dep
  dep-ref tot≡0 = ℤ.+-injective $ begin
    (uDep + ref)⁺           ≡⟨ ℤ.pos-+ uDep ref ⟩
    uDep ⁺ + (ref ⊖ 0)      ≡˘⟨ cong (λ x → uDep ⁺ + (ref ⊖ x)) tot≡0 ⟩
    uDep ⁺ + (ref ⊖ tot)    ≡⟨ cong (_+_ (uDep ⁺)) (ℤ.⊖-swap ref tot) ⟩
    uDep ⁺ - (tot ⊖ ref)    ≡˘⟨ cong! deposits-change' ⟩
    uDep ⁺ - Δdep           ≡˘⟨ cong (uDep ⁺ +_) (ℤ.⊖-swap dep uDep) ⟩
    uDep ⁺ + (dep ⊖ uDep)   ≡⟨ ℤ.distribʳ-⊖-+-pos uDep dep uDep ⟩
    uDep + dep ⊖ uDep       ≡⟨ cong (_⊖ uDep) (+-comm uDep dep) ⟩
    dep + uDep ⊖ uDep       ≡˘⟨ ℤ.distribʳ-⊖-+-pos dep uDep uDep ⟩
    dep ⁺  + (uDep ⊖ uDep)  ≡⟨ cong (dep ⁺ +_) (ℤ.n⊖n≡0 uDep) ⟩
    dep ⁺ + 0ℤ              ≡⟨ ℤ.+-identityʳ _ ⟩
    dep ⁺                   ∎

  ref-tot-0 : ref ≢ 0 → tot ≡ 0
  ref-tot-0 ref≢0 with Δdep
  ... | n ⁺         = ⊥-elim (ref≢0 refl)
  ... | ℤ.negsuc n  = refl

  ref≤dep : ref ℕ.≤ dep
  ref≤dep with ref ≟ 0
  ... | no ¬p = ≤″⇒≤ $ less-than-or-equal $ begin
    ref + uDep ≡⟨ +-comm ref uDep ⟩
    uDep + ref ≡⟨ dep-ref $ ref-tot-0 ¬p ⟩
    dep        ∎
  ... | yes p rewrite p = z≤n

  deposits-change : uDep ≡ dep + tot ∸ ref
  deposits-change = ℤ.+-injective $ begin
    uDep ⁺                        ≡˘⟨ ℤ.+-identityʳ _ ⟩
    uDep ⁺ + 0ℤ                   ≡˘⟨ cong (uDep ⁺ +_) (ℤ.+-inverseˡ (dep ⁺)) ⟩
    uDep ⁺ + ((dep ⁺) ⁻ + dep ⁺)  ≡˘⟨ ℤ.+-assoc (uDep ⁺) ((dep ⁺) ⁻) (dep ⁺) ⟩
    (uDep ⁺ - dep ⁺) + dep ⁺      ≡⟨ cong (_+ dep ⁺) (ℤ.m-n≡m⊖n uDep dep) ⟩
    Δdep + dep ⁺                  ≡⟨ ℤ.+-comm Δdep (dep ⁺) ⟩
    dep ⁺ + Δdep                  ≡⟨ cong (dep ⁺ +_) deposits-change' ⟩
    dep ⁺ + (tot ⊖ ref)           ≡⟨ ℤ.distribʳ-⊖-+-pos dep tot ref ⟩
    dep + tot ⊖ ref               ≡⟨ ℤ.⊖-≥ (m≤n⇒m≤n+o tot ref≤dep) ⟩
    (dep + tot ∸ ref) ⁺ ∎

  utxo-ref-prop : cbalance utxo + ref ≡ (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx) + don + tot
  utxo-ref-prop = begin
    cbalance utxo + ref ≡˘⟨ γ ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ utxoIns) + ref                              ≡⟨ cong (_+ ref) (balance-∪ {utxoInsᶜ} {utxoIns} (flip res-ex-disjoint)) ⟩
    cbalance utxoInsᶜ + cbalance utxoIns + ref                         ≡⟨ +-assoc (cbalance utxoInsᶜ) (cbalance utxoIns) ref ⟩
    cbalance utxoInsᶜ + (cbalance utxoIns + ref)                       ≡⟨ cong (cbalance utxoInsᶜ +_) (balValueToCoin {tx} {utxoSt} noMintAda newBal) ⟩
    cbalance utxoInsᶜ + (cbalance (outs tx) + txfee tx + tot + don)    ≡⟨ cong (cbalance utxoInsᶜ +_ ) (+-assoc (cbalance (outs tx) + txfee tx) tot don) ⟩
    cbalance utxoInsᶜ + (cbalance (outs tx) + txfee tx + (tot + don))  ≡⟨ cong (λ x → cbalance utxoInsᶜ + (cbalance (outs tx) + txfee tx + x)) (+-comm tot don) ⟩
    cbalance utxoInsᶜ + (cbalance (outs tx) + txfee tx + (don + tot))  ≡˘⟨ +-assoc (cbalance utxoInsᶜ) (cbalance (outs tx) + txfee tx) (don + tot) ⟩
    cbalance utxoInsᶜ + (cbalance (outs tx) + txfee tx) + (don + tot)  ≡˘⟨ cong (_+ (don + tot)) (+-assoc (cbalance utxoInsᶜ) (cbalance (outs tx)) (txfee tx)) ⟩
    cbalance utxoInsᶜ + cbalance (outs tx) + txfee tx + (don + tot)    ≡˘⟨ cong (λ x → x + (txfee tx) + (don + tot)) (balance-∪ {utxoInsᶜ} {outs tx} h) ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx + (don + tot)           ≡˘⟨ +-assoc (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx) don tot ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx + don + tot             ∎
    where
      γ : cbalance (utxoInsᶜ ∪ᵐˡ utxoIns) + ref ≡ cbalance utxo + ref
      γ = cong (_+ ref) (balance-cong-coin {utxo = utxoInsᶜ ∪ᵐˡ utxoIns} {utxo' = utxo}
          let open IsEquivalence ≡ᵉ-isEquivalence renaming (trans to _≡ᵉ-∘_)
          in (disjoint-∪ᵐˡ-∪ (disjoint-sym res-ex-disjoint) ≡ᵉ-∘ ∪-sym) ≡ᵉ-∘ res-ex-∪ (_∈? txins tx))


  rearrange0 : txfee tx + don + (tot + remDepTot) + fees ≡ fees + txfee tx + getCoin deposits' + don
  rearrange0 = begin
    txfee tx + don + tot+remDep + fees         ≡⟨ +-comm (txfee tx + don + tot+remDep) fees ⟩
    fees + (txfee tx + don + tot+remDep)       ≡⟨ cong (fees +_) (+-assoc (txfee tx) don tot+remDep) ⟩
    fees + (txfee tx + (don + tot+remDep))     ≡˘⟨ +-assoc fees (txfee tx) (don + tot+remDep) ⟩
    fees + txfee tx + (don + tot+remDep)       ≡⟨ cong (fees + txfee tx +_) (+-comm don tot+remDep) ⟩
    fees + txfee tx + (tot + remDepTot + don)  ≡˘⟨ +-assoc (fees + txfee tx) tot+remDep don ⟩
    fees + txfee tx + tot+remDep + don         ≡⟨ cong (λ x → (fees + txfee tx) + x + don) γ ⟩
    fees + txfee tx + getCoin deposits' + don  ∎
      where

      γ : tot + remDepTot ≡ getCoin deposits'
      γ = begin
        tot + (dep ∸ ref)  ≡˘⟨ +-∸-assoc tot ref≤dep ⟩
        tot + dep ∸ ref    ≡⟨ cong (_∸ ref) (+-comm tot dep) ⟩
        dep + tot ∸ ref    ≡˘⟨ deposits-change ⟩
        uDep               ≡⟨ cong getCoin (sym $ uDep≡ step) ⟩
        getCoin deposits'  ∎

  rearrange1 : cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (txfee tx + don + (tot + remDepTot) + fees)
          ≡ cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + ((fees + txfee tx) + getCoin deposits' + don)
  rearrange1 = cong (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) +_) rearrange0

\end{code}

Here, we state the fact that the UTxO relation is computable. This
just follows from our automation.

\begin{figure*}[h]
\begin{code}
UTXO-step : UTxOEnv → UTxOState → TxBody → Maybe UTxOState
UTXO-step = compute Computational-UTXO

UTXO-step-computes-UTXO :
  UTXO-step Γ utxoState tx ≡ just utxoState' ⇔ Γ ⊢ utxoState ⇀⦇ tx ,UTXO⦈ utxoState'
UTXO-step-computes-UTXO = ≡-just⇔STS Computational-UTXO
\end{code}
\caption{Computing the UTXO transition system}
\end{figure*}

\begin{property}[\textbf{Preserve Balance}]
For all $\var{env}\in\UTxOEnv$, $\var{utxo},\var{utxo'}\in\UTxO$,
$\var{fees},\var{fees'}\in\Coin$ and $\var{tx}\in\TxBody$, if
\begin{code}[hide]
pov :
\end{code}
\begin{code}[inline*]
  txid tx ∉ map proj₁ (dom (utxo ˢ))
\end{code}
and
\begin{code}[hide]
  →
\end{code}
\begin{code}[inline*]
      Γ ⊢ ⟦ utxo , fees , deposits , donations ⟧ᵘ ⇀⦇ tx ,UTXO⦈ ⟦ utxo' , fees' , deposits' , donations' ⟧ᵘ
\end{code}
then
\begin{code}[hide]
  →
\end{code}
\begin{code}
      getCoin ⟦ utxo , fees , deposits , donations ⟧ᵘ ≡ getCoin ⟦ utxo' , fees' , deposits' , donations' ⟧ᵘ
\end{code}
\begin{code}[hide]
pov {tx} {utxo} {_} {fees} {deps} {dons} {_} {fees'} {deps'} h' step@(UTXO-inductive {Γ} _ _ _ _ _ _ _) =
  let  utxoInsᶜ = utxo ∣ txins tx ᶜ
       donate = txdonation tx in
  begin
    cbalance utxo + fees + dep + dons   ≡⟨ cong (_+ dons) γ ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + ((fees + txfee tx) + getCoin deps' + donate) + dons ≡⟨ cong (λ x → cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + x + dons) (+-assoc (fees + txfee tx) (getCoin deps') (donate)) ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + ((fees + txfee tx) + (getCoin deps' + donate)) + dons ≡˘⟨ cong (_+ dons) (+-assoc (cbalance (utxoInsᶜ ∪ᵐˡ outs tx)) (fees + txfee tx) (getCoin deps' + donate)) ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx) + (getCoin deps' + donate) + dons ≡˘⟨ cong (_+ dons) (+-assoc (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx)) (getCoin deps') (donate)) ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx) + getCoin deps' + donate + dons ≡⟨ +-assoc (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx) + getCoin deps') (donate) dons ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx) + getCoin deps' + (donate + dons)
      ≡⟨ cong (λ x → cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx) + getCoin deps' + x) (+-comm (donate) dons) ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx) + getCoin deps' + (dons + donate) ∎
      where
      utxoSt = ⟦ utxo , fees , deps , dons ⟧ᵘ
      dep = getCoin deps
      pp = UTxOEnv.pparams Γ
      ref = depositRefunds pp utxoSt tx
      remDepTot = getCoin deps ∸ ref
      tot = newDeposits pp utxoSt tx
      donate = txdonation tx
      utxoInsᶜ = utxo ∣ txins tx ᶜ
      open DepositHelpers step h'
      γ : cbalance utxo + fees + dep ≡ cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + ((fees + txfee tx) + getCoin deps' + donate)
      γ = begin
          cbalance utxo + fees + dep                                                       ≡⟨ +-assoc (cbalance utxo) fees dep ⟩
          cbalance utxo + (fees + dep)                                                     ≡⟨ cong (cbalance utxo +_) (+-comm fees dep) ⟩
          cbalance utxo + (dep + fees)                                                     ≡˘⟨ cong (λ x → cbalance utxo + (x + fees)) (m+[n∸m]≡n ref≤dep) ⟩
          cbalance utxo + (ref + remDepTot + fees)                                         ≡⟨ cong (cbalance utxo +_) (+-assoc ref remDepTot fees) ⟩
          cbalance utxo + (ref + (remDepTot + fees))                                       ≡˘⟨ +-assoc (cbalance utxo ) ref (remDepTot + fees) ⟩
          cbalance utxo + ref + (remDepTot + fees)                                         ≡⟨ cong (_+ (remDepTot + fees)) utxo-ref-prop ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx + donate + tot + (remDepTot + fees)    ≡˘⟨ +-assoc (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx + donate + tot) remDepTot fees ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx + donate + tot + remDepTot + fees      ≡⟨ cong (_+ fees) (+-assoc (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx + donate) tot remDepTot) ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx + donate + (tot + remDepTot) + fees    ≡⟨ cong (λ x → x + (tot + remDepTot) + fees) (+-assoc (cbalance (utxoInsᶜ ∪ᵐˡ outs tx)) (txfee tx) donate) ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (txfee tx + donate) + (tot + remDepTot) + fees  ≡⟨ cong (_+ fees) (+-assoc (cbalance (utxoInsᶜ ∪ᵐˡ outs tx)) (txfee tx + donate) (tot + remDepTot)) ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (txfee tx + donate + (tot + remDepTot)) + fees  ≡⟨ +-assoc (cbalance (utxoInsᶜ ∪ᵐˡ outs tx)) (txfee tx + donate + (tot + remDepTot)) fees ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (txfee tx + donate + (tot + remDepTot) + fees)  ≡⟨ rearrange1 ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx + getCoin deps' + donate)  ∎

\end{code}

\end{property}
