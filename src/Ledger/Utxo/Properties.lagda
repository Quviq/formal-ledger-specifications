\subsection{UTxO}
\label{sec:utxo-properties}

\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Ledger.Transaction

module Ledger.Utxo.Properties (txs : TransactionStructure) where

open import Prelude
open import Ledger.Prelude

import Data.List as List
import Data.Nat as ℕ
open import Algebra.Morphism
open import Data.Nat.Properties using
  (+-0-commutativeMonoid; +-0-monoid; +-comm; +-identityʳ; +-assoc; +-∸-assoc; m≤n⇒m≤n+o; ≤″⇒≤; m+[n∸m]≡n)
open import Data.Sign using (Sign)
open import Data.Integer as ℤ using (ℤ; _⊖_)
open import Data.Integer.Ext
import Data.Integer.Properties as ℤ
open import Interface.ComputationalRelation
open import Relation.Binary
open import Tactic.Cong
open import Tactic.EquationalReasoning
open import Tactic.MonoidSolver

open TransactionStructure txs

open import Ledger.PParams epochStructure
open import Ledger.TokenAlgebra using (TokenAlgebra)
open import Ledger.Utxo txs

open TxBody
open TxWitnesses
open Tx

open Equivalence
open Properties

import Data.Nat.Tactic.RingSolver as ℕ
open Tactic.EquationalReasoning.≡-Reasoning {A = ℕ} (solve-macro (quoteTerm +-0-monoid))

instance
  _ = TokenAlgebra.Value-CommutativeMonoid tokenAlgebra
  _ = +-0-monoid

private variable
  tx : TxBody
  utxo utxo' utxo1 utxo2 : UTxO
  fee fee' fees fees' : Coin
  utxoState utxoState' utxoState1 utxoState2 : UTxOState
  deposits deposits' : DepositPurpose ⇀ Coin
  Γ : UTxOEnv
  s s' : UTxOState

⟦⟧-cong-Coin = IsCommutativeMonoidMorphism.⟦⟧-cong coinIsMonoidMorphism
∙-homo-Coin = IsCommutativeMonoidMorphism.∙-homo

balance-cong : proj₁ utxo ≡ᵉ proj₁ utxo' → balance utxo ≈ balance utxo'
balance-cong {utxo} {utxo'} = indexedSumᵐ-cong {x = utxo ᶠᵐ} {utxo' ᶠᵐ}

balance-cong-coin : proj₁ utxo ≡ᵉ proj₁ utxo' → cbalance utxo ≡ cbalance utxo'
balance-cong-coin {utxo} {utxo'} x = ⟦⟧-cong-Coin (balance-cong {utxo} {utxo'} x)

balance-∪ :  disjoint (dom (utxo ˢ)) (dom (utxo' ˢ))
  →          cbalance (utxo ∪ᵐˡ utxo') ≡ cbalance utxo + cbalance utxo'
balance-∪ {utxo} {utxo'} h = begin
  cbalance (utxo ∪ᵐˡ utxo')
    ≡⟨ ⟦⟧-cong-Coin (indexedSumᵐ-cong {x = (utxo ∪ᵐˡ utxo') ᶠᵐ} {(utxo ᶠᵐ) ∪ᵐˡᶠ (utxo' ᶠᵐ)} (id , id)) ⟩
  coin (indexedSumᵐ _ ((utxo ᶠᵐ) ∪ᵐˡᶠ (utxo' ᶠᵐ)))
    ≡⟨ ⟦⟧-cong-Coin (indexedSumᵐ-∪ {X = utxo ᶠᵐ} {utxo' ᶠᵐ} h) ⟩
  coin (balance utxo +ᵛ balance utxo')
    ≡⟨ ∙-homo-Coin coinIsMonoidMorphism _ _ ⟩
  cbalance utxo + cbalance utxo' ∎

newTxid⇒disj : txid tx ∉ map proj₁ (dom (utxo ˢ)) → disjoint' (dom (utxo ˢ)) (dom ((outs tx) ˢ))
newTxid⇒disj id∉utxo = disjoint⇒disjoint' λ h h' → id∉utxo $ to ∈-map
  (-, (case from ∈-map h' of λ where (_ , refl , h'') → case from ∈-map h'' of λ where (_ , refl , _) → refl) , h)

consumedCoinEquality :  ∀ {pp} → coin (mint tx) ≡ 0
                     → coin (consumed pp utxoState tx)
                     ≡ cbalance ((UTxOState.utxo utxoState) ∣ txins tx) + depositRefunds pp utxoState tx

-- ∀ {pp} → coin (mint tx) ≡ 0
--                      →  coin (consumed pp utxoState tx)
--                         ≡ cbalance ((UTxOState.utxo utxoState) ∣ txins tx) + depositRefunds utxoState tx
consumedCoinEquality {tx} {utxoState} {pp} h =
  let  utxo        = UTxOState.utxo utxoState
       balUtxo     = balance (utxo ∣ txins tx)
       depRefunds  = depositRefunds pp utxoState tx in begin
  coin (balUtxo +ᵛ mint tx +ᵛ inject depRefunds)          ≡⟨ ∙-homo-Coin coinIsMonoidMorphism _ _ ⟩
  coin (balUtxo +ᵛ mint tx) + coin (inject $ depRefunds)  ≡⟨ cong (coin (balUtxo +ᵛ mint tx) +_) (property _) ⟩
  coin (balUtxo +ᵛ mint tx) + depRefunds                  ≡⟨ cong! (∙-homo-Coin coinIsMonoidMorphism _ _) ⟩
  coin balUtxo + coin (mint tx) + depRefunds              ≡⟨ cong(λ x → cbalance(utxo ∣ txins tx)+ x + depRefunds)h ⟩
  cbalance (utxo ∣ txins tx) + 0 + depRefunds             ≡⟨ cong! (+-identityʳ (cbalance (utxo ∣ txins tx))) ⟩
  cbalance (utxo ∣ txins tx) + depRefunds                 ∎

producedCoinEquality : ∀ {pp} →  coin (produced pp utxoState tx)
                                 ≡ cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx
producedCoinEquality {utxoState} {tx} {pp} = begin
  coin (balance (outs tx) +ᵛ inject (txfee tx) +ᵛ inject (newDeposits pp utxoState tx))
    ≡⟨ ∙-homo-Coin coinIsMonoidMorphism _ _ ⟩
  coin (balance (outs tx) +ᵛ inject (txfee tx)) + coin (inject (newDeposits pp utxoState tx))
    ≡⟨ cong! (property _) ⟩
  coin (balance (outs tx) +ᵛ inject (txfee tx)) + newDeposits pp utxoState tx
    ≡⟨ cong! (∙-homo-Coin coinIsMonoidMorphism _ _) ⟩
  coin (balance (outs tx)) + coin (inject (txfee tx)) + newDeposits pp utxoState tx
    ≡⟨ cong (λ x → cbalance (outs tx) + x + newDeposits pp utxoState tx) (property (txfee tx)) ⟩
  cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx                     ∎

balValueToCoin :  ∀ {pp} → coin (mint tx) ≡ 0 → consumed pp utxoState tx ≡ produced pp utxoState tx
               →  cbalance ((UTxOState.utxo utxoState) ∣ txins tx) + depositRefunds pp utxoState tx
                  ≡ cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx
balValueToCoin {tx} {utxoState} {pp} h h' = begin
  cbalance ((UTxOState.utxo utxoState) ∣ txins tx) + depositRefunds pp utxoState tx
    ≡˘⟨ consumedCoinEquality {tx} {utxoState} {pp} h ⟩
  coin (consumed pp utxoState tx) ≡⟨ cong! h' ⟩
  coin (produced pp utxoState tx) ≡⟨ producedCoinEquality {utxoState} {tx} {pp} ⟩
  cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx ∎

posPart-negPart≡x : ∀ {x} → posPart x ⊖ negPart x ≡ x
posPart-negPart≡x {ℤ.+_ n}     = refl
posPart-negPart≡x {ℤ.negsuc n} = refl

module DepositHelpers
  (utxo : UTxO) (fees : Coin) (deposits : DepositPurpose ⇀ Coin) (tx : TxBody) (pp : PParams) where

  private
    dep = getCoin deposits
    uDep = getCoin (updateDeposits pp tx deposits)
    Δdep = depositsChange pp tx deposits
    ref = depositRefunds pp ⟦ utxo , fees , deposits ⟧ᵘ tx
    tot = newDeposits pp ⟦ utxo , fees , deposits ⟧ᵘ tx

  deposits-change' : Δdep ≡ tot ⊖ ref
  deposits-change' = sym posPart-negPart≡x

  dep-ref : tot ≡ 0 → uDep + ref ≡ dep
  dep-ref tot≡0 = ℤ.+-injective $ begin
    ℤ.+_ (uDep + ref)           ≡⟨ ℤ.pos-+ uDep ref ⟩
    ℤ.+_ uDep ℤ.+ (ref ⊖ 0)     ≡˘⟨ cong! tot≡0 ⟩
    ℤ.+_ uDep ℤ.+ (ref ⊖ tot)   ≡⟨ cong (ℤ._+_ (ℤ.+ uDep)) (ℤ.⊖-swap ref tot) ⟩
    ℤ.+_ uDep ℤ.- (tot ⊖ ref)   ≡˘⟨ cong! deposits-change' ⟩
    ℤ.+_ uDep ℤ.- Δdep          ≡˘⟨ cong (ℤ._+_ (ℤ.+ uDep)) (ℤ.⊖-swap dep uDep) ⟩
    ℤ.+_ uDep ℤ.+ (dep ⊖ uDep)  ≡⟨ ℤ.distribʳ-⊖-+-pos uDep dep uDep ⟩
    (uDep + dep) ⊖ uDep         ≡⟨ cong (_⊖ uDep) (+-comm uDep dep) ⟩
    (dep + uDep) ⊖ uDep         ≡˘⟨ ℤ.distribʳ-⊖-+-pos dep uDep uDep ⟩
    ℤ.+_ dep ℤ.+ (uDep ⊖ uDep)  ≡⟨ cong! (ℤ.n⊖n≡0 uDep) ⟩
    ℤ.+_ dep ℤ.+ ℤ.0ℤ           ≡⟨ ℤ.+-identityʳ _ ⟩
    ℤ.+_ dep                    ∎

  ref-tot-0 : ref ≢ 0 → tot ≡ 0
  ref-tot-0 ref≢0 with Δdep
  ... | ℤ.+_ n      = ⊥-elim (ref≢0 refl)
  ... | ℤ.negsuc n  = refl

  ref≤dep : ref ℕ.≤ dep
  ref≤dep with ref ≟ 0
  ... | no ¬p = ≤″⇒≤ $ less-than-or-equal $ begin
    ref + uDep  ≡⟨ +-comm ref uDep ⟩
    uDep + ref  ≡⟨ dep-ref $ ref-tot-0 ¬p ⟩
    dep         ∎
  ... | yes p rewrite p = z≤n

  deposits-change : uDep ≡ dep + tot ∸ ref
  deposits-change = ℤ.+-injective $ begin
    ℤ.+_ uDep                                  ≡˘⟨ ℤ.+-identityʳ _ ⟩
    ℤ.+_ uDep ℤ.+ ℤ.0ℤ                         ≡˘⟨ cong! (ℤ.+-inverseˡ (ℤ.+_ dep)) ⟩
    ℤ.+_ uDep ℤ.+ (ℤ.-_ (ℤ.+_ dep) ℤ.+ (ℤ.+_ dep))
      ≡˘⟨ ℤ.+-assoc (ℤ.+_ uDep) (ℤ.-_ (ℤ.+_ dep)) (ℤ.+_ dep) ⟩
    (ℤ.+_ uDep ℤ.- (ℤ.+_ dep)) ℤ.+ (ℤ.+_ dep)  ≡⟨ cong! (ℤ.m-n≡m⊖n uDep dep) ⟩
    Δdep ℤ.+ (ℤ.+_ dep)                        ≡⟨ ℤ.+-comm Δdep (ℤ.+_ dep) ⟩
    (ℤ.+_ dep) ℤ.+ Δdep                        ≡⟨ cong! deposits-change' ⟩
    (ℤ.+_ dep) ℤ.+ (tot ⊖ ref)                 ≡⟨ ℤ.distribʳ-⊖-+-pos dep tot ref ⟩
    (dep + tot) ⊖ ref                          ≡⟨ ℤ.⊖-≥ (m≤n⇒m≤n+o tot ref≤dep) ⟩
    ℤ.+_ (dep + tot ∸ ref)                     ∎

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
      Γ ⊢ ⟦ utxo , fees , deposits ⟧ᵘ ⇀⦇ tx ,UTXO⦈ ⟦ utxo' , fees' , deposits' ⟧ᵘ
\end{code}
then
\begin{code}[hide]
  →
\end{code}
\begin{code}
      getCoin ⟦ utxo , fees , deposits ⟧ᵘ ≡ getCoin ⟦ utxo' , fees' , deposits' ⟧ᵘ
\end{code}
\begin{code}[hide]
pov {tx}{utxo}{_}{fees}{deposits}{utxo'}{fees'}{deposits'} h' (UTXO-inductive {Γ} _ _ _ _ newBal noMintAda _) =
  begin
    cbalance utxo + fees + dep                           ≡tˡ⟨ cong (cbalance utxo +_) (+-comm fees _) ⟩
    cbalance utxo + (dep + fees)                         ≡˘⟨ cong (λ x → cbalance utxo + (x + fees)) (m+[n∸m]≡n (ref≤dep pp)) ⟩
    cbalance utxo + (ref + (dep ∸ ref) + fees)           ≡t⟨⟩
    cbalance utxo + ref + ((dep ∸ ref) + fees)           ≡⟨ cong (_+ (dep ∸ ref + fees)) i ⟩
    cbalIO + txfee tx + totDep + ((dep ∸ ref) + fees)    ≡t⟨⟩
    cbalIO + (txfee tx + totDep + (dep ∸ ref) + fees)    ≡⟨ cong (cbalIO +_) (+-comm (txfee tx + totDep + (dep ∸ ref)) fees) ⟩
    cbalIO + (fees + (txfee tx + totDep + (dep ∸ ref)))  ≡⟨ cong (cbalIO +_) ii ⟩
    cbalIO + (fees + txfee tx + (totDep + (dep ∸ ref)))  ≡˘⟨ +-assoc cbalIO (fees + txfee tx) (totDep + (dep ∸ ref)) ⟩
    cbalIO + (fees + txfee tx) + (totDep + (dep ∸ ref))  ≡⟨ cong (cbalIO + (fees + txfee tx) +_) $ iii ⟩
    cbalIO + (fees + txfee tx) + ((dep + totDep) ∸ ref)  ≡˘⟨ cong (cbalIO + (fees + txfee tx) +_) (deposits-change pp) ⟩
    cbalIO + (fees + txfee tx) + getCoin deposits'       ∎
  where
  open DepositHelpers utxo fees deposits tx

  utxoI utxoIC : TxIn ⇀ TxOut
  utxoI = utxo ∣ txins tx
  utxoIC = utxo ∣ txins tx ᶜ

  utxoSt : UTxOState
  utxoSt = ⟦ utxo , fees , deposits ⟧ᵘ

  pp : PParams
  pp = UTxOEnv.pparams Γ

  ref totDep dep cbalIO : ℕ
  ref = depositRefunds pp utxoSt tx
  totDep = newDeposits pp utxoSt tx
  dep = getCoin deposits
  cbalIO = cbalance (utxoIC ∪ᵐˡ outs tx)

  h₀ : proj₁ ((∈-sp Unionᵐ.∪ᵐˡ utxoIC) utxoI) ≡ᵉ proj₁ utxo
  h₀ =  let open IsEquivalence ≡ᵉ-isEquivalence renaming (trans to _≡ᵉ-∘_)
        in (disjoint-∪ᵐˡ-∪ (disjoint-sym res-ex-disjoint) ≡ᵉ-∘ ∪-sym) ≡ᵉ-∘ res-ex-∪ (_∈? txins tx)

  h₁ : disjoint (dom (utxoIC ˢ)) (dom (outs tx ˢ))
  h₁ = λ h₁ h₂ → ∉-∅ $ proj₁ (newTxid⇒disj {tx = tx} {utxo} h') $ to ∈-∩ (res-comp-domᵐ h₁ , h₂)

  i :  cbalance utxo + ref ≡  cbalance ((∈-sp Unionᵐ.∪ᵐˡ (∈-sp Restrictionᵐ.∣ utxo ᶜ) (txins tx))(outs tx))
                              + txfee tx + totDep
  i =  begin
    cbalance utxo + ref                                      ≡˘⟨ cong(_+ ref)(balance-cong-coin{utxo = utxoIC ∪ᵐˡ utxoI}{utxo' = utxo}h₀)⟩
    cbalance (utxoIC ∪ᵐˡ utxoI) + ref                        ≡⟨ cong! (balance-∪ {utxoIC} {utxoI} (flip res-ex-disjoint)) ⟩
    cbalance utxoIC + cbalance utxoI + ref                   ≡t⟨⟩
    cbalance utxoIC +(cbalance utxoI + ref)                  ≡⟨ cong(cbalance utxoIC +_)(balValueToCoin{tx}{utxoSt} noMintAda newBal) ⟩
    cbalance utxoIC +(cbalance(outs tx)+ txfee tx + totDep)  ≡t⟨⟩
    cbalance utxoIC + cbalance(outs tx)+ txfee tx + totDep   ≡˘⟨ cong (λ x → (x + txfee tx) + totDep) (balance-∪ {utxoIC} {outs tx} h₁) ⟩
    cbalance (utxoIC ∪ᵐˡ outs tx) + txfee tx + totDep        ∎

  ii : fees + (txfee tx + totDep + (dep ∸ ref)) ≡ fees + txfee tx + (totDep + (dep ∸ ref))
  ii = begin
    fees + (txfee tx + totDep + (dep ∸ ref))    ≡⟨ cong (fees +_) (+-assoc (txfee tx) totDep (dep ∸ ref)) ⟩
    fees + (txfee tx + (totDep + (dep ∸ ref)))  ≡˘⟨ +-assoc fees (txfee tx) (totDep + (dep ∸ ref)) ⟩
    fees + txfee tx + (totDep + (dep ∸ ref))    ∎

  iii : totDep + (dep ∸ ref) ≡ dep + totDep ∸ ref
  iii = begin
    totDep + (dep ∸ ref)  ≡˘⟨ +-∸-assoc totDep (ref≤dep pp) ⟩
    (totDep + dep) ∸ ref  ≡⟨ cong (_∸ ref) (+-comm totDep dep) ⟩
    (dep + totDep) ∸ ref  ∎
\end{code}

\end{property}
