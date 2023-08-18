\subsection{UTxO}
\label{sec:utxo-properties}

\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Ledger.Transaction

module Ledger.Utxo.Properties (txs : TransactionStructure) where

open import Prelude
open import Ledger.Prelude

open import Algebra                     using (CommutativeMonoid; Monoid)
open import Algebra.Morphism            using (module MonoidMorphisms; IsMagmaHomomorphism)
open import Data.Nat.Properties         hiding (_≟_)
open import Data.Sign                   using (Sign)
open import Data.Integer as ℤ           using (ℤ; _⊖_)
open import Data.Integer.Ext            using (posPart; negPart)
open import Relation.Binary             using (IsEquivalence)
open import Tactic.Cong                 using (cong!)
open import Tactic.EquationalReasoning  using (module ≡-Reasoning)
open import Tactic.MonoidSolver         using (solve-macro)

import Data.Nat as ℕ
import Data.Integer.Properties as ℤ

open TransactionStructure txs

open import Ledger.PParams epochStructure using (PParams)
open import Ledger.TokenAlgebra ScriptHash
open import Ledger.Utxo txs renaming (Computational-UTXO to Computational-UTXO')

open TxBody

open Equivalence
open Properties

open Tactic.EquationalReasoning.≡-Reasoning {A = ℕ} (solve-macro (quoteTerm +-0-monoid))

instance
  _ = TokenAlgebra.Value-CommutativeMonoid tokenAlgebra
  _ = +-0-monoid

private variable
  tx : TxBody
  utxo utxo' : UTxO
  fees fees' : Coin
  utxoState utxoState' : UTxOState
  deposits deposits' : DepositPurpose ⇀ Coin
  donations donations' : Coin
  Γ : UTxOEnv

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
  coin (balance utxo +ᵛ balance utxo')
    ≡⟨ ∙-homo-Coin  _ _ ⟩
  cbalance utxo + cbalance utxo' ∎

newTxid⇒disj : txid tx ∉ map proj₁ (dom (utxo ˢ)) → disjoint' (dom (utxo ˢ)) (dom ((outs tx) ˢ))
newTxid⇒disj id∉utxo = disjoint⇒disjoint' λ h h' → id∉utxo $ to ∈-map
  (-, (case from ∈-map h' of λ where (_ , refl , h'') → case from ∈-map h'' of λ where (_ , refl , _) → refl) , h)

consumedCoinEquality : ∀ {pp} → coin (mint tx) ≡ 0
                     → coin (consumed pp utxoState tx)
                     ≡ cbalance ((UTxOState.utxo utxoState) ∣ txins tx) + depositRefunds pp utxoState tx
consumedCoinEquality {tx} {utxoState} {pp} h =
  let  utxo = UTxOState.utxo utxoState
       utxoIns = utxo ∣ txins tx
  in begin
  coin (balance utxoIns +ᵛ mint tx +ᵛ inject (depositRefunds pp utxoState tx))
    ≡⟨ ∙-homo-Coin _ _ ⟩
  coin (balance utxoIns +ᵛ mint tx) + coin (inject $ depositRefunds pp utxoState tx)
    ≡⟨ cong (coin (balance utxoIns +ᵛ mint tx) +_) (property _) ⟩
  coin (balance utxoIns +ᵛ mint tx) + depositRefunds pp utxoState tx
    ≡⟨ cong! (∙-homo-Coin _ _) ⟩
  coin (balance utxoIns) + coin (mint tx) + depositRefunds pp utxoState tx
    ≡⟨ cong (λ x → cbalance utxoIns + x + depositRefunds pp utxoState tx) h ⟩
  cbalance utxoIns + 0 + depositRefunds pp utxoState tx
    ≡⟨ cong! (+-identityʳ (cbalance utxoIns)) ⟩
  cbalance utxoIns + depositRefunds pp utxoState tx                        ∎

producedCoinEquality : ∀ {pp} → coin (produced pp utxoState tx)
                              ≡ cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx + txdonation tx
producedCoinEquality {utxoState} {tx} {pp} = begin
  coin (balance (outs tx) +ᵛ inject (txfee tx) +ᵛ inject (newDeposits pp utxoState tx) +ᵛ inject (txdonation tx))
    ≡⟨ ∙-homo-Coin _ _ ⟩
  coin (balance (outs tx) +ᵛ inject (txfee tx) +ᵛ inject (newDeposits pp utxoState tx)) + coin (inject (txdonation tx))
    ≡⟨ cong (_+ coin (inject (txdonation tx))) (begin
      coin (balance (outs tx) +ᵛ inject (txfee tx) +ᵛ inject (newDeposits pp utxoState tx))
        ≡⟨ ∙-homo-Coin _ _ ⟩
      coin (balance (outs tx) +ᵛ inject (txfee tx)) + coin (inject (newDeposits pp utxoState tx))
        ≡⟨ cong! (property _) ⟩
      coin (balance (outs tx) +ᵛ inject (txfee tx)) + newDeposits pp utxoState tx
        ≡⟨ cong! (∙-homo-Coin _ _) ⟩
      coin (balance (outs tx)) + coin (inject (txfee tx)) + newDeposits pp utxoState tx
        ≡⟨ cong (λ x → cbalance (outs tx) + x + newDeposits pp utxoState tx) (property (txfee tx)) ⟩
      cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx                     ∎
    )⟩
  cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx + coin (inject (txdonation tx))
    ≡⟨ cong (cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx +_) (property _) ⟩
  cbalance (outs tx) + (txfee tx) + newDeposits pp utxoState tx + txdonation tx
    ∎

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
posPart-negPart≡x {ℤ.+_ n}     = refl
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
    uDep : Coin
    uDep = getCoin (updateDeposits pp tx deposits)
    Δdep : ℤ
    Δdep = depositsChange pp tx deposits
    utxoSt : UTxOState
    utxoSt = ⟦ utxo , fees , deposits , donations ⟧ᵘ
    ref : Coin
    ref = depositRefunds pp utxoSt tx
    tot : Coin
    tot = newDeposits    pp utxoSt tx

    utxoIns utxoInsᶜ : UTxO
    utxoInsᶜ = utxo ∣ txins tx ᶜ
    utxoIns = utxo ∣ txins tx

    h : disjoint (dom (utxoInsᶜ ˢ)) (dom (outs tx ˢ))
    h = λ h₁ h₂ → ∉-∅ $ proj₁ (newTxid⇒disj {tx = tx} {utxo} h') $ to ∈-∩ (res-comp-domᵐ h₁ , h₂)
    newBal'
      : Γ ⊢ ⟦ utxo , fees , deposits , donations ⟧ᵘ ⇀⦇ tx ,UTXO⦈ ⟦ utxo' , fees' , deposits' , donations' ⟧ᵘ
      → consumed pp utxoSt tx ≡ produced pp utxoSt tx
    newBal' (UTXO-inductive _ _ _ _ x _ _) = x
    newBal : consumed pp utxoSt tx ≡ produced pp utxoSt tx
    newBal = newBal' step
    noMintAda'
      : Γ ⊢ ⟦ utxo , fees , deposits , donations ⟧ᵘ ⇀⦇ tx ,UTXO⦈ ⟦ utxo' , fees' , deposits' , donations' ⟧ᵘ
      → coin (mint tx) ≡ 0
    noMintAda' (UTXO-inductive _ _ _ _ _ x _) = x
    noMintAda : coin (mint tx) ≡ 0
    noMintAda = noMintAda' step
    remDepTot : Coin
    remDepTot = getCoin deposits ∸ ref

  uDep≡
    : Γ ⊢ ⟦ utxo , fees , deposits , donations ⟧ᵘ ⇀⦇ tx ,UTXO⦈ ⟦ utxo' , fees' , deposits' , donations' ⟧ᵘ
    → deposits' ≡ updateDeposits pp tx deposits
  uDep≡ (UTXO-inductive _ _ _ _ _ _ _) = refl

  deposits-change' : Δdep ≡ tot ⊖ ref
  deposits-change' = sym posPart-negPart≡x

  dep-ref : tot ≡ 0 → uDep + ref ≡ getCoin deposits
  dep-ref tot≡0 = let dep = getCoin deposits in ℤ.+-injective $ begin
    ℤ.+_ (uDep + ref)          ≡⟨ ℤ.pos-+ uDep ref ⟩
    ℤ.+_ uDep ℤ.+ (ref ⊖ 0)    ≡˘⟨ cong! tot≡0 ⟩
    ℤ.+_ uDep ℤ.+ (ref ⊖ tot)  ≡⟨ cong (ℤ._+_ (ℤ.+ uDep)) (ℤ.⊖-swap ref tot) ⟩
    ℤ.+_ uDep ℤ.- (tot ⊖ ref)  ≡˘⟨ cong! deposits-change' ⟩
    ℤ.+_ uDep ℤ.- Δdep         ≡˘⟨ cong (ℤ._+_ (ℤ.+ uDep)) (ℤ.⊖-swap dep uDep) ⟩
    ℤ.+_ uDep ℤ.+ (dep ⊖ uDep) ≡⟨ ℤ.distribʳ-⊖-+-pos uDep dep uDep ⟩
    (uDep + dep) ⊖ uDep        ≡⟨ cong (_⊖ uDep) (+-comm uDep dep) ⟩
    (dep + uDep) ⊖ uDep        ≡˘⟨ ℤ.distribʳ-⊖-+-pos dep uDep uDep ⟩
    ℤ.+_ dep ℤ.+ (uDep ⊖ uDep) ≡⟨ cong! (ℤ.n⊖n≡0 uDep) ⟩
    ℤ.+_ dep ℤ.+ ℤ.0ℤ          ≡⟨ ℤ.+-identityʳ _ ⟩
    ℤ.+_ dep ∎

  ref-tot-0 : ref ≢ 0 → tot ≡ 0
  ref-tot-0 ref≢0 with Δdep
  ... | ℤ.+_ n     = ⊥-elim (ref≢0 refl)
  ... | ℤ.negsuc n = refl

  ref≤dep : ref ℕ.≤ getCoin deposits
  ref≤dep with ref ≟ 0
  ... | no ¬p = ≤″⇒≤ $ less-than-or-equal $ begin
    ref + uDep ≡⟨ +-comm ref uDep ⟩
    uDep + ref ≡⟨ dep-ref $ ref-tot-0 ¬p ⟩
    getCoin deposits       ∎
  ... | yes p rewrite p = z≤n

  deposits-change : uDep ≡ getCoin deposits + tot ∸ ref
  deposits-change = let dep = getCoin deposits in
    ℤ.+-injective $ begin
    ℤ.+_ uDep                                 ≡˘⟨ ℤ.+-identityʳ _ ⟩
    ℤ.+_ uDep ℤ.+ ℤ.0ℤ                        ≡˘⟨ cong! (ℤ.+-inverseˡ (ℤ.+_ dep)) ⟩
    ℤ.+_ uDep ℤ.+ (ℤ.-_ (ℤ.+_ dep) ℤ.+ (ℤ.+_ dep))
      ≡˘⟨ ℤ.+-assoc (ℤ.+_ uDep) (ℤ.-_ (ℤ.+_ dep)) (ℤ.+_ dep) ⟩
    (ℤ.+_ uDep ℤ.- (ℤ.+_ dep)) ℤ.+ (ℤ.+_ dep) ≡⟨ cong! (ℤ.m-n≡m⊖n uDep dep) ⟩
    Δdep ℤ.+ (ℤ.+_ dep)                       ≡⟨ ℤ.+-comm Δdep (ℤ.+_ dep) ⟩
    (ℤ.+_ dep) ℤ.+ Δdep                       ≡⟨ cong! deposits-change' ⟩
    (ℤ.+_ dep) ℤ.+ (tot ⊖ ref)                ≡⟨ ℤ.distribʳ-⊖-+-pos dep tot ref ⟩
    (dep + tot) ⊖ ref                         ≡⟨ ℤ.⊖-≥ (m≤n⇒m≤n+o tot ref≤dep) ⟩
    ℤ.+_ (dep + tot ∸ ref) ∎

  utxo-ref-prop :
    cbalance utxo + ref ≡
    (cbalance (utxo ∣ txins tx ᶜ ∪ᵐˡ outs tx) + txfee tx) + txdonation tx + tot
  utxo-ref-prop = begin
    cbalance utxo + ref ≡˘⟨ cong (_+ ref) γ ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ utxoIns) + ref
      ≡⟨ cong (_+ ref) (balance-∪ {utxoInsᶜ} {utxoIns} (flip res-ex-disjoint)) ⟩
    cbalance utxoInsᶜ + cbalance utxoIns + ref ≡t⟨⟩
    cbalance utxoInsᶜ + (cbalance utxoIns + ref)
      ≡⟨ cong (cbalance utxoInsᶜ +_)
         (balValueToCoin {tx} {utxoSt} {UTxOEnv.pparams Γ} noMintAda newBal) ⟩
    cbalance utxoInsᶜ + (cbalance (outs tx) + txfee tx + tot + txdonation tx) ≡t⟨⟩
    (cbalance utxoInsᶜ + cbalance (outs tx) + txfee tx) + tot + txdonation tx
      ≡˘⟨ cong (λ x → (x + txfee tx) + tot + txdonation tx) (balance-∪ {utxoInsᶜ} {outs tx} h) ⟩
    (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx) + tot + txdonation tx ≡t⟨⟩
    (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx) + (tot + txdonation tx)
      ≡⟨ cong ((cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx) +_) (+-comm tot (txdonation tx)) ⟩
    (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx) + (txdonation tx + tot) ≡t⟨⟩
    (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx) + txdonation tx + tot ∎
    where
    γ : cbalance (utxoInsᶜ ∪ᵐˡ utxoIns) ≡ cbalance utxo
    γ = (balance-cong-coin {utxo = utxoInsᶜ ∪ᵐˡ utxoIns} {utxo' = utxo}
          let open IsEquivalence ≡ᵉ-isEquivalence renaming (trans to _≡ᵉ-∘_)
          in (disjoint-∪ᵐˡ-∪ (disjoint-sym res-ex-disjoint) ≡ᵉ-∘ ∪-sym) ≡ᵉ-∘ res-ex-∪ (_∈? txins tx))


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
+-assoc-1 : (a b c d : ℕ) → a + b + c + d ≡ a + (b + (c + d))
+-assoc-1 a b c d =
  begin
    a + b + c + d      ≡⟨ +-assoc (a + b) c d ⟩
    a + b + (c + d)    ≡⟨ +-assoc a b (c + d) ⟩
    a + (b + (c + d))  ∎

+-assoc-2 : (a b c d e : ℕ) → a + b + c + d + e ≡ a + (b + (c + (d + e)))
+-assoc-2 a b c d e =
  begin
    a + b + c + d + e        ≡⟨ +-assoc (a + b + c) d e ⟩
    a + b + c + (d + e)      ≡⟨ +-assoc (a + b) c (d + e) ⟩
    a + b + (c + (d + e))    ≡⟨ +-assoc a b (c + (d + e)) ⟩
    a + (b + (c + (d + e)))  ∎




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
pov {tx} {utxo} {_} {fees} {dep} {don} {_} {fees'} {dep'} h' step@(UTXO-inductive {Γ} _ _ _ _ newBal noMintAda _) =
  begin
    cbalance utxo + fees + getCoin dep + don   ≡⟨ cong (_+ don) γ ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx + getCoin dep' + txdonation tx) + don ≡t⟨⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx) + getCoin dep' + (txdonation tx + don)
      ≡⟨ cong (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx) + getCoin dep' +_) (+-comm (txdonation tx) don) ⟩
    cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx) + getCoin dep' + (don + txdonation tx) ∎
    where
    utxoIns utxoInsᶜ : UTxO
    utxoInsᶜ = utxo ∣ txins tx ᶜ
    utxoIns = utxo ∣ txins tx

    ref tot remDepTot uDep : Coin
    ref = depositRefunds (UTxOEnv.pparams Γ) ⟦ utxo , fees , dep , don ⟧ᵘ tx
    tot = newDeposits    (UTxOEnv.pparams Γ) ⟦ utxo , fees , dep , don ⟧ᵘ tx
    uDep = getCoin (updateDeposits (UTxOEnv.pparams Γ) tx dep)
    remDepTot = getCoin dep ∸ ref
    open DepositHelpers step h'

    γ : cbalance utxo + fees + getCoin dep ≡ cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + ((fees + txfee tx) + getCoin dep' + txdonation tx)
    γ = begin
          cbalance utxo + fees + getCoin dep          ≡t⟨⟩
          cbalance utxo + (fees + getCoin dep)        ≡⟨ cong (cbalance utxo +_) (+-comm fees (getCoin dep)) ⟩
          cbalance utxo + (getCoin dep + fees)        ≡˘⟨ cong (λ x → cbalance utxo + (x + fees)) (m+[n∸m]≡n ref≤dep) ⟩
          cbalance utxo + (ref + remDepTot + fees)    ≡⟨ cong (cbalance utxo +_) (+-assoc ref remDepTot fees) ⟩
          cbalance utxo + (ref + (remDepTot + fees))  ≡˘⟨ +-assoc (cbalance utxo ) ref (remDepTot + fees) ⟩
          cbalance utxo + ref + (remDepTot + fees)    ≡⟨ cong (_+ (remDepTot + fees)) utxo-ref-prop ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + txfee tx + txdonation tx + tot + (remDepTot + fees)   ≡⟨ +-assoc-2 (cbalance (utxoInsᶜ ∪ᵐˡ outs tx)) (txfee tx) (txdonation tx) tot (remDepTot + fees) ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (txfee tx + (txdonation tx + (tot + (remDepTot + fees)))) ≡˘⟨ cong (λ x → cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (txfee tx + (txdonation tx + x))) (+-assoc tot remDepTot fees) ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (txfee tx + (txdonation tx + (tot + remDepTot + fees))) ≡⟨ cong (cbalance (utxoInsᶜ ∪ᵐˡ outs tx) +_) ϕ ⟩
          cbalance (utxoInsᶜ ∪ᵐˡ outs tx) + (fees + txfee tx + getCoin dep' + txdonation tx)  ∎
          where
          ζ : tot + remDepTot ≡ getCoin dep'
          ζ = begin
            tot + (getCoin dep ∸ ref)  ≡˘⟨ +-∸-assoc tot ref≤dep ⟩
            (tot + getCoin dep) ∸ ref  ≡⟨ cong (_∸ ref) (+-comm tot (getCoin dep)) ⟩
            (getCoin dep + tot) ∸ ref  ≡˘⟨ deposits-change ⟩
            uDep               ≡⟨ cong getCoin (sym $ uDep≡ step) ⟩
            getCoin dep'  ∎
          ϕ : txfee tx + (txdonation tx + (tot + remDepTot + fees)) ≡ fees + txfee tx + getCoin dep' + txdonation tx
          ϕ = begin
            txfee tx + (txdonation tx + (tot + remDepTot + fees)) ≡⟨ cong (λ x → txfee tx + (txdonation tx + (x + fees))) ζ ⟩
            txfee tx + (txdonation tx + (getCoin dep' + fees)) ≡⟨ cong (txfee tx +_) (+-comm (txdonation tx) (getCoin dep' + fees)) ⟩
            txfee tx + (getCoin dep' + fees + txdonation tx) ≡˘⟨ +-assoc (txfee tx) (getCoin dep' + fees ) (txdonation tx) ⟩
            txfee tx + (getCoin dep' + fees) + txdonation tx ≡˘⟨ cong (λ x → x + txdonation tx) (+-assoc (txfee tx) (getCoin dep') fees) ⟩
            txfee tx + getCoin dep' + fees + txdonation tx ≡⟨ cong (_+ txdonation tx) (+-comm (txfee tx + getCoin dep') fees) ⟩
            fees + (txfee tx + getCoin dep') + txdonation tx ≡˘⟨ cong (_+ txdonation tx) (+-assoc fees (txfee tx) (getCoin dep')) ⟩
            fees + txfee tx + getCoin dep' + txdonation tx  ∎



\end{code}

\end{property}
