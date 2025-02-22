\section{UTxO}
\label{sec:utxo}

\subsection{Accounting}

\begin{code}[hide]
{-# OPTIONS --safe #-}
{-# OPTIONS --overlapping-instances #-}

open import Ledger.Transaction

module Ledger.Utxo (txs : TransactionStructure) where

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
open import Ledger.PParams epochStructure
open import Ledger.TokenAlgebra using (TokenAlgebra)

open import MyDebugOptions
--open import Tactic.Defaults
open import Tactic.DeriveComp
open import Tactic.Derive.DecEq

instance
  _ = Decidable²⇒Dec _≤?_
  _ = TokenAlgebra.Value-CommutativeMonoid tokenAlgebra
  _ = +-0-monoid
  _ = +-0-commutativeMonoid

  HasCoin-Map : ∀ {A} → ⦃ DecEq A ⦄ → HasCoin (A ⇀ Coin)
  HasCoin-Map .getCoin s = Σᵐᵛ[ x ← s ᶠᵐ ] x


-- utxoEntrySizeWithoutVal = 27 words (8 bytes)
utxoEntrySizeWithoutVal : MemoryEstimate
utxoEntrySizeWithoutVal = 8

utxoEntrySize : TxOut → MemoryEstimate
utxoEntrySize (fst , v) = utxoEntrySizeWithoutVal + size v

-- TODO: fix this
serSize : Value → MemoryEstimate
serSize = λ _ → zero

\end{code}

Figure~\ref{fig:functions:utxo} defines functions needed for the UTxO transition system.
Figure~\ref{fig:ts-types:utxo-shelley} defines the types needed for the UTxO transition system.
The UTxO transition system is given in Figure~\ref{fig:rules:utxo-shelley}.

\begin{itemize}

  \item
    The function $\fun{outs}$ creates the unspent outputs generated by a transaction.
    It maps the transaction id and output index to the output.

  \item
    The $\fun{balance}$ function calculates sum total of all the coin in a given UTxO.
\end{itemize}

\AgdaTarget{outs, minfee, inInterval, balance}
\begin{figure*}[h]
\begin{code}
outs : TxBody → UTxO
outs tx = mapKeys (txid tx ,_) (txouts tx) λ where _ _ refl → refl

balance : UTxO → Value
balance utxo = Σᵐᵛ[ x ← utxo ᶠᵐ ] getValue x

cbalance : UTxO → Coin
cbalance utxo = coin (balance utxo)

minfee : PParams → TxBody → Coin
minfee pp tx = a * txsize tx + b
  where open PParams pp

data DepositPurpose : Set where
  CredentialDeposit  : Credential  → DepositPurpose
  PoolDeposit        : Credential  → DepositPurpose
  DRepDeposit        : Credential  → DepositPurpose
  GovActionDeposit   : GovActionID → DepositPurpose

certDeposit : PParams → DCert → Maybe (DepositPurpose × Coin)
certDeposit _   (delegate c _ _ v)  = just (CredentialDeposit c , v)
certDeposit pp  (regpool c _)       = just (PoolDeposit       c , PParams.poolDeposit pp)
certDeposit _   (regdrep c v _)     = just (DRepDeposit       c , v)
certDeposit _   _                   = nothing

certDepositᵐ : PParams → DCert → DepositPurpose ⇀ Coin
certDepositᵐ pp cert = case certDeposit pp cert of λ where
  (just (p , v))  → ❴ p , v ❵ᵐ
  nothing         → ∅ᵐ

certRefund : DCert → Maybe DepositPurpose
certRefund (delegate c nothing nothing x)  = just (CredentialDeposit c)
certRefund (deregdrep c)                   = just (DRepDeposit       c)
certRefund _                               = nothing

certRefundˢ : DCert → ℙ DepositPurpose
certRefundˢ = partialToSet certRefund

propDepositᵐ : PParams → GovActionID → GovProposal → DepositPurpose ⇀ Coin
propDepositᵐ pp gaid record { returnAddr = record { stake = c } }
  = ❴ GovActionDeposit gaid , PParams.govDeposit pp ❵ᵐ

-- this has to be a type definition for inference to work
data inInterval (slot : Slot) : (Maybe Slot × Maybe Slot) → Set where
  both  : ∀ {l r} → l ≤ˢ slot × slot ≤ˢ r  →  inInterval slot (just l  , just r)
  lower : ∀ {l}   → l ≤ˢ slot              →  inInterval slot (just l  , nothing)
  upper : ∀ {r}   → slot ≤ˢ r              →  inInterval slot (nothing , just r)
  none  :                                     inInterval slot (nothing , nothing)

\end{code}
\begin{code}[hide]
instance
  unquoteDecl DecEq-DepositPurpose = derive-DecEq ((quote DepositPurpose , DecEq-DepositPurpose) ∷ [])

  HasCoin-UTxO : HasCoin UTxO
  HasCoin-UTxO .getCoin = cbalance
\end{code}

\caption{Functions used in UTxO rules}
\label{fig:functions:utxo}
\end{figure*}

\AgdaTarget{UTxOEnv, UTxOState, \_⊢\_⇀⦇\_,UTXO⦈\_}
\begin{figure*}[h]
\emph{Derived types}
\begin{code}
Deposits = DepositPurpose ⇀ Coin
\end{code}
\emph{UTxO environment}
\begin{code}
record UTxOEnv : Set where
  field slot     : Slot
        pparams  : PParams
\end{code}
\emph{UTxO states}
\begin{code}
record UTxOState : Set where
  constructor ⟦_,_,_,_⟧ᵘ
  field utxo       : UTxO
        fees       : Coin
        deposits   : Deposits
        donations  : Coin
\end{code}
\emph{UTxO transitions}

\begin{code}[hide]
⟦_⟧ : {A : Set} → A → A
⟦_⟧ = id

instance
  _ = ≟-∅

  ∈-inst : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {s : ℙ A} → Dec₁ (_∈ s)
  ∈-inst {s = s} .Dec₁.P? = _∈? s

  all?' : ∀ {A : Set} {P : A → Set} ⦃ P? : Dec₁ P ⦄ ⦃ _ : DecEq A ⦄ {s : ℙ A} → Dec (All P s)
  all?' ⦃ P? = record { P? = P? } ⦄ {s} = all? P?

  netId? : ∀ {A : Set} {networkId : Network} {f : A → Network} → Dec₁ (λ a → f a ≡ networkId)
  netId? {_} {networkId} {f} .Dec₁.P? a = f a ≟ networkId

  Dec-inInterval : {slot : Slot} {I : Maybe Slot × Maybe Slot} → Dec (inInterval slot I)
  Dec-inInterval {slot} {just x  , just y } with x ≤ˢ? slot | slot ≤ˢ? y
  ... | no ¬p₁ | _      = no λ where (both (h₁ , h₂)) → ¬p₁ h₁
  ... | yes p₁ | no ¬p₂ = no λ where (both (h₁ , h₂)) → ¬p₂ h₂
  ... | yes p₁ | yes p₂ = yes (both (p₁ , p₂))
  Dec-inInterval {slot} {just x  , nothing} with x ≤ˢ? slot
  ... | no ¬p = no  (λ where (lower h) → ¬p h)
  ... | yes p = yes (lower p)
  Dec-inInterval {slot} {nothing , just x } with slot ≤ˢ? x
  ... | no ¬p = no  (λ where (upper h) → ¬p h)
  ... | yes p = yes (upper p)
  Dec-inInterval {slot} {nothing , nothing} = yes none

  HasCoin-UTxOState : HasCoin UTxOState
  HasCoin-UTxOState .getCoin s = getCoin (UTxOState.utxo s) + (UTxOState.fees s) + getCoin (UTxOState.deposits s) + UTxOState.donations s
data
\end{code}
\begin{code}
  _⊢_⇀⦇_,UTXO⦈_ : UTxOEnv → UTxOState → TxBody → UTxOState → Set
\end{code}
\caption{UTxO transition-system types}
\label{fig:ts-types:utxo-shelley}
\end{figure*}

\begin{figure*}
\begin{code}
updateCertDeposits : PParams → List DCert → DepositPurpose ⇀ Coin → DepositPurpose ⇀ Coin
updateCertDeposits _  []              deposits = deposits
updateCertDeposits pp (cert ∷ certs)  deposits =
  ((updateCertDeposits pp certs deposits) ∪⁺ certDepositᵐ pp cert) ∣ certRefundˢ cert ᶜ

updateProposalDeposits : PParams → TxId → List GovProposal → DepositPurpose ⇀ Coin → DepositPurpose ⇀ Coin
updateProposalDeposits pp _    []             deposits = deposits
updateProposalDeposits pp txid (prop ∷ props) deposits =
  updateProposalDeposits pp txid props deposits ∪⁺ propDepositᵐ pp (txid , length props) prop

updateDeposits : PParams → TxBody → DepositPurpose ⇀ Coin → DepositPurpose ⇀ Coin
updateDeposits pp txb = updateCertDeposits pp (txcerts txb)
                      ∘ updateProposalDeposits pp (txid txb) (txprop txb)

depositsChange : PParams → TxBody → DepositPurpose ⇀ Coin → ℤ
depositsChange pp txb deposits = getCoin (updateDeposits pp txb deposits) ⊖ getCoin deposits

depositRefunds : PParams → UTxOState → TxBody → Coin
depositRefunds pp st txb = negPart $ depositsChange pp txb deposits
  where open UTxOState st

newDeposits : PParams → UTxOState → TxBody → Coin
newDeposits pp st txb = posPart $ depositsChange pp txb deposits
  where open UTxOState st

consumed : PParams → UTxOState → TxBody → Value
consumed pp st txb = balance (UTxOState.utxo st ∣ txins txb)
                   + mint txb
                   + inject (depositRefunds pp st txb)

produced : PParams → UTxOState → TxBody → Value
produced pp st txb = balance (outs txb)
                   + inject (txfee txb)
                   + inject (newDeposits pp st txb)
                   + inject (txdonation txb)

\end{code}
\caption{Functions used in UTxO rules, continued}
\label{fig:functions:utxo-2}
\end{figure*}

\begin{figure*}[h]
\begin{code}[hide]
open PParams

data _⊢_⇀⦇_,UTXO⦈_ where
\end{code}
\begin{code}
  UTXO-inductive :
    ∀ {Γ} {s} {tx}
    → let slot          = UTxOEnv.slot Γ
          pp            = UTxOEnv.pparams Γ
          utxo          = UTxOState.utxo s
          fees          = UTxOState.fees s
          deposits      = UTxOState.deposits s
          donations     = UTxOState.donations s
      in
    txins tx ≢ ∅                           → txins tx ⊆ dom (utxo ˢ)
    → inInterval slot (txvldt tx)          → minfee pp tx ≤ txfee tx
    → consumed pp s tx ≡ produced pp s tx  → coin (mint tx) ≡ 0
    → txsize tx ≤ maxTxSize pp
    ────────────────────────────────
    Γ ⊢ s ⇀⦇ tx ,UTXO⦈  ⟦ (utxo ∣ txins tx ᶜ) ∪ᵐˡ outs tx
                        , fees + txfee tx
                        , updateDeposits pp tx deposits
                        , donations + txdonation tx
                        ⟧ᵘ
\end{code}
\begin{code}[hide]
-- TODO: This can't be moved into Properties because it breaks. Move
-- this once this is fixed.
unquoteDecl Computational-UTXO = deriveComputational (quote _⊢_⇀⦇_,UTXO⦈_) Computational-UTXO
\end{code}
\caption{UTXO inference rules}
\label{fig:rules:utxo-shelley}
\end{figure*}
