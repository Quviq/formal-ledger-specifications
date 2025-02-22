\section{Ratification}
\label{sec:ratification}
Governance actions are \defn{ratified} through on-chain voting actions.
Different kinds of governance actions have different ratification requirements
but always involve \textit{two of the three} governance bodies, with the exception
of a hard-fork initiation, which requires ratification by all governance bodies.
Depending on the type of governance action, an action will thus be ratified when
a combination of the following occurs:
\begin{itemize}
\item
  the \defn{constitutional committee} (\CC) approves of the action; for this to occur,
  the number of \CC members who vote \yes must meet the \CC vote threshold;
\item
  the \defn{delegation representatives} (\DReps) approve of the action; for this to occur,
  the stake controlled by the \DReps who vote \yes must meet the \DRep vote threshold
  as a percentage of the \defn{total participating voting stake} (\totalStake);
\item
  the stake pool operators (\SPOs) approve of the action; for this to occur,
  the stake controlled by the \SPOs who vote \yes must meet a certain threshold as a percentage of
  the \defn{total registered voting stake} (\totalStake).
\end{itemize}
\textbf{Warning}. Different stake distributions apply to \DReps and \SPOs.
\\[4pt]
A successful motion of no-confidence, election of a new constitutional
committee, a constitutional change, or a hard-fork delays ratification of
all other governance actions until the first epoch after their
enactment. This gives a new constitutional committee enough time to vote
on current proposals, re-evaluate existing proposals with respect to a
new constitution, and ensures that the in principle arbitrary semantic
changes caused by enacting a hard-fork do not have unintended
consequences in combination with other actions.

\subsection{Ratification requirements}
\label{sec:ratification-requirements}
Figure~\ref{fig:ratification-requirements} details the ratification requirements for each
governance action scenario. The columns represent
\begin{itemize}
\item
  \GovAction: the action under consideration;
\item
  \CC: a \ding{51} indicates that the constitutional committee must approve this action;
  a - symbol means that constitutional committee votes do not apply;
\item
  \DRep: the vote threshold that must be met as a percentage of \totalStake;
\item
  \SPO: the vote threshold that must be met as a percentage of the stake held by
  all stake pools; a - symbol means that \SPO votes do not apply.
\end{itemize}
\begin{figure*}[h!]
\begin{longtable}[]{@{}
   >{\raggedright\arraybackslash}p{(\columnwidth - 6\tabcolsep) * \real{0.65}}
  >{\raggedright\arraybackslash}p{(\columnwidth - 6\tabcolsep) * \real{0.11}}
  >{\raggedright\arraybackslash}p{(\columnwidth - 6\tabcolsep) * \real{0.12}}
  >{\raggedright\arraybackslash}p{(\columnwidth - 6\tabcolsep) * \real{0.12}}@{}}
\GovAction  & \CC  &  \DRep & \SPO \\
\hline
\endhead
1. Motion of no-confidence & - & \AgdaField{P1} & \AgdaField{Q1} \\
2a. New committee/threshold (\emph{normal state}) & - & \AgdaField{P2a} & \AgdaField{Q2a} \\
2b. New committee/threshold (\emph{state of no-confidence}) & - & \AgdaField{P2b} & \AgdaField{Q2b} \\
3. Update to the Constitution & \ding{51} & \AgdaField{P3} & - \\
4. Hard-fork initiation & \ding{51} & \AgdaField{P4} & \AgdaField{Q4} \\
5a. Changes to protocol parameters in the \NetworkGroup & \ding{51} & \AgdaField{P5a} & - \\
5b. Changes to protocol parameters in the \EconomicGroup & \ding{51} & \AgdaField{P5b} & - \\
5c. Changes to protocol parameters in the \TechnicalGroup & \ding{51} & \AgdaField{P5c} & - \\
5d. Changes to protocol parameters in the \GovernanceGroup & \ding{51} & \AgdaField{P5d} & - \\
6. Treasury withdrawal & \ding{51} & \AgdaField{P6} & - \\
7. Info & \ding{51} & \(100\) & \(100\) \\
\end{longtable}
\caption{Retification requirements}
\label{fig:ratification-requirements}
\end{figure*}
Each of these thresholds is a governance parameter.  The two thresholds for the \Info
action are set to 100\% since setting it any lower would result in not being able to poll
above the threshold.

\subsection{Ratification restrictions}
\label{sec:ratification-restrictions}
\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Ledger.Transaction

module Ledger.Ratify (txs : TransactionStructure) where

open import Ledger.Prelude hiding (_∧_)

open TransactionStructure txs
open import Ledger.Gov TxId Network ADHash epochStructure ppUpd ppHashingScheme crypto
open import Ledger.PParams epochStructure

import Data.Integer as Z
import Data.Maybe
import Data.Rational as R
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties hiding (_≟_)
open import Data.Nat.Properties.Ext
open import Data.Product using (map₂)

open import Relation.Nullary.Decidable using (⌊_⌋)

infixr 2 _∧_
_∧_ = _×_

instance
  _ = +-0-commutativeMonoid
  _ = +-0-monoid
\end{code}
\begin{figure*}[h!]
{\small
\begin{code}
record StakeDistrs : Set where
  field stakeDistr  : VDeleg ⇀ Coin

record RatifyEnv : Set where
  field stakeDistrs   : StakeDistrs
        currentEpoch  : Epoch
        dreps         : Credential ⇀ Epoch
        ccHotKeys     : KeyHash ⇀ Maybe KeyHash

record RatifyState : Set where
  constructor ⟦_,_,_,_⟧ʳ
  field es              : EnactState
        future          : List (GovActionID × GovActionState)
        removed         : List (GovActionID × GovActionState)
        delay           : Bool

CCData : Set
CCData = Maybe (KeyHash ⇀ Epoch × R.ℚ)
\end{code}
} %% end small
\caption{Types and functions for the RATIFY transition system}
\label{fig:types-and-functions-for-the-ratify-transition-system}
\end{figure*}
As mentioned earlier, each \GovAction must include a \GovActionID
for the most recently enacted action of its given type. Consequently, two actions of the
same type can be enacted at the same time, but they must be \emph{deliberately}
designed to do so.

Figure~\ref{fig:types-and-functions-for-the-ratify-transition-system} defines three more types used in the ratification transition system.
\begin{itemize}
\item \StakeDistrs represents a map relating each voting delegate to an amount of stake;
\item \RatifyEnv denotes an environment with data required for ratification;
\item \RatifyState denotes an enactment state that exists during ratification;
\item \CCData stores data about the constitutional committee.
\end{itemize}
\begin{code}[hide]
-- TODO: remove these or put them into RatifyState
coinThreshold rankThreshold : ℕ
coinThreshold = 1000000000
rankThreshold = 1000

-- DReps with at least `c` coins
mostStakeDRepDist : Credential ⇀ Coin → Coin → Credential ⇀ Coin
mostStakeDRepDist dist c = dist ↾' to-sp (_≥? c)

-- mostStakeDRepDist-homomorphic : ∀ {dist} → Homomorphic₂ _ _ _>_ (_⊆_ on _ˢ) (mostStakeDRepDist dist)
-- mostStakeDRepDist-homomorphic x>y = impl⇒cores⊆ _ _ {!!} --(<-trans x>y)

mostStakeDRepDist-0 : ∀ {dist} → mostStakeDRepDist dist 0 ≡ᵉᵐ dist
mostStakeDRepDist-0 = (proj₂ ∘ Equivalence.from ∈-filter) , λ x → Equivalence.to ∈-filter (z≤n , x)

-- TODO: maybe this can be proven easier with the maximum?
mostStakeDRepDist-∅ : ∀ {dist} → ∃[ N ] mostStakeDRepDist dist N ˢ ≡ᵉ ∅
mostStakeDRepDist-∅ {dist} = suc (Σᵐᵛ[ x ← dist ᶠᵐ ] x) , Properties.∅-least
  (⊥-elim ∘ uncurry helper ∘ Equivalence.from ∈-filter)
  where
    open ≤-Reasoning

    helper : ∀ {k v} → v > Σᵐᵛ[ x ← dist ᶠᵐ ] x → ¬ (k , v) ∈ dist ˢ
    helper {k} {v} v>sum kv∈dist = 1+n≰n $ begin-strict
      v
        ≡˘⟨ indexedSum-singleton' (finiteness ❴ k , v ❵) ⟩
      Σᵐᵛ[ x ← ❴ k , v ❵ᵐ ᶠᵐ ] x
        ≡˘⟨ indexedSumᵐ-cong {x = (dist ∣ ❴ k ❵) ᶠᵐ} {y = ❴ k , v ❵ᵐ ᶠᵐ}
                             (res-singleton' {m = dist} kv∈dist) ⟩
      Σᵐᵛ[ x ← (dist ∣ ❴ k ❵) ᶠᵐ ] x
        ≤⟨ m≤m+n _ _ ⟩
      Σᵐᵛ[ x ← (dist ∣ ❴ k ❵) ᶠᵐ ] x +ℕ Σᵐᵛ[ x ← (dist ∣ ❴ k ❵ ᶜ) ᶠᵐ ] x
        ≡˘⟨ indexedSumᵐ-partition {m = dist ᶠᵐ} {(dist ∣ ❴ k ❵) ᶠᵐ} {(dist ∣ ❴ k ❵ ᶜ) ᶠᵐ}
                                  (res-ex-disj-∪ Properties.Dec-∈-singleton) ⟩
      Σᵐᵛ[ x ← dist ᶠᵐ ] x
        <⟨ v>sum ⟩
      v ∎

∃topNDRepDist : ∀ {n dist} → lengthˢ (dist ˢ) ≥ n → n > 0
                → ∃[ c ] lengthˢ (mostStakeDRepDist dist c ˢ) ≥ n
                       × lengthˢ (mostStakeDRepDist dist (suc c) ˢ) < n
∃topNDRepDist {n} {dist} length≥n n>0 with negInduction (λ _ → _ ≥? n)
  (subst (_≥ n) (sym $ lengthˢ-≡ᵉ _ _ (mostStakeDRepDist-0 {dist})) length≥n)
  (map₂ (λ h h' → ≤⇒≯ (subst (_≥ n) (trans (lengthˢ-≡ᵉ _ _ h) lengthˢ-∅) h') n>0)
                     (mostStakeDRepDist-∅ {dist}))
... | (c , h , h') = c , h , ≰⇒> h'

topNDRepDist : ℕ → Credential ⇀ Coin → Credential ⇀ Coin
topNDRepDist n dist = case (lengthˢ (dist ˢ) ≥? n) ,′ (n >? 0) of λ where
  (_     , no  _)  → ∅ᵐ
  (no _  , yes _)  → dist
  (yes p , yes p₁) → mostStakeDRepDist dist (proj₁ (∃topNDRepDist {dist = dist} p p₁))

-- restrict the DRep stake distribution
-- commented out for now, since we don't know if that'll actually be implemented
restrictedDists : ℕ → ℕ → StakeDistrs → StakeDistrs
restrictedDists coins rank dists = dists -- record dists { drepStakeDistr = restrict drepStakeDistr }
  where open StakeDistrs dists
        -- one always includes the other
        restrict : Credential ⇀ Coin → Credential ⇀ Coin
        restrict dist = topNDRepDist rank dist ∪ᵐˡ mostStakeDRepDist dist coins
\end{code}
\begin{figure*}[h!]
{\small
\begin{code}[hide]
module _
\end{code}
\begin{code}
  -- Module Parameters:
  (Γ      : RatifyEnv)                      -- ratification environment
  (cc     : CCData)                         -- constitutional committee data
  (votes  : (GovRole × Credential) ⇀ Vote)  -- the map relating delegates to their votes
  (ga     : GovAction)                      -- the governance action that was voted on
\end{code}
\begin{code}[hide]
  where

  open RatifyEnv Γ
\end{code}
\begin{code}
  roleVotes : GovRole → (GovRole × Credential) ⇀ Vote
  roleVotes r = filterᵐ (to-sp ((r ≟_) ∘ proj₁ ∘ proj₁)) votes

  actualCCVote : KeyHash → Epoch → Vote
  actualCCVote kh e = case ⌊ currentEpoch ≤ᵉ? e ⌋ ,′ lookupᵐ? ccHotKeys kh ⦃ _ ∈? _ ⦄ of λ where
    (true , just (just hk)) → maybe′ id Vote.no $ lookupᵐ? votes (CC , (inj₁ hk)) ⦃ _ ∈? _ ⦄
    _                       → Vote.abstain -- expired, no hot key or resigned

  actualCCVotes : Credential ⇀ Vote
  actualCCVotes = case cc of λ where
    (just (cc , _)) → mapKeys inj₁ (mapWithKey actualCCVote cc) (λ where _ _ refl → refl)
    nothing         → ∅ᵐ

  actualPDRepVotes : VDeleg ⇀ Vote
  actualPDRepVotes = ❴ abstainRep      , Vote.abstain ❵ᵐ
                 ∪ᵐˡ ❴ noConfidenceRep , (case ga of λ where
                                           NoConfidence → Vote.yes
                                           _            → Vote.no) ❵ᵐ
  actualDRepVotes : VDeleg ⇀ Vote
  actualDRepVotes = mapKeys (uncurry credVoter) (roleVotes GovRole.DRep) (λ where _ _ refl → refl)
                  ∪ᵐˡ constMap (map (credVoter DRep) activeDReps) Vote.no
    where
      activeDReps : ℙ Credential
      activeDReps = dom (filterᵐ (to-sp (currentEpoch ≤ᵉ?_ ∘ proj₂)) dreps ˢ)

  actualVotes : VDeleg ⇀ Vote
  actualVotes = mapKeys (credVoter CC) actualCCVotes (λ where _ _ refl → refl)
              ∪ᵐˡ actualPDRepVotes ∪ᵐˡ actualDRepVotes
              ∪ᵐˡ mapKeys (uncurry credVoter) votes (λ where _ _ refl → refl)
              -- TODO: make `actualVotes` for SPO
\end{code}
} %% end small
\caption{%Ratify i:
Types and proofs for the ratification of governance actions}
\label{fig:defs:ratify-i}
\end{figure*}
The code in Figure~\ref{fig:defs:ratify-i} defines some of the types required for ratification of a governance action.
\begin{itemize}
  \item Assuming a ratification environment \AgdaPostulate{Γ},
  \begin{itemize}
    \item \cc contains constitutional committee data;
    \item \votes is a relation associating each role-credential pair with the vote cast by the individual denoted by that pair;
    \item \ga denotes the governance action being voted upon.
  \end{itemize}

  \item \roleVotes filters the votes based on the given governance role.

  \item \actualCCVote determines how the vote of each \CC member will be counted; specifically, if a \CC member has not yet registered a hot key, has
  \expired, or has resigned, then \actualCCVote returns \abstain;
  if those none of these conditions is met, then
  \begin{itemize}
    \item if the \CC member has voted, then that vote is returned;
    \item if the \CC member has not voted, then the default value of \no is returned.
  \end{itemize}

  \item \actualCCVotes uses \actualCCVote to determine how the votes of all \CC members will be counted.

  \item \actualPDRepVotes determines how the votes will be counted for \DReps;
  here, \abstainRep is mapped to \abstain and \noConfidenceRep is mapped to either \yes or \no,
  depending on the value of \ga.

  \item \actualDRepVotes determines how the votes of \DReps will be counted; \activeDReps that didn't vote count as a \no.

  \item \actualVotes is a partial function relating delegates to the actual vote that will be counted on their behalf;
  it accomplishes this by aggregating the results of \actualCCVotes, \actualPDRepVotes, and \actualDRepVotes.
\end{itemize}
\begin{figure*}[h!]
{\small
\begin{code}
votedHashes : Vote → (VDeleg ⇀ Vote) → GovRole → ℙ VDeleg
votedHashes v votes r = votes ⁻¹ v

votedYesHashes : (VDeleg ⇀ Vote) → GovRole → ℙ VDeleg
votedYesHashes = votedHashes Vote.yes

votedAbstainHashes : (VDeleg ⇀ Vote) → GovRole → ℙ VDeleg
votedAbstainHashes = votedHashes Vote.abstain

participatingHashes : (VDeleg ⇀ Vote) → GovRole → ℙ VDeleg
participatingHashes votes r = votedYesHashes votes r ∪ votedHashes Vote.no votes r

isCC : VDeleg → Bool
isCC (credVoter CC _)  = true
isCC _                 = false

isDRep : VDeleg → Bool
isDRep (credVoter DRep _)  = true
isDRep (credVoter _ _)     = false
isDRep abstainRep          = true
isDRep noConfidenceRep     = true

isSPO : VDeleg → Bool
isSPO (credVoter SPO _)  = true
isSPO _                  = false
\end{code}
} %% end small
\caption{Calculation of the votes as they will be counted}
\label{fig:defs:ratify-ii}
\end{figure*}
\begin{code}[hide]
isCCProp : specProperty λ x → isCC x ≡ true
isCCProp = to-sp (λ x → isCC x ≟ true)

isDRepProp : specProperty λ x → isDRep x ≡ true
isDRepProp = to-sp (λ x → isDRep x ≟ true)

isSPOProp : specProperty λ x → isSPO x ≡ true
isSPOProp = to-sp (λ x → isSPO x ≟ true)
\end{code}
The code in Figure~\ref{fig:defs:ratify-ii} defines \votedHashes, which returns the set of delegates who voted a certain way on the given governance role,
as well as \isCC, \isDRep, and \isSPO, which return \true if the given delegate is a \CC member, a \DRep, or an \SPO (resp.) and \false otherwise.
\begin{figure*}[h!]
{\small
\begin{code}
getStakeDist : GovRole → ℙ VDeleg → StakeDistrs → VDeleg ⇀ Coin
getStakeDist CC    cc  _                             = constMap (filterˢ isCCProp cc) 1
getStakeDist DRep  _   record { stakeDistr = dist }  = filterᵐ (sp-∘ isDRepProp proj₁) dist
getStakeDist SPO   _   record { stakeDistr = dist }  = filterᵐ (sp-∘ isSPOProp proj₁) dist

acceptedStake : GovRole → ℙ VDeleg → StakeDistrs → (VDeleg ⇀ Vote) → Coin
acceptedStake r cc dists votes =
  Σᵐᵛ[ x ← (getStakeDist r cc dists ∣ votedYesHashes votes r) ᶠᵐ ] x

totalStake : GovRole → ℙ VDeleg → StakeDistrs → (VDeleg ⇀ Vote) → Coin
totalStake r cc dists votes = Σᵐᵛ[ x ← getStakeDist r cc dists ∣ votedAbstainHashes votes r ᶜ ᶠᵐ ] x

activeVotingStake : ℙ VDeleg → StakeDistrs → (VDeleg ⇀ Vote) → Coin
activeVotingStake cc dists votes = Σᵐᵛ[ x ← getStakeDist DRep cc dists ∣ dom (votes ˢ) ᶜ ᶠᵐ ] x

-- For now, consider a proposal as accepted if the CC and half of the SPOs
-- and DReps agree.
accepted' : RatifyEnv → EnactState → GovActionState → Set
accepted' Γ es@record { cc = cc , _    ; pparams = pparams , _ }
            s@record  { votes = votes' ; action = action } =
  acceptedBy CC ∧ acceptedBy DRep ∧ acceptedBy SPO ∧ meetsMinAVS
  where
    open RatifyEnv Γ
    open PParams pparams

    votes = actualVotes Γ cc votes' action
    cc' = dom (votes ˢ)
    redStakeDistr = restrictedDists coinThreshold rankThreshold stakeDistrs

    meetsMinAVS : Set
    meetsMinAVS = activeVotingStake cc' redStakeDistr votes ≥ minimumAVS

    acceptedBy : GovRole → Set
    acceptedBy role = let t = threshold pparams (Data.Maybe.map proj₂ cc) action role in
      case totalStake role cc' redStakeDistr votes of λ where
        0          → t ≡ R.0ℚ -- if there's no stake, accept only if threshold is zero
        x@(suc _)  → Z.+ acceptedStake role cc' redStakeDistr votes R./ x R.≥ t

expired : Epoch → GovActionState → Set
expired current record { expiresIn = expiresIn } = expiresIn <ᵉ current
\end{code}
} %% end small
\caption{%%Ratify iii:
Calculation of stake distributions}
\label{fig:defs:ratify-iii}
\end{figure*}
The code in Figure~\ref{fig:defs:ratify-iii} defines yet more types required for ratification of a governance action.
\begin{itemize}
  \item \getStakeDist computes the stake distribution based on the given governance role and the corresponding delegations;
  \item \acceptedStake calculates the sum of stakes for all delegations that voted \yes for the specified role;
  \item \totalStake calculates the sum of stakes for all delegations that didn't vote \abstain for the given role;
  \item \activeVotingStake computes the total stake for the role of \DRep for active voting; it calculates the sum of
  stakes for all active delegates that have not voted (i.e., their delegation is present in \CC but not in the \votes mapping);
  \item \accepted checks if an action is accepted for the \CC, \DRep, and \SPO roles and whether it meets the minimum active voting stake (\meetsMinAVS);
  \item \expired checks whether a governance action is expired in a given epoch.
\end{itemize}
\begin{figure*}[h!]
{\small
\begin{code}
verifyPrev : (a : GovAction) → NeedsHash a → EnactState → Set
verifyPrev NoConfidence          h es = let open EnactState es in h ≡ proj₂ cc
verifyPrev (NewCommittee _ _ _)  h es = let open EnactState es in h ≡ proj₂ cc
verifyPrev (NewConstitution _)   h es = let open EnactState es in h ≡ proj₂ constitution
verifyPrev (TriggerHF _)         h es = let open EnactState es in h ≡ proj₂ pv
verifyPrev (ChangePParams _ _)   h es = let open EnactState es in h ≡ proj₂ pparams
verifyPrev (TreasuryWdrl _)      _ _  = ⊤
verifyPrev Info                  _ _  = ⊤

delayingAction : GovAction → Bool
delayingAction NoConfidence          = true
delayingAction (NewCommittee _ _ _)  = true
delayingAction (NewConstitution _)   = true
delayingAction (TriggerHF _)         = true
delayingAction (ChangePParams _ _)   = false
delayingAction (TreasuryWdrl _)      = false
delayingAction Info                  = false

delayed : (a : GovAction) → NeedsHash a → EnactState → Bool → Set
delayed a h es d = ¬ verifyPrev a h es ⊎ d ≡ true
\end{code}
} %% end small
\caption{%Ratify iv:
Determination of the status of ratification of the governance action}
\label{fig:defs:ratify-iv}
\end{figure*}
The code in Figure~\ref{fig:defs:ratify-iv} defines still more types required for ratification of a governance action.
\begin{itemize}
  \item \verifyPrev takes a governance action, its \NeedsHash, and \EnactState and checks whether the ratification restrictions are met;
  \item \delayingAction takes a governance action and returns \true if it is a ``delaying action'' (\NoConfidence, \NewCommittee, \NewConstitution, \TriggerHF)
  and returns \false otherwise;
  \item \delayed checks whether a given \GovAction is delayed.
\end{itemize}
\begin{code}[hide]
private variable
  Γ : RatifyEnv
  s s' : RatifyState
  es es' : EnactState
  upd : PParamsUpdate
  a : GovActionID × GovActionState
  f f' l removed : List (GovActionID × GovActionState)
  d : Bool

-- having `accepted` abstract speeds up type checking of RATIFY' a lot
abstract
  accepted : RatifyEnv → EnactState → GovActionState → Set
  accepted = accepted'

data _⊢_⇀⦇_,RATIFY'⦈_ : RatifyEnv → RatifyState → GovActionID × GovActionState → RatifyState → Set where

\end{code}
\begin{figure*}[h!]
{\small
\begin{code}
  RATIFY-Accept : let st = proj₂ a; open GovActionState st in
    accepted Γ es st
    → ¬ delayed action prevAction es d
    → ⟦ proj₁ a ⟧ᵉ ⊢ es ⇀⦇ action ,ENACT⦈ es'
    ────────────────────────────────
    Γ ⊢ ⟦ es , f , removed , d ⟧ʳ ⇀⦇ a ,RATIFY'⦈ ⟦ es' , f , a ∷ removed , delayingAction action ⟧ʳ

  -- remove expired actions
  -- NOTE:  We don't have to remove actions that can never be accpted because of
  --        sufficient no votes.

  RATIFY-Reject : let open RatifyEnv Γ; st = proj₂ a in
    ¬ accepted Γ es st
    → expired currentEpoch st
    ────────────────────────────────
    Γ ⊢ ⟦ es , f , removed , d ⟧ʳ ⇀⦇ a ,RATIFY'⦈ ⟦ es , f , a ∷ removed , d ⟧ʳ

  -- Continue voting in the next epoch

  RATIFY-Continue : let open RatifyEnv Γ; st = proj₂ a; open GovActionState st in
    ¬ accepted Γ es st × ¬ expired currentEpoch st ⊎ delayed action prevAction es d
    ────────────────────────────────
    Γ ⊢ ⟦ es , f , removed , d ⟧ʳ ⇀⦇ a ,RATIFY'⦈ ⟦ es , a ∷ f , removed , d ⟧ʳ

_⊢_⇀⦇_,RATIFY⦈_ :  RatifyEnv → RatifyState → List (GovActionID × GovActionState)
                   → RatifyState → Set
_⊢_⇀⦇_,RATIFY⦈_ = SS⇒BS (λ where (Γ , _) → Γ ⊢_⇀⦇_,RATIFY'⦈_)
\end{code}
} %% end small
\caption{The RATIFY transition system}
\label{fig:ratify-transition-system}
\end{figure*}
Figure~\ref{fig:ratify-transition-system} defines three rules, \RATIFYAccept, \RATIFYReject, and \RATIFYContinue, along with the relation \RATIFYsyntax.
The latter is the transition relation for ratification of a \GovAction.  The three rules are briefly described here, followed by more details about how they work.
\begin{itemize}
  \item \RATIFYAccept asserts that the votes for a given \GovAction meets the threshold required for acceptance; the action is accepted and not delayed,
  and \RATIFYAccept ratifies the action.
  \item \RATIFYReject asserts that the given \GovAction is not \accepted and \expired; it removes the governance action.
  \item \RATIFYContinue covers the remaining cases and keeps the \GovAction around for further voting.
\end{itemize}
