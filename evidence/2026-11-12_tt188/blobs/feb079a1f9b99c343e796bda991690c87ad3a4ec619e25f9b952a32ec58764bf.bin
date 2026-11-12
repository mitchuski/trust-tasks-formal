/-
The MyTerms roster as published at agreements.info, read against the
`understanding/seal` rules on trustoverip/dtgwg-trust-tasks-tf#904
(head 83af40f).

Data: the machine-readable JSON of each relationship agreement
(`agreements.info/r/<code>/<hash>.json`, all `version` 1.1), read
2026-11-12. Each agreement is reduced to its code and its `purposes` list;
the five agreements of the SD-BASE line are, by `purposes`,
SD-BASE ⊂ SD-BASE-A ⊂ SD-BASE-AT ⊂ SD-BASE-ATP ⊂ SD-BASE-ATP3.

Rules taken from #904 head, `specs/understanding/seal/0.1/spec.md`: the
seal is grounded in a passed `understanding/exchange`; the host decides
`accepted`, `countered` (one `counterAgreement` from the same roster) or
`refused`; a countered proposal may be answered by one follow-up
re-proposing the countered terms, and that follow-up is not countered
again. The spec says itself that "a counter may name different roster items
than the ones an `understanding/exchange` tested" and that it "does not
require a fresh exchange before a follow-up". This file makes that gap
concrete on the published roster and proves a completion rule that closes
it without a second exchange.

Not modelled: signatures, digests, issuer binding and round limits (see
MyTerms.lean and Ceremony.lean), prohibitions as distinct from absent
purposes, and what an exchange's questions are.
-/

namespace TrustTasks.Roster

/-- Values of `agreement.purposes` in the published JSON. `serviceAnalytics`
is the newer vocabulary used by the `-DP` and `-S3P` documents. -/
inductive Purpose
  | serviceDelivery
  | analytics
  | serviceAnalytics
  | tracking
  | profiling
  | thirdPartySharing
  deriving DecidableEq, Repr

structure Agreement where
  /-- The JSON `id` member. -/
  code : String
  purposes : List Purpose
  deriving DecidableEq, Repr

def sdBase : Agreement := ⟨"SD-BASE", [.serviceDelivery]⟩
def sdBaseA : Agreement := ⟨"SD-BASE-A", [.serviceDelivery, .analytics]⟩
def sdBaseAT : Agreement := ⟨"SD-BASE-AT", [.serviceDelivery, .analytics, .tracking]⟩
def sdBaseATP : Agreement :=
  ⟨"SD-BASE-ATP", [.serviceDelivery, .analytics, .tracking, .profiling]⟩
def sdBaseATP3 : Agreement :=
  ⟨"SD-BASE-ATP3", [.serviceDelivery, .analytics, .tracking, .profiling, .thirdPartySharing]⟩

/-- The relationship roster, SD-BASE line. -/
def roster : List Agreement := [sdBase, sdBaseA, sdBaseAT, sdBaseATP, sdBaseATP3]

/-- `b` permits nothing `a` does not. -/
def Covers (a b : Agreement) : Prop := ∀ p, p ∈ b.purposes → p ∈ a.purposes

instance (a b : Agreement) : Decidable (Covers a b) :=
  inferInstanceAs (Decidable (∀ p, p ∈ b.purposes → p ∈ a.purposes))

inductive Decision
  | accepted
  | countered
  | refused
  deriving DecidableEq, Repr

/-- One sealing engagement. `tested` is the agreement the grounding exchange
examined; `proposed` the seal request's agreement; `counter` the host's
`counterAgreement`; `followup` the decision on the one follow-up, if sent. -/
structure Engagement where
  tested : Agreement
  proposed : Agreement
  decision : Decision
  counter : Option Agreement
  followup : Option Decision
  deriving DecidableEq, Repr

/-- The rules of #904 head that this file reads. The exchange tested the
terms first proposed; `counterAgreement` is present exactly with
`countered` and comes from the roster; a follow-up exists only after a
counter, takes the counter, and is not itself countered. -/
def Adm (R : List Agreement) (e : Engagement) : Prop :=
  e.proposed ∈ R ∧ e.tested = e.proposed ∧
  (e.decision = .countered ↔ e.counter.isSome) ∧
  (∀ c, e.counter = some c → c ∈ R) ∧
  (e.followup.isSome → e.decision = .countered) ∧
  e.followup ≠ some .countered

/-- The agreement sealed, if any: the proposal on `accepted`, the counter on
an accepted follow-up. -/
def sealed (e : Engagement) : Option Agreement :=
  match e.decision, e.counter, e.followup with
  | .accepted, _, _ => some e.proposed
  | .countered, some c, some .accepted => some c
  | _, _, _ => none

/-- What #904 head lets a relying party conclude: something from the roster
was sealed (completion reading `decision`, Ceremony.lean). -/
def completesHead (e : Engagement) : Prop := (sealed e).isSome

/-- Under #904's rules, what is sealed is in the roster. -/
theorem sealed_in_roster {R : List Agreement} {e : Engagement} (hA : Adm R e)
    {a : Agreement} (hs : sealed e = some a) : a ∈ R := by
  obtain ⟨hp, _, _, hc, _, _⟩ := hA
  rcases e with ⟨t, p, d, c, f⟩
  cases d with
  | accepted => simp only [sealed] at hs; cases hs; exact hp
  | refused => simp [sealed] at hs
  | countered =>
      cases c with
      | none => simp [sealed] at hs
      | some c =>
          cases f with
          | none => simp [sealed] at hs
          | some f =>
              cases f with
              | accepted => simp only [sealed] at hs; cases hs; exact hc _ rfl
              | countered => simp [sealed] at hs
              | refused => simp [sealed] at hs

/-- The individual is tested on SD-BASE, proposes it, the host counters with
SD-BASE-ATP3, the individual's follow-up is accepted. -/
def broadCounter : Engagement :=
  { tested := sdBase, proposed := sdBase, decision := .countered,
    counter := some sdBaseATP3, followup := some .accepted }

/-- On the published roster the engagement is admissible and complete, and the
sealed agreement permits third-party sharing, tracking and profiling, none
of which the tested agreement permits: the exchange said nothing about the
terms that bind. -/
theorem counter_escapes_exchange :
    Adm roster broadCounter ∧ completesHead broadCounter ∧
    sealed broadCounter = some sdBaseATP3 ∧
    .thirdPartySharing ∈ sdBaseATP3.purposes ∧ .thirdPartySharing ∉ sdBase.purposes ∧
    .tracking ∉ sdBase.purposes ∧ .profiling ∉ sdBase.purposes := by
  refine ⟨⟨by decide, rfl, by decide, ?_, by decide, by decide⟩, rfl, rfl,
    by decide, by decide, by decide, by decide⟩
  intro c h; cases h; decide

/-! ### The fix: completion checks that the exchange covered the sealed terms -/

/-- Complete when an agreement is sealed and the tested agreement permits
everything it does. Needs no second exchange when the counter is narrower. -/
def completesCovered (e : Engagement) : Prop :=
  ∃ a, sealed e = some a ∧ Covers e.tested a

/-- Completion gives a roster agreement every one of whose purposes the
individual was tested on. -/
theorem covered_sound {R : List Agreement} {e : Engagement} (hA : Adm R e)
    (hc : completesCovered e) :
    ∃ a, sealed e = some a ∧ a ∈ R ∧ ∀ p, p ∈ a.purposes → p ∈ e.tested.purposes := by
  obtain ⟨a, hs, hcov⟩ := hc
  exact ⟨a, hs, sealed_in_roster hA hs, hcov⟩

theorem covered_refuses_broad_counter : ¬ completesCovered broadCounter := by
  rintro ⟨a, hs, hcov⟩
  cases hs
  exact absurd (hcov .thirdPartySharing (by decide)) (by decide)

/-- The rule is not vacuous and does not forbid counters: tested and proposed
on SD-BASE-ATP, countered with SD-BASE-A, accepted, complete. -/
def narrowCounter : Engagement :=
  { tested := sdBaseATP, proposed := sdBaseATP, decision := .countered,
    counter := some sdBaseA, followup := some .accepted }

theorem covered_admits_narrow_counter :
    Adm roster narrowCounter ∧ completesCovered narrowCounter := by
  refine ⟨⟨by decide, rfl, by decide, ?_, by decide, by decide⟩, sdBaseA, rfl, by decide⟩
  intro c h; cases h; decide

/-- A direct acceptance always passes: the tested terms are the sealed ones. -/
theorem covered_on_accept {R : List Agreement} {e : Engagement} (hA : Adm R e)
    (hd : e.decision = .accepted) : completesCovered e := by
  obtain ⟨_, ht, _⟩ := hA
  refine ⟨e.proposed, ?_, ?_⟩
  · unfold sealed; rw [hd]
  · intro p hp; rw [ht]; exact hp

/-! ### The published codes are not unique -/

/-- `agreements.info/r/sd-base-dp`: its JSON `id` is "SD-BASE" (as are the
JSON of sd-base-a-dp, sd-base-at-dp, sd-base-atp-dp, sd-base-atp-s3p and
sd-base-atp-s3p-dp), with purposes `service-analytics`, `service-delivery`. -/
def sdBaseDp : Agreement := ⟨"SD-BASE", [.serviceAnalytics, .serviceDelivery]⟩

/-- Two published agreements carry the same code and permit different
purposes: a seal or contract that names its agreement by the JSON `id` does
not determine what was agreed. The agreement must be named by something
unique to the document (its `agreementId`, or a digest of it). -/
theorem code_not_unique :
    sdBase.code = sdBaseDp.code ∧ sdBase ≠ sdBaseDp ∧
    .serviceAnalytics ∈ sdBaseDp.purposes ∧ .serviceAnalytics ∉ sdBase.purposes := by
  decide

end TrustTasks.Roster
