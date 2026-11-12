/-
`vtc/member-onboarding/0.1` (upstream trustoverip/dtgwg-trust-tasks-tf main,
2e3149010) against trustoverip/dtgwg-trust-tasks-spec#52.

The ceremony's step descriptions state its intent: `decide` is "Terminal on
rejection — a refused applicant produces a complete, verifiable enactment
that ends here"; `reciprocate` "closes the bidirectional membership edge".
So an enactment should complete on `apply` and either a rejection, or an
approval followed by the reciprocal credential. Its completion predicate is
`allOf[apply, decide, anyOf[decide, reciprocate]]`, read today by presence
(`ceremony.meta.schema.json`, `$defs.Predicate`). `decide`'s success response
carries `decision`: `approved` or `rejected`.

This file shows the predicate reduces to `apply ∧ decide`, so `reciprocate`
is never required and an approved member who never reciprocates completes
exactly as a rejected applicant does; that no presence-only predicate can
state the intent; and that one declared read of `decide`'s `decision`, the
proposal of spec#52 (Ceremony.lean), states it exactly.

Not modelled: optional steps other than `reciprocate`, rounds, ordering,
`maxDuration`, evidence, and the content of any step but `decide`.
-/

namespace TrustTasks.Onboarding

inductive StepName
  | discover
  | apply
  | acknowledge
  | supplement
  | decide
  | solicit
  | ask
  | reciprocate
  deriving DecidableEq, Repr

inductive Decision
  | approved
  | rejected
  deriving DecidableEq, Repr

/-- What a completion check can see: which steps are present, and the
`decision` member of `decide`'s success response, if any. -/
structure Enactment where
  present : StepName → Bool
  decision : Option Decision

/-- Completion predicates: presence atoms, combined by `allOf`/`anyOf`, and
(proposed) a declared read of `decide`'s `decision`. -/
inductive Pred
  | has : StepName → Pred
  | decided : Decision → Pred
  | allOf : Pred → Pred → Pred
  | anyOf : Pred → Pred → Pred

def Pred.eval : Pred → Enactment → Bool
  | .has s, e => e.present s
  | .decided v, e => e.present .decide && e.decision == some v
  | .allOf p q, e => p.eval e && q.eval e
  | .anyOf p q, e => p.eval e || q.eval e

/-- A predicate today's schema can state: presence atoms only. -/
def Pred.presenceOnly : Pred → Bool
  | .has _ => true
  | .decided _ => false
  | .allOf p q => p.presenceOnly && q.presenceOnly
  | .anyOf p q => p.presenceOnly && q.presenceOnly

/-- The ceremony's completion as published. -/
def published : Pred :=
  .allOf (.has .apply) (.allOf (.has .decide) (.anyOf (.has .decide) (.has .reciprocate)))

/-- The intent its step descriptions state. -/
def intended (e : Enactment) : Bool :=
  e.present .apply && e.present .decide &&
    (e.decision == some .rejected ||
      (e.decision == some .approved && e.present .reciprocate))

/-- The published predicate is `apply ∧ decide`: the `anyOf` is absorbed. -/
theorem published_is_apply_and_decide (e : Enactment) :
    published.eval e = (e.present .apply && e.present .decide) := by
  simp only [published, Pred.eval]
  cases e.present .apply <;> cases e.present .decide <;> cases e.present .reciprocate <;> rfl

def steps (l : List StepName) : StepName → Bool := fun s => l.contains s

/-- Approved, credential never reciprocated. -/
def approvedUnreciprocated : Enactment :=
  ⟨steps [.apply, .decide], some .approved⟩

/-- Rejected. -/
def rejected : Enactment := ⟨steps [.apply, .decide], some .rejected⟩

/-- Approved and reciprocated. -/
def approvedReciprocated : Enactment :=
  ⟨steps [.apply, .decide, .solicit, .ask, .reciprocate], some .approved⟩

/-- `reciprocate` is never required: an approved member who never sends the
reciprocal credential completes, as a rejected applicant does, though the
ceremony's intent completes only the second. -/
theorem reciprocate_never_required :
    published.eval approvedUnreciprocated = true ∧ published.eval rejected = true ∧
    intended approvedUnreciprocated = false ∧ intended rejected = true := by
  decide

/-- Presence-only predicates see only which steps are present. -/
theorem presence_only_blind (p : Pred) (hp : p.presenceOnly = true)
    {e1 e2 : Enactment} (h : e1.present = e2.present) : p.eval e1 = p.eval e2 := by
  induction p with
  | has s => simp [Pred.eval, h]
  | decided v => cases hp
  | allOf p q ihp ihq =>
      simp only [Pred.presenceOnly, Bool.and_eq_true] at hp
      simp [Pred.eval, ihp hp.1, ihq hp.2]
  | anyOf p q ihp ihq =>
      simp only [Pred.presenceOnly, Bool.and_eq_true] at hp
      simp [Pred.eval, ihp hp.1, ihq hp.2]

/-- No completion predicate today's schema can state matches the ceremony's
intent: whatever it is, it answers alike for the rejected enactment and the
unreciprocated approval, which the intent tells apart. Moving `reciprocate`
into `allOf` would not help: rejections would then never complete. -/
theorem no_presence_predicate (p : Pred) (hp : p.presenceOnly = true) :
    ∃ e, p.eval e ≠ intended e := by
  have hsame := presence_only_blind p hp (e1 := rejected) (e2 := approvedUnreciprocated) rfl
  cases hr : p.eval rejected
  · exact ⟨rejected, by rw [hr]; decide⟩
  · refine ⟨approvedUnreciprocated, ?_⟩
    rw [← hsame, hr]; decide

/-- With one declared read of `decide`'s `decision` (spec#52's proposal), the
intent is stated exactly. -/
def proposed : Pred :=
  .allOf (.has .apply)
    (.anyOf (.decided .rejected) (.allOf (.decided .approved) (.has .reciprocate)))

theorem proposed_is_intended (e : Enactment) : proposed.eval e = intended e := by
  rcases e with ⟨pr, d⟩
  simp only [proposed, intended, Pred.eval]
  cases pr .apply <;> cases pr .decide <;> cases pr .reciprocate <;>
    rcases d with _ | _ | _ <;> rfl

theorem proposed_nonvacuous :
    proposed.eval rejected = true ∧ proposed.eval approvedReciprocated = true ∧
    proposed.eval approvedUnreciprocated = false := by
  decide

end TrustTasks.Onboarding
