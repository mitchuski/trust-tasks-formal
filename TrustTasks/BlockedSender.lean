/-
A blocked sender, against ruling #37 ("a verdict is data", SPEC §8, landed in
trustoverip/dtgwg-trust-tasks-spec#46).

Read at trustoverip/dtgwg-trust-tasks-spec#31, comment of 2026-10-30
(issuecomment-6531047019), which asks #37 for an allowance: in RLTP "a blocked
sender observes what an unblocked one would" (RLTP-DEL-6240 to RLTP-DEL-6260),
so a refusal on account of a block is answered as an accepted document would
be, never with `permissionDenied` or another error; and in RLTP no type
defines a `#response` (RLTP-DEL-3020).

Two kinds of task:

1. A task with no `#response`: the consumer answers a delivered document
   with an acknowledgement that carries no verdict. Answering a block with
   the same acknowledgement makes the block unobservable, keeps the technical
   errors, and produces no outcome evidence (SPEC §4.9.4 check 3) either way,
   so nothing #37 promises is lost (`ack_*`).
2. A task with a `#response`: the success response is a verdict and is
   outcome evidence. Any encoding that answers a block the way it answers
   some verdict either makes that verdict's response something other than
   evidence, against #37, or makes the block's reply evidence of a task that
   did not run (`no_hidden_block_with_response`). The allowance is sound
   exactly for the first kind.

Abstracted: signatures, digests, timing and every other side channel (an
unobservable block in this model means only that the reply is the same),
`details`, and the standard codes other than `malformedRequest`.
-/

namespace TrustTasks.BlockedSender

/-- The consumer's situation. A block is applied only to a document that
validated: an invalid document is refused the same way from any sender. -/
inductive Situation (V : Type)
  | invalid
  | blocked
  | ran (v : V)
  deriving DecidableEq, Repr

/-- Whether the task ran. A blocked document is not acted on. -/
def performed {V : Type} : Situation V → Bool
  | .ran _ => true
  | _ => false

/-! ## A task with no `#response` -/

namespace Ack

/-- Without a `#response`, a task that ran has no verdict to report. -/
abbrev S := Situation Unit

inductive Reply
  | ack
  | malformedRequest
  deriving DecidableEq, Repr

/-- An acknowledgement is not a success response, so not outcome evidence. -/
def isEvidence : Reply → Bool
  | _ => false

/-- RLTP's encoding: a block answered as a delivery is. -/
def rltp : S → Reply
  | .invalid => .malformedRequest
  | .blocked => .ack
  | .ran _ => .ack

/-- The block is unobservable: the blocked sender receives exactly what an
unblocked one does. -/
theorem ack_block_unobservable : rltp .blocked = rltp (.ran ()) := rfl

/-- The technical error is kept: an invalid document is still refused. -/
theorem ack_errors_kept : rltp .invalid = .malformedRequest ∧ rltp .invalid ≠ rltp (.ran ()) :=
  ⟨rfl, by decide⟩

/-- Nothing is evidence, a delivery or a block, so no reader is told a task
ran that did not. -/
theorem ack_no_false_evidence (s : S) : isEvidence (rltp s) = true → performed s = true := by
  intro h; cases h

end Ack

/-! ## A task with a `#response` -/

namespace Resp

inductive Reply (V : Type)
  | response (v : V)
  | malformedRequest
  deriving DecidableEq, Repr

/-- SPEC §4.9.4 check 3: a success response is outcome evidence. -/
def isEvidence {V : Type} : Reply V → Bool
  | .response _ => true
  | .malformedRequest => false

/-- #37 on the task that ran: its reply is outcome evidence. -/
def RulingOnRun {V : Type} (f : Situation V → Reply V) : Prop :=
  ∀ v, isEvidence (f (.ran v)) = true

/-- The allowance asked for, on a task with a `#response`: the block is
answered as some verdict is. -/
def HidesBlock {V : Type} (f : Situation V → Reply V) : Prop :=
  ∃ v, f .blocked = f (.ran v)

/-- No encoding has both: if a block is answered as a verdict is, and that
verdict's reply is evidence as #37 requires, then the blocked sender holds
outcome evidence of a task that did not run. -/
theorem no_hidden_block_with_response {V : Type} (f : Situation V → Reply V)
    (hr : RulingOnRun f) (hb : HidesBlock f) :
    isEvidence (f .blocked) = true ∧ performed (.blocked : Situation V) = false := by
  obtain ⟨v, hv⟩ := hb
  exact ⟨hv ▸ hr v, rfl⟩

inductive V
  | admit
  | refuse
  deriving DecidableEq, Repr

/-- The allowance read literally: a block answered as an accepted document. -/
def blockAsAccepted : Situation V → Reply V
  | .invalid => .malformedRequest
  | .blocked => .response .admit
  | .ran v => .response v

/-- Non-vacuity: the encoding satisfies #37 on every run, hides the block, and
so hands the blocked sender a citable `admit` for a task that never ran. -/
theorem block_as_accepted_counterexample :
    RulingOnRun blockAsAccepted ∧ HidesBlock blockAsAccepted ∧
    blockAsAccepted .blocked = .response .admit ∧
    isEvidence (blockAsAccepted .blocked) = true ∧
    performed (.blocked : Situation V) = false :=
  ⟨fun v => by cases v <;> rfl, ⟨.admit, rfl⟩, rfl, rfl, rfl⟩

end Resp

end TrustTasks.BlockedSender
