/-
Small models of four rulings requested on trustoverip/dtgwg-trust-tasks-spec#31
and decided on their own issues:

1. #36: a hold for approval, consent or step-up is a next step (SPEC §8.6,
   "A hold is a next step", landed in #45).
2. #37: a verdict is data; `permissionDenied` is a refusal to run (SPEC §8,
   "A decision is not a failure", landed in #46).
3. #38: "already in that state": a setting operation succeeds idempotently,
   a duplicate create and a missing target are errors (SPEC §7.2, "A target
   already in the requested state", landed in #47).
4. #39: shared schemas never default a governance value (SPEC §6.6 rule 5,
   "No governance defaults", landed in #48).

Each section has a model, the theorem that captures the ruling, and a
counterexample under the alternative the ruling rejected. Each model is a
deliberately small abstraction; what it leaves out is stated at the top of
its section.
-/

import TrustTasks.MyTerms

namespace TrustTasks.Rulings

open TrustTasks.MyTerms (Party)

/-- Point update of a function on indices. -/
def upd {α : Type} (f : Nat → α) (d : Nat) (v : α) : Nat → α :=
  fun x => if x = d then v else f x

/-! ## Ruling 1 (#36): a hold is a next step

One producer wants one operation run once. It sends a request; the consumer
holds it until a third party approves or declines, then runs it (and answers
with a success response) or refuses it (and answers with an error). The only
thing that varies between the ruling and the alternative is the reply the
consumer sends when it puts a request on hold: `nextStep` (the ruling) or an
error whose code or `details` says the task is held (the alternative).

The producer follows the framework's reading of each reply: an error closes
the exchange and says the task was not performed (SPEC §4.12, §8), so a
producer that still wants the outcome issues a new request, which is a new
document with a new `id`; a next step leaves the exchange open, so it waits.

Abstracted: the approver (an approval or decline simply happens to a held
request), `expects` and `continuation: resubmit`, timing and the acceptance
window, an abandoned hold, transport loss, and the decline being answered
"when the producer next asks" (here it is answered at once). Consumer
Requirements item 11 is not in play: the reissue is a different document, so
the duplicate-execution record does not catch it.
-/

namespace Hold

inductive Reply
  | response
  | error
  | nextStep
  deriving DecidableEq, Repr

/-- The consumer's state for one request document. -/
inductive St
  | unsent
  | pending
  | held
  | done
  | refused
  deriving DecidableEq, Repr

/-- Documents are numbered `0 … n-1` in the order the producer sent them.
`seen d` is the last reply the producer holds for document `d`; `perf` counts
how many times the operation has run. -/
structure Cfg where
  n : Nat
  st : Nat → St
  seen : Nat → Option Reply
  perf : Nat

def init : Cfg := { n := 0, st := fun _ => .unsent, seen := fun _ => none, perf := 0 }

/-- One step of the system. `hr` is the reply the consumer gives a hold. -/
inductive Step (hr : Reply) : Cfg → Cfg → Prop
  /-- The producer sends a (new) request once every earlier one was closed
  by an error. -/
  | submit {c : Cfg} : (∀ d, d < c.n → c.seen d = some .error) →
      Step hr c { c with n := c.n + 1, st := upd c.st c.n .pending }
  /-- The consumer understands the request and holds it. -/
  | hold {c : Cfg} {d : Nat} : c.st d = .pending →
      Step hr c { c with st := upd c.st d .held, seen := upd c.seen d (some hr) }
  /-- The awaited act happens: the consumer runs the operation and answers. -/
  | approve {c : Cfg} {d : Nat} : c.st d = .held →
      Step hr c { c with st := upd c.st d .done, seen := upd c.seen d (some .response),
                         perf := c.perf + 1 }
  /-- The awaited act is declined: a refusal to run (`permissionDenied`). -/
  | decline {c : Cfg} {d : Nat} : c.st d = .held →
      Step hr c { c with st := upd c.st d .refused, seen := upd c.seen d (some .error) }

inductive Reach (hr : Reply) : Cfg → Prop
  | init : Reach hr init
  | step {c c' : Cfg} : Reach hr c → Step hr c c' → Reach hr c'

/-- The invariant under the ruling. -/
def Inv (c : Cfg) : Prop :=
  (∀ d, c.seen d = some .error → c.st d = .refused) ∧
  (∀ d, d + 1 < c.n → c.seen d = some .error) ∧
  (∀ d, c.n ≤ d → c.st d = .unsent) ∧
  (c.perf = 0 ∨ (c.perf = 1 ∧ 0 < c.n ∧ c.st (c.n - 1) = .done))

theorem inv_init : Inv init := by
  refine ⟨?_, ?_, ?_, Or.inl rfl⟩
  · intro d h; simp [init] at h
  · intro d h; simp [init] at h
  · intro d _; rfl

theorem inv_step {c c' : Cfg} (hI : Inv c) (hs : Step .nextStep c c') : Inv c' := by
  obtain ⟨i1, i2, i3, i4⟩ := hI
  -- a document in any state other than `unsent` was sent
  have sent : ∀ d, c.st d ≠ .unsent → d < c.n := by
    intro d hd
    false_or_by_contra
    exact hd (i3 d (by omega))
  -- only the last document sent can be open
  have last : ∀ d, c.st d ≠ .unsent → c.st d ≠ .refused → d = c.n - 1 := by
    intro d hu hr
    have := sent d hu
    false_or_by_contra
    exact hr (i1 d (i2 d (by omega)))
  cases hs with
  | @submit hall =>
      unfold Inv; dsimp only
      have hp : c.perf = 0 := by
        rcases i4 with h | ⟨_, hn, hd⟩
        · exact h
        · have := i1 (c.n - 1) (hall (c.n - 1) (by omega))
          rw [hd] at this; cases this
      refine ⟨?_, ?_, ?_, Or.inl hp⟩
      · intro d h
        simp only [upd]
        split
        · subst_vars
          have := i1 _ h
          rw [i3 c.n (Nat.le_refl _)] at this; cases this
        · exact i1 d h
      · intro d hd
        exact hall d (by simp at hd; omega)
      · intro d hd
        simp only [upd] at hd ⊢
        split
        · omega
        · exact i3 d (by omega)
  | @hold d hp =>
      unfold Inv; dsimp only
      have hl := last d (by rw [hp]; decide) (by rw [hp]; decide)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x h
        simp only [upd] at h ⊢
        split at h
        · cases h
        · rw [if_neg (by assumption)]; exact i1 x h
      · intro x hx
        simp only [upd]
        rw [if_neg (by omega)]
        exact i2 x hx
      · intro x hx
        simp only [upd]
        rw [if_neg (by have := sent d (by rw [hp]; decide); omega)]
        exact i3 x hx
      · rcases i4 with h | ⟨h1, h2, h3⟩
        · exact Or.inl h
        · subst hl; rw [h3] at hp; cases hp
  | @approve d hh =>
      unfold Inv; dsimp only
      have hl := last d (by rw [hh]; decide) (by rw [hh]; decide)
      have hd := sent d (by rw [hh]; decide)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x h
        simp only [upd] at h ⊢
        split at h
        · cases h
        · rw [if_neg (by assumption)]; exact i1 x h
      · intro x hx
        simp only [upd]
        rw [if_neg (by omega)]
        exact i2 x hx
      · intro x hx
        simp only [upd]
        rw [if_neg (by omega)]
        exact i3 x hx
      · rcases i4 with h | ⟨_, _, h3⟩
        · refine Or.inr ⟨by simp [h], by omega, ?_⟩
          simp only [upd]
          rw [if_pos (by omega)]
        · subst hl; rw [h3] at hh; cases hh
  | @decline d hh =>
      unfold Inv; dsimp only
      have hl := last d (by rw [hh]; decide) (by rw [hh]; decide)
      have hd := sent d (by rw [hh]; decide)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x h
        simp only [upd] at h ⊢
        split
        · rfl
        · rw [if_neg (by assumption)] at h; exact i1 x h
      · intro x hx
        simp only [upd]
        rw [if_neg (by omega)]
        exact i2 x hx
      · intro x hx
        simp only [upd]
        rw [if_neg (by omega)]
        exact i3 x hx
      · rcases i4 with h | ⟨h1, h2, h3⟩
        · exact Or.inl h
        · subst hl; rw [h3] at hh; cases hh

theorem inv_reach {c : Cfg} (h : Reach .nextStep c) : Inv c := by
  induction h with
  | init => exact inv_init
  | step _ hs ih => exact inv_step ih hs

/-- The ruling: when a hold is answered with a next step, the operation runs
at most once however many requests the producer sends, and an error the
producer holds always means the request was refused and will not run. -/
theorem hold_next_step_sound {c : Cfg} (h : Reach .nextStep c) :
    c.perf ≤ 1 ∧ ∀ d, c.seen d = some .error → c.st d = .refused := by
  obtain ⟨i1, _, _, i4⟩ := inv_reach h
  refine ⟨?_, i1⟩
  rcases i4 with h | ⟨h, _⟩ <;> omega

/-- Non-vacuity: under the ruling, a held request is approved, runs, and the
producer holds its success response. -/
theorem hold_next_step_nonvacuous :
    ∃ c, Reach .nextStep c ∧ c.perf = 1 ∧ c.seen 0 = some .response := by
  have h1 := Reach.step (hr := .nextStep) Reach.init
    (Step.submit (c := init) (by intro d hd; simp [init] at hd))
  have h2 := Reach.step h1 (Step.hold (d := 0) rfl)
  have h3 := Reach.step h2 (Step.approve (d := 0) rfl)
  exact ⟨_, h3, rfl, rfl⟩

/-- The alternative: when a hold is answered with an error, the producer reads
a closed exchange and reissues; both the original (still held) and the
reissue are approved, and the operation runs twice. Along the way the
producer holds an error for a request the consumer is still holding. -/
theorem hold_as_error_runs_twice :
    (∃ c, Reach .error c ∧ c.seen 0 = some .error ∧ c.st 0 = .held ∧ c.n = 2) ∧
    (∃ c, Reach .error c ∧ c.perf = 2) := by
  have h1 := Reach.step (hr := .error) Reach.init
    (Step.submit (c := init) (by intro d hd; simp [init] at hd))
  have h2 := Reach.step h1 (Step.hold (d := 0) rfl)
  have h3 := Reach.step h2 (Step.submit (by
    intro d hd
    have : d = 0 := by simp [init] at hd; omega
    subst this; rfl))
  have h4 := Reach.step h3 (Step.hold (d := 1) rfl)
  have h5 := Reach.step h4 (Step.approve (d := 0) rfl)
  have h6 := Reach.step h5 (Step.approve (d := 1) rfl)
  exact ⟨⟨_, h3, rfl, rfl, rfl⟩, ⟨_, h6, rfl⟩⟩

end Hold

/-! ## Ruling 2 (#37): a verdict is data; `permissionDenied` is a refusal to run

A task that exists to produce a decision, such as a join request. The
situation at the consumer is one of: the document did not validate, the
requester may not invoke the task, or the task ran and produced a verdict.
An encoding maps each situation to a reply. A reader that knows the task's
success schema and the standard error codes, but not task-specific codes,
reads a reply back. Outcome evidence (SPEC §4.9.4 check 3) is a success
response.

Abstracted: signatures, digests, the content of a verdict beyond its value,
`details`, and the other standard codes. `notAuthorized` covers both "may not
invoke" (SPEC §8.3) and a hold whose awaited act was declined (§8.6), since
the framework answers both with `permissionDenied`.
-/

namespace Verdict

inductive V
  | admit
  | refuse
  | refer
  deriving DecidableEq, Repr

inductive Situation
  | invalid
  | notAuthorized
  | decided (v : V)
  deriving DecidableEq, Repr

inductive Code
  | malformedRequest
  | permissionDenied
  /-- A task-specific code, e.g. `policyRefused`. -/
  | ext (n : Nat)
  deriving DecidableEq, Repr

inductive Reply
  | response (v : V)
  | error (c : Code)
  deriving DecidableEq, Repr

/-- Whether the task ran. -/
def performed : Situation → Bool
  | .decided _ => true
  | _ => false

/-- SPEC §4.9.4 check 3: only a success response is outcome evidence. -/
def isEvidence : Reply → Bool
  | .response _ => true
  | .error _ => false

/-- The ruling's encoding. -/
def ruling : Situation → Reply
  | .invalid => .error .malformedRequest
  | .notAuthorized => .error .permissionDenied
  | .decided v => .response v

/-- A reader that knows the success schema and the standard codes. An
unrecognized task-specific code reads as "not performed, reason unknown". -/
def readStd : Reply → Option Situation
  | .response v => some (.decided v)
  | .error .malformedRequest => some .invalid
  | .error .permissionDenied => some .notAuthorized
  | .error (.ext _) => none

/-- The ruling: a reader recovers every situation exactly, and a reply is
outcome evidence exactly when the task ran, a refusal included. -/
theorem verdict_as_data_sound (s : Situation) :
    readStd (ruling s) = some s ∧ isEvidence (ruling s) = performed s := by
  cases s <;> exact ⟨rfl, rfl⟩

/-- Non-vacuity: a refusal is read back as a refusal and is citable. -/
theorem verdict_as_data_nonvacuous :
    ruling (.decided .refuse) = .response .refuse ∧
    readStd (ruling (.decided .refuse)) = some (.decided .refuse) ∧
    isEvidence (ruling (.decided .refuse)) = true :=
  ⟨rfl, rfl, rfl⟩

/-- No reader inverts an encoding that sends two situations to one reply. -/
theorem no_reader_of_collision {f : Situation → Reply} {a b : Situation}
    (hab : a ≠ b) (hf : f a = f b) :
    ¬ ∃ read : Reply → Option Situation, ∀ s, read (f s) = some s := by
  rintro ⟨read, hr⟩
  have ha := hr a
  rw [hf, hr b] at ha
  exact hab (Option.some.inj ha).symm

/-- Alternative A: a negative verdict reported as `permissionDenied`. -/
def refusalAsDenied : Situation → Reply
  | .decided .refuse => .error .permissionDenied
  | s => ruling s

/-- Under A, "may not ask" and "asked, and the answer is no" are the same
reply, so no reader can tell them apart, and the refusal is not evidence. -/
theorem refusal_as_denied_conflates :
    refusalAsDenied .notAuthorized = refusalAsDenied (.decided .refuse) ∧
    (¬ ∃ read : Reply → Option Situation, ∀ s, read (refusalAsDenied s) = some s) ∧
    isEvidence (refusalAsDenied (.decided .refuse)) = false :=
  ⟨rfl, no_reader_of_collision (a := .notAuthorized) (b := .decided .refuse) (by decide) rfl, rfl⟩

/-- Alternative B: a negative verdict reported as a task-specific error code. -/
def refusalAsCode : Situation → Reply
  | .decided .refuse => .error (.ext 0)
  | s => ruling s

/-- Under B the encoding is injective, but a reader that does not recognize the
code reads a task that ran as one that did not, and the refusal still is not
outcome evidence. -/
theorem refusal_as_code_misread :
    performed (.decided .refuse) = true ∧
    readStd (refusalAsCode (.decided .refuse)) = none ∧
    isEvidence (refusalAsCode (.decided .refuse)) = false :=
  ⟨rfl, rfl, rfl⟩

/-- Alternative C, the other direction: a refusal to run reported as a negative
verdict. A requester that may not ask obtains a citable "refused" decision
indistinguishable from an evaluated one. -/
def denialAsVerdict : Situation → Reply
  | .notAuthorized => .response .refuse
  | s => ruling s

theorem denial_as_verdict_conflates :
    denialAsVerdict .notAuthorized = denialAsVerdict (.decided .refuse) ∧
    performed .notAuthorized = false ∧
    isEvidence (denialAsVerdict .notAuthorized) = true ∧
    (¬ ∃ read : Reply → Option Situation, ∀ s, read (denialAsVerdict s) = some s) :=
  ⟨rfl, rfl, rfl, no_reader_of_collision (a := .notAuthorized) (b := .decided .refuse) (by decide) rfl⟩

end Verdict

/-! ## Ruling 3 (#38): already in that state

A store maps target identifiers to a state value, or to nothing where no
target exists. A setting operation (revoke, disable, set) names an existing
target and a state; a creating operation (register, grant) names a new
target. The specification declares which kind each operation is; the model
takes that classification as given.

Abstracted: authorization, visibility (the ruling's MAY on answering an
invisible target as missing), concurrency and replicated stores, any effect
other than the stored state, and what makes two requests name "the same"
target (here: the same key).
-/

namespace AlreadyInState

abbrev Key := Nat
abbrev Store := Key → Option Nat

inductive Out
  | ok (changed : Bool)
  | alreadyExists
  | alreadyInState
  | notFound
  deriving DecidableEq, Repr

def Out.isOk : Out → Bool
  | .ok _ => true
  | _ => false

/-- The ruling's setting operation. -/
def set (σ : Store) (k : Key) (v : Nat) : Out × Store :=
  match σ k with
  | none => (.notFound, σ)
  | some w => (.ok (w != v), upd σ k (some v))

/-- The ruling's creating operation. -/
def create (σ : Store) (k : Key) (v : Nat) : Out × Store :=
  match σ k with
  | some _ => (.alreadyExists, σ)
  | none => (.ok true, upd σ k (some v))

theorem upd_self (σ : Store) (k : Key) (v : Option Nat) (h : σ k = v) : upd σ k v = σ := by
  funext x
  simp only [upd]
  split
  · next hx => rw [hx, h]
  · rfl

/-- Setting is idempotent: a second identical request leaves the store as the
first left it and succeeds, reporting no change. -/
theorem set_idempotent (σ : Store) (k : Key) (v : Nat) :
    (set (set σ k v).2 k v).2 = (set σ k v).2 ∧
    (σ k ≠ none → (set (set σ k v).2 k v).1 = .ok false) := by
  unfold set
  cases h : σ k with
  | none => simp [h]
  | some w =>
      have hk : upd σ k (some v) k = some v := by simp [upd]
      simp only [hk, bne_self_eq_false]
      exact ⟨upd_self _ _ _ hk, fun _ => trivial⟩

/-- A set succeeds exactly when the target exists, and afterwards the target
is in the requested state. -/
theorem set_ok_iff_exists (σ : Store) (k : Key) (v : Nat) :
    ((set σ k v).1.isOk = true ↔ σ k ≠ none) ∧
    ((set σ k v).1.isOk = true → (set σ k v).2 k = some v) := by
  unfold set
  cases h : σ k with
  | none => simp [Out.isOk]
  | some w => simp [Out.isOk, upd]

/-- A create succeeds exactly when the target did not exist: a success means
this request created it. -/
theorem create_ok_iff_created (σ : Store) (k : Key) (v : Nat) :
    ((create σ k v).1.isOk = true ↔ σ k = none) ∧
    ((create σ k v).1.isOk = true → (create σ k v).2 k = some v) := by
  unfold create
  cases h : σ k with
  | none => simp [Out.isOk, upd]
  | some w => simp [Out.isOk]

/-- Non-vacuity: from an empty store, create then set then set again: every
reply is a success and the last reports no change. -/
theorem already_in_state_nonvacuous :
    let σ0 : Store := fun _ => none
    let σ1 := (create σ0 1 5).2
    let σ2 := (set σ1 1 6).2
    (create σ0 1 5).1 = .ok true ∧ (set σ1 1 6).1 = .ok true ∧
    (set σ2 1 6).1 = .ok false ∧ (create σ1 1 7).1 = .alreadyExists := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide

/-- Retry while the reply is not a success, at most `n` more times. -/
def retry (op : Store → Out × Store) : Nat → Store → Out × Store
  | 0, σ => op σ
  | n + 1, σ =>
      let r := op σ
      if r.1.isOk then r else retry op n r.2

/-- Alternative A: a setting operation that refuses a state that already holds
(`alreadyRevoked`). -/
def setStrict (σ : Store) (k : Key) (v : Nat) : Out × Store :=
  match σ k with
  | none => (.notFound, σ)
  | some w => if w = v then (.alreadyInState, σ) else (.ok true, upd σ k (some v))

/-- Under A, a producer that retries until success never gets one when the
state already holds, however many times it retries; under the ruling the
first request succeeds. -/
theorem set_strict_retry_loop (σ : Store) (k : Key) (v : Nat) (h : σ k = some v) :
    (∀ n, retry (fun s => setStrict s k v) n σ = (.alreadyInState, σ)) ∧
    (set σ k v).1 = .ok false := by
  have hs : setStrict σ k v = (.alreadyInState, σ) := by simp [setStrict, h]
  refine ⟨fun n => ?_, by simp [set, h]⟩
  induction n with
  | zero => exact hs
  | succ n ih => simp only [retry, hs, Out.isOk]; exact ih

/-- Alternative B: a creating operation that succeeds on a duplicate. -/
def createLax (σ : Store) (k : Key) (v : Nat) : Out × Store :=
  match σ k with
  | some _ => (.ok false, σ)
  | none => (.ok true, upd σ k (some v))

/-- Under B, a second requester asking to create target 1 with value 2 is told
it succeeded, while target 1 is the first requester's, with value 1. Under
the ruling the same request is refused. -/
theorem create_lax_misleads :
    let σ1 := (createLax (fun _ => none) 1 1).2
    (createLax σ1 1 2).1.isOk = true ∧ (createLax σ1 1 2).2 1 = some 1 ∧
    (create σ1 1 2).1 = .alreadyExists := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

/-- Alternative C: a setting operation that succeeds on a missing target. -/
def setUpsert (σ : Store) (k : Key) (v : Nat) : Out × Store :=
  match σ k with
  | none => (.ok true, upd σ k (some v))
  | some w => (.ok (w != v), upd σ k (some v))

/-- Under C, setting a target that never existed succeeds and brings it into
being (a revoke of a key never registered records a revoked key). Under the
ruling it is `notFound`. -/
theorem set_upsert_phantom :
    let σ0 : Store := fun _ => none
    σ0 1 = none ∧ (setUpsert σ0 1 3).1.isOk = true ∧ (setUpsert σ0 1 3).2 1 = some 3 ∧
    (set σ0 1 3).1 = .notFound := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  decide

end AlreadyInState

/-! ## Ruling 4 (#39): no governance defaults in shared schemas

The `requireConsent` constraint of `policy/_shared` carries `minApprovals`
and `excludeRequester`. A community's governance framework fixes both. The
producer fills the wire members from its policy engine, which may supply a
value or nothing; it never supplies a wrong value (`Honest`). The consumer
computes the effective constraint: under the ruling an omitted member is
`malformedRequest`; under the alternative the schema's default fills it.
An approval passes when the counted approvers reach the threshold.

Abstracted: the approval protocol itself, approver identity and
authentication, duplicate approvers (the list is taken as distinct), TTLs,
roles and evaluation order (the ruling covers them; the model has two
members), and how the governance value reaches the producer.
-/

namespace Defaults

structure Gov where
  minApprovals : Nat
  excludeRequester : Bool
  deriving DecidableEq, Repr

structure Wire where
  minApprovals : Option Nat
  excludeRequester : Option Bool
  deriving DecidableEq, Repr

inductive Schema
  | required
  | defaulted (d : Gov)
  deriving DecidableEq, Repr

/-- The effective constraint; `none` is `malformedRequest`. -/
def effective : Schema → Wire → Option Gov
  | .required, ⟨some m, some x⟩ => some ⟨m, x⟩
  | .required, _ => none
  | .defaulted d, w =>
      some ⟨w.minApprovals.getD d.minApprovals, w.excludeRequester.getD d.excludeRequester⟩

/-- The producer sends either the governance value or nothing, per member. -/
def Honest (g : Gov) (w : Wire) : Prop :=
  (w.minApprovals = none ∨ w.minApprovals = some g.minApprovals) ∧
  (w.excludeRequester = none ∨ w.excludeRequester = some g.excludeRequester)

def counted (g : Gov) (requester : Party) (approvers : List Party) : Nat :=
  (if g.excludeRequester then approvers.filter (· != requester) else approvers).length

def passes (g : Gov) (requester : Party) (approvers : List Party) : Bool :=
  decide (g.minApprovals ≤ counted g requester approvers)

/-- The ruling: with the members required, whatever the consumer evaluates is
the governance framework's constraint, and an omission is refused. -/
theorem required_sound {g e : Gov} {w : Wire} (hw : Honest g w)
    (he : effective .required w = some e) : e = g := by
  obtain ⟨hm, hx⟩ := hw
  rcases w with ⟨_ | m, _ | x⟩ <;> simp [effective] at he
  simp at hm hx
  subst hm hx
  exact he.symm

theorem required_refuses_omission (w : Wire)
    (h : w.minApprovals = none ∨ w.excludeRequester = none) :
    effective .required w = none := by
  rcases w with ⟨_ | m, _ | x⟩ <;> simp_all [effective]

/-- Non-vacuity: a complete wire constraint is evaluated as sent, and an
approval meeting it passes. -/
theorem required_nonvacuous :
    Honest ⟨3, true⟩ ⟨some 3, some true⟩ ∧
    effective .required ⟨some 3, some true⟩ = some ⟨3, true⟩ ∧
    passes ⟨3, true⟩ 10 [11, 12, 13] = true :=
  ⟨⟨Or.inr rfl, Or.inr rfl⟩, rfl, rfl⟩

/-- The alternative, as `policy/_shared/0.3` had it (`minApprovals` 1,
`excludeRequester` false): governance says three approvers, requester
excluded; the policy engine supplies neither; the request validates; the
requester's own single approval passes. -/
theorem defaulted_quorum_unsound :
    Honest ⟨3, true⟩ ⟨none, none⟩ ∧
    effective (.defaulted ⟨1, false⟩) ⟨none, none⟩ = some ⟨1, false⟩ ∧
    passes ⟨1, false⟩ 10 [10] = true ∧
    passes ⟨3, true⟩ 10 [10] = false :=
  ⟨⟨Or.inl rfl, Or.inl rfl⟩, rfl, rfl, rfl⟩

/-- Nothing in the evaluation distinguishes an omission from an explicit
choice of the default. -/
theorem omission_indistinguishable (d : Gov) :
    effective (.defaulted d) ⟨none, none⟩ =
      effective (.defaulted d) ⟨some d.minApprovals, some d.excludeRequester⟩ := rfl

/-- A shared component is used by communities whose governance differs, and
any default it fixes is wrong for one of them. -/
theorem shared_default_wrong_somewhere (d : Gov) :
    ∃ g : Gov, Honest g ⟨none, none⟩ ∧ effective (.defaulted d) ⟨none, none⟩ ≠ some g := by
  refine ⟨⟨d.minApprovals + 1, d.excludeRequester⟩, ⟨Or.inl rfl, Or.inl rfl⟩, ?_⟩
  simp [effective]

/-- A default is harmless for a community exactly when it is that community's
own governance value. -/
theorem default_sound_iff_governance (d g : Gov) :
    (∀ w, Honest g w → effective (.defaulted d) w = some g) ↔ d = g := by
  constructor
  · intro h
    have := h ⟨none, none⟩ ⟨Or.inl rfl, Or.inl rfl⟩
    simp only [effective, Option.getD_none, Option.some.injEq] at this
    rw [← this]
  · rintro rfl w ⟨hm, hx⟩
    rcases w with ⟨m, x⟩
    rcases hm with hm | hm <;> rcases hx with hx | hx <;>
      simp only at hm hx <;> subst hm hx <;> first | rfl | trivial

end Defaults

end TrustTasks.Rulings
