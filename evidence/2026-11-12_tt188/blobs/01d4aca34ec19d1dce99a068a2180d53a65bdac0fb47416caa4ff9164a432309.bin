/-
Threshold approval in the task-consent family, read against upstream
trustoverip/dtgwg-trust-tasks-tf main (101a51d8d):
`specs/task-consent/request/0.1/spec.md` and
`specs/task-consent/decision/0.2/spec.md` (with their payload schemas).

The invariant decision/0.2 states: "No state-mutating task executes at the
executor unless it has verified a single-use decision, signed by a
**currently-enrolled** approver, whose `payloadDigest` equals the digest of
the **exact payload it is about to execute** ... and unless policy and
enrolment **still** permit it at the moment of execution."

Rules read, all from decision/0.2's consumer conformance list:
item 2, look up the pending request by `payloadDigest`, "absent or lapsed →
`noPending`" (`noPending`: "never raised, already decided, or lapsed");
item 5, "Assert the proven signer is a member of the approver set the policy
named"; item 6, "Assert the signer is not the requester when
`excludeRequester` is set"; item 9, "On `deny`, close the pending request for
every approver"; item 10, "On `approve`, record the approval idempotently per
approver, and at the threshold of distinct approvers ... issue a single-use,
time-boxed grant ... or execute the parked operation itself, exactly once";
item 11, "Re-derive `payloadDigest` from the payload it is about to execute
and refuse on mismatch"; item 13, "Consume the challenge at execution, not on
receipt of this decision. A decision authorizes exactly one execution";
item 14, "Re-evaluate policy and every approver's enrolment and standing. An
approver revoked during the approval window MUST NOT be able to carry a task
through it." request/0.1 producer item 9 says the same as item 14.

What is modelled: one pending request (its approver set resolved to a list,
its requester, `excludeRequester`, `minApprovals`, its digest), the set of
currently enrolled approvers (revocation removes one), the approvals
recorded, whether the request is pending, granted or denied, the challenge,
and the executions performed (by digest). Items 2 and 11 are the guards
`d = q.digest`; standing at re-check (item 14) is membership of the set,
not being the excluded requester, and enrolment.

Results. Under the rules as written, an execution happens at most once, of
the approved digest, and is carried by at least `minApprovals` distinct
approvers who are in the set, are not the excluded requester, and are
enrolled at the moment of execution (`execution_sound`); a deny that is
accepted means the task never runs, and once granted no further decision is
accepted (`deny_final`, `granted_closed`). Idempotent recording, consumption
at execution, the re-check, and closing on deny are each needed. Items 5 and
6 at receipt are not needed for this guarantee once item 14 is in force;
without both, a requester carries its own task (`exclusion_needed`).

Gap. `minApprovals` is constrained only by `"minimum": 1`
(request/0.1/payload.schema.json, `minApprovals`; likewise
policy/_shared/0.4 `requireConsent.minApprovals`) and `approverSet` is a name.
Nothing in request/0.1 or decision/0.2 refuses a request whose threshold
exceeds the eligible approvers; such a request is prompted and its approvals
recorded, and it can never run (`unmeetable_accepted_never_runs`). The fix,
a mint-time check that enough distinct eligible enrolled approvers exist,
refuses no request that could ever run (`runs_only_if_feasible`).

Not modelled: signatures and evidence (items 1, 7, 8), the challenge's
per-approver form (item 3), `actionId` (item 4), `statePin` (item 12), time
and `expiresAt`, policy re-evaluation beyond the approver set and
`excludeRequester`, enrolment of new approvers during the window, the
`granted` notice, and the consent surface.
-/

namespace TrustTasks.TaskConsent

/-- The pending request, as the executor minted it. -/
structure Req where
  approverSet : List Nat
  requester : Nat
  excludeRequester : Bool
  minApprovals : Nat
  digest : Nat
  deriving DecidableEq, Repr

/-- Eligible by the request's own terms (items 5 and 6). -/
def eligible (q : Req) (a : Nat) : Bool :=
  q.approverSet.contains a && !(q.excludeRequester && a == q.requester)

structure St where
  enrolled : List Nat
  approvals : List Nat
  pending : Bool
  granted : Bool
  denied : Bool
  challenge : Bool
  ran : List Nat
  deriving DecidableEq, Repr

def init (e : List Nat) : St := ⟨e, [], true, false, false, true, []⟩

/-- Which rules the executor applies. `strict` is all of them. -/
structure Rules where
  /-- Items 5 and 6 at receipt. -/
  receipt : Bool
  /-- Item 10: approvals recorded idempotently per approver. -/
  distinct : Bool
  /-- Item 9: a deny closes the request. -/
  denyCloses : Bool
  /-- Item 13: the challenge is consumed at execution. Otherwise it was
  consumed on receipt and cannot gate execution. -/
  atExec : Bool
  /-- Item 14: standing re-checked at execution. -/
  recheck : Bool
  deriving DecidableEq, Repr

def strict : Rules := ⟨true, true, true, true, true⟩

/-- Standing now: eligible and currently enrolled. -/
def standing (q : Req) (s : St) (a : Nat) : Bool :=
  eligible q a && s.enrolled.contains a

def accepts (r : Rules) (q : Req) (s : St) (a : Nat) : Bool :=
  !r.receipt || standing q s a

def record (r : Rules) (a : Nat) (l : List Nat) : List Nat :=
  if r.distinct && l.contains a then l else a :: l

/-- Item 10: record, and at the threshold grant; the request is then decided. -/
def afterApprove (r : Rules) (q : Req) (s : St) (a : Nat) : St :=
  let l := record r a s.approvals
  { s with approvals := l, granted := decide (q.minApprovals ≤ l.length),
           pending := !decide (q.minApprovals ≤ l.length) }

inductive Step (r : Rules) (q : Req) : St → St → Prop
  /-- An `approve` decision from `a` for digest `d`. -/
  | approve (s : St) (a d : Nat) : s.pending = true → d = q.digest →
      accepts r q s a = true → Step r q s (afterApprove r q s a)
  /-- A `deny` decision. -/
  | deny (s : St) (a d : Nat) : s.pending = true → d = q.digest →
      accepts r q s a = true →
      Step r q s { s with denied := true, pending := !r.denyCloses && s.pending }
  /-- An approver's enrolment is revoked. -/
  | revoke (s : St) (a : Nat) :
      Step r q s { s with enrolled := s.enrolled.filter (· != a) }
  /-- The executor runs the task with digest `d`. -/
  | execute (s : St) (d : Nat) : s.granted = true → d = q.digest →
      (r.atExec = true → s.challenge = true) →
      (r.recheck = true → q.minApprovals ≤ (s.approvals.filter (standing q s)).length) →
      Step r q s { s with challenge := false, ran := d :: s.ran }

inductive Reach (r : Rules) (q : Req) (s0 : St) : St → Prop
  | refl : Reach r q s0 s0
  | step {s s' : St} : Reach r q s0 s → Step r q s s' → Reach r q s0 s'

/-! ### Soundness of the rules as written -/

/-- Item 13: at most one execution, of the approved digest. -/
theorem at_most_once {r : Rules} {q : Req} {e : List Nat} {s : St}
    (hr : r.atExec = true) (h : Reach r q (init e) s) :
    s.ran = [] ∨ (s.ran = [q.digest] ∧ s.challenge = false) := by
  induction h with
  | refl => exact Or.inl rfl
  | @step s _ _ st ih =>
      cases st with
      | approve => exact ih
      | deny => exact ih
      | revoke => exact ih
      | execute d _ hd hc _ =>
          have hc := hc hr
          rcases ih with h0 | ⟨_, h1⟩
          · exact Or.inr ⟨by simp [h0, hd], rfl⟩
          · rw [hc] at h1; cases h1

/-- Item 10: recorded approvals are distinct. -/
theorem approvals_nodup {r : Rules} {q : Req} {e : List Nat} {s : St}
    (hr : r.distinct = true) (h : Reach r q (init e) s) : s.approvals.Nodup := by
  induction h with
  | refl => exact List.nodup_nil
  | @step s _ _ st ih =>
      cases st with
      | approve a =>
          simp only [afterApprove, record, hr, Bool.true_and]
          by_cases hc : s.approvals.contains a = true
          · simp only [hc, if_true]; exact ih
          · simp only [hc]
            refine List.nodup_cons.mpr ⟨?_, ih⟩
            intro hm; exact hc (List.contains_iff_mem.mpr hm)
      | deny => exact ih
      | revoke => exact ih
      | execute => exact ih

/-- Enrolment only shrinks during the window (no enrolment is modelled). -/
theorem enrolled_sub {r : Rules} {q : Req} {e : List Nat} {s : St}
    (h : Reach r q (init e) s) : ∀ a, a ∈ s.enrolled → a ∈ e := by
  induction h with
  | refl => intro a ha; exact ha
  | @step s _ _ st ih =>
      cases st with
      | approve => exact ih
      | deny => exact ih
      | revoke b =>
          intro a ha
          exact ih a (List.mem_filter.mp ha).1
      | execute => exact ih

/-- The rules as written: an execution step is the first and only one, runs
the approved digest, and is carried by at least `minApprovals` distinct
approvers who approved, are in the set, are not the excluded requester, and
are enrolled at that moment. Items 5 and 6 at receipt are not assumed. -/
theorem execution_sound {r : Rules} {q : Req} {e : List Nat} {s s' : St}
    (hd : r.distinct = true) (hx : r.atExec = true) (hc : r.recheck = true)
    (h : Reach r q (init e) s) (st : Step r q s s') (hran : s'.ran ≠ s.ran) :
    s.ran = [] ∧ s'.ran = [q.digest] ∧
    ∃ L : List Nat, L.Nodup ∧ q.minApprovals ≤ L.length ∧
      ∀ a, a ∈ L → a ∈ s.approvals ∧ a ∈ q.approverSet ∧
        ¬(q.excludeRequester = true ∧ a = q.requester) ∧ a ∈ s.enrolled := by
  cases st with
  | approve => exact absurd rfl hran
  | deny => exact absurd rfl hran
  | revoke => exact absurd rfl hran
  | execute d _ hdg hch hre =>
      have h0 : s.ran = [] := by
        rcases at_most_once hx h with h0 | ⟨_, h1⟩
        · exact h0
        · rw [hch hx] at h1; cases h1
      refine ⟨h0, by simp [h0, hdg], s.approvals.filter (standing q s),
        (approvals_nodup hd h).sublist List.filter_sublist, hre hc, ?_⟩
      intro a ha
      have ⟨ham, hs⟩ := List.mem_filter.mp ha
      simp only [standing, eligible, Bool.and_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff, List.contains_iff_mem] at hs
      obtain ⟨⟨hset, hex⟩, hen⟩ := hs
      refine ⟨ham, hset, ?_, hen⟩
      rintro ⟨h1, h2⟩
      rcases hex with h3 | h3
      · rw [h1] at h3; cases h3
      · simp [h2] at h3

/-- Item 9: an accepted deny means the task never runs; and once granted, a
request is decided and accepts no further decision (`noPending`, "already
decided"), so no deny arrives between grant and execution. -/
theorem deny_invariant {r : Rules} {q : Req} {e : List Nat} {s : St}
    (hr : r.denyCloses = true) (h : Reach r q (init e) s) :
    (s.pending = true → s.granted = false) ∧
    (s.denied = true → s.pending = false ∧ s.granted = false) ∧
    (s.ran ≠ [] → s.granted = true) := by
  induction h with
  | refl => exact ⟨fun _ => rfl, fun h => by simp [init] at h, fun h => absurd rfl h⟩
  | @step s _ _ st ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      cases st with
      | approve a _ hp _ _ =>
          have hg := i1 hp
          have hdn : s.denied = false := by
            cases hx : s.denied
            · rfl
            · rw [(i2 hx).1] at hp; cases hp
          have hrn : s.ran = [] := by
            cases hx : s.ran
            · rfl
            · rw [i3 (by simp [hx])] at hg; cases hg
          simp only [afterApprove]
          refine ⟨?_, ?_, ?_⟩
          · intro h; simpa using h
          · intro h; simp [hdn] at h
          · intro h; exact absurd hrn h
      | deny a _ hp _ _ =>
          have hg := i1 hp
          refine ⟨?_, ?_, ?_⟩
          · intro h; simp [hr] at h
          · intro _; exact ⟨by simp [hr], hg⟩
          · intro h; rw [i3 h] at hg; cases hg
      | revoke => exact ⟨i1, i2, i3⟩
      | execute _ hg =>
          refine ⟨i1, ?_, fun _ => hg⟩
          intro h; rw [(i2 h).2] at hg; cases hg

theorem deny_final {r : Rules} {q : Req} {e : List Nat} {s : St}
    (hr : r.denyCloses = true) (h : Reach r q (init e) s) (hd : s.denied = true) :
    s.ran = [] := by
  obtain ⟨_, i2, i3⟩ := deny_invariant hr h
  cases hx : s.ran
  · rfl
  · rw [(i2 hd).2] at i3; exact absurd (i3 (by simp [hx])) (by simp)

theorem granted_closed {r : Rules} {q : Req} {e : List Nat} {s : St}
    (hr : r.denyCloses = true) (h : Reach r q (init e) s) (hg : s.granted = true) :
    s.pending = false := by
  obtain ⟨i1, _, _⟩ := deny_invariant hr h
  cases hp : s.pending
  · rfl
  · rw [i1 hp] at hg; cases hg

/-! ### Soundness applies to a real run -/

/-- Approvers 1, 2 and 3; 3 is the requester, excluded; two approvals needed. -/
def q0 : Req := ⟨[1, 2, 3], 3, true, 2, 7⟩

/-- 1 and 2 approve, the grant is issued, the executor runs the task. -/
theorem execution_sound_nonvacuous :
    ∃ s s', Reach strict q0 (init [1, 2, 3]) s ∧ Step strict q0 s s' ∧ s'.ran ≠ s.ran := by
  let s1 := afterApprove strict q0 (init [1, 2, 3]) 1
  let s2 := afterApprove strict q0 s1 2
  have h1 : Reach strict q0 (init [1, 2, 3]) s1 :=
    Reach.step Reach.refl (Step.approve _ 1 7 rfl rfl rfl)
  have h2 : Reach strict q0 (init [1, 2, 3]) s2 :=
    Reach.step h1 (Step.approve _ 2 7 rfl rfl rfl)
  exact ⟨s2, _, h2, Step.execute _ 7 rfl rfl (fun _ => rfl) (fun _ => by decide),
    by decide⟩

/-! ### Each rule is needed -/

/-- Without idempotent recording (item 10), one approver's two approvals meet
a threshold of two, and the task runs. -/
theorem distinct_needed :
    let r : Rules := { strict with distinct := false }
    let q : Req := ⟨[1, 2], 0, true, 2, 7⟩
    ∃ s, Reach r q (init [1, 2]) s ∧ s.ran = [7] ∧ ∀ a, a ∈ s.approvals → a = 1 := by
  intro r q
  have h1 := Reach.step (Reach.refl (r := r) (q := q) (s0 := init [1, 2]))
    (Step.approve _ 1 7 rfl rfl rfl)
  have h2 := Reach.step h1 (Step.approve _ 1 7 rfl rfl rfl)
  refine ⟨_, Reach.step h2 (Step.execute _ 7 rfl rfl (fun _ => rfl) (fun _ => by decide)),
    rfl, ?_⟩
  decide

/-- Consuming the challenge on receipt (against item 13) leaves nothing
single-use at execution: the executor's retry runs the task twice. -/
theorem consume_at_execution_needed :
    let r : Rules := { strict with atExec := false }
    let q : Req := ⟨[1], 0, true, 1, 7⟩
    ∃ s, Reach r q (init [1]) s ∧ s.ran = [7, 7] := by
  intro r q
  have h1 := Reach.step (Reach.refl (r := r) (q := q) (s0 := init [1]))
    (Step.approve _ 1 7 rfl rfl rfl)
  have h2 := Reach.step h1 (Step.execute _ 7 rfl rfl (fun h => by cases h) (fun _ => by decide))
  exact ⟨_, Reach.step h2 (Step.execute _ 7 rfl rfl (fun h => by cases h) (fun _ => by decide)),
    rfl⟩

/-- Without the re-check at execution (item 14), approver 2 is revoked after
approving, and its approval still carries the task: two approvals were needed,
and only one of the two approvers is enrolled when it runs. -/
theorem recheck_needed :
    let r : Rules := { strict with recheck := false }
    let q : Req := ⟨[1, 2], 0, true, 2, 7⟩
    ∃ s, Reach r q (init [1, 2]) s ∧ s.ran = [7] ∧ s.approvals = [2, 1] ∧
      2 ∉ s.enrolled ∧ (s.approvals.filter (standing q s)).length < q.minApprovals := by
  intro r q
  have h1 := Reach.step (Reach.refl (r := r) (q := q) (s0 := init [1, 2]))
    (Step.approve _ 1 7 rfl rfl rfl)
  have h2 := Reach.step h1 (Step.approve _ 2 7 rfl rfl rfl)
  have h3 := Reach.step h2 (Step.revoke _ 2)
  exact ⟨_, Reach.step h3 (Step.execute _ 7 rfl rfl (fun _ => rfl) (fun h => by cases h)),
    rfl, rfl, by decide, by decide⟩

/-- Without closing on deny (item 9), approver 1 denies (and is answered
`denied`), approver 2 then approves, and the task runs. -/
theorem deny_closes_needed :
    let r : Rules := { strict with denyCloses := false }
    let q : Req := ⟨[1, 2], 0, true, 1, 7⟩
    ∃ s, Reach r q (init [1, 2]) s ∧ s.denied = true ∧ s.ran = [7] := by
  intro r q
  have h1 := Reach.step (Reach.refl (r := r) (q := q) (s0 := init [1, 2]))
    (Step.deny _ 1 7 rfl rfl rfl)
  have h2 := Reach.step h1 (Step.approve _ 2 7 rfl rfl rfl)
  exact ⟨_, Reach.step h2 (Step.execute _ 7 rfl rfl (fun _ => rfl) (fun _ => by decide)),
    rfl, rfl⟩

/-- `execution_sound` does not assume items 5 and 6 at receipt: item 14's
re-check subsumes them for execution. Without both the receipt checks and the
re-check, the requester approves its own task with `excludeRequester` set,
and it runs. -/
theorem exclusion_needed :
    let r : Rules := { strict with receipt := false, recheck := false }
    let q : Req := ⟨[1, 2], 1, true, 1, 7⟩
    ∃ s, Reach r q (init [1, 2]) s ∧ s.ran = [7] ∧ s.approvals = [q.requester] := by
  intro r q
  have h1 := Reach.step (Reach.refl (r := r) (q := q) (s0 := init [1, 2]))
    (Step.approve _ 1 7 rfl rfl rfl)
  exact ⟨_, Reach.step h1 (Step.execute _ 7 rfl rfl (fun _ => rfl) (fun h => by cases h)),
    rfl, rfl⟩

/-! ### A threshold the eligible approvers cannot meet -/

/-- Enough distinct approvers, eligible by the request's terms and enrolled
when it is minted, exist to meet the threshold. -/
def Feasible (q : Req) (e : List Nat) : Prop :=
  ∃ L : List Nat, L.Nodup ∧ q.minApprovals ≤ L.length ∧
    ∀ a, a ∈ L → eligible q a = true ∧ a ∈ e

/-- The fix is safe: under items 10 and 14, a request that ever runs was
feasible when minted, so refusing infeasible requests at mint refuses
nothing that could run. -/
theorem runs_only_if_feasible {r : Rules} {q : Req} {e : List Nat} {s : St}
    (hd : r.distinct = true) (hc : r.recheck = true)
    (h : Reach r q (init e) s) (hran : s.ran ≠ []) : Feasible q e := by
  induction h with
  | refl => exact absurd rfl hran
  | @step s s' hreach st ih =>
      cases st with
      | approve => exact ih hran
      | deny => exact ih hran
      | revoke => exact ih hran
      | execute _ _ _ _ hre =>
          refine ⟨s.approvals.filter (standing q s),
            (approvals_nodup hd hreach).sublist List.filter_sublist, hre hc, ?_⟩
          intro a ha
          have hs := (List.mem_filter.mp ha).2
          simp only [standing, Bool.and_eq_true, List.contains_iff_mem] at hs
          exact ⟨hs.1, enrolled_sub hreach a hs.2⟩

/-- Approvers 1 and 2, 2 the requester and excluded, two approvals needed. The
schema admits it (`minApprovals` ≥ 1), approver 1 is prompted and its approval
recorded with the request still pending, and it can never run. -/
def qOver : Req := ⟨[1, 2], 2, true, 2, 7⟩

theorem not_feasible_qOver : ¬ Feasible qOver [1, 2] := by
  rintro ⟨L, hn, hk, hL⟩
  have h1 : ∀ a, a ∈ L → a = 1 := by
    intro a ha
    have ⟨he, hm⟩ := hL a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rfl
    · simp [eligible, qOver] at he
  match L, hn, hk, h1 with
  | x :: y :: _, hn, _, h1 =>
      have hx := h1 x (by simp)
      have hy := h1 y (by simp)
      have := (List.nodup_cons.mp hn).1
      exact absurd (by simp [hx, hy]) this

theorem unmeetable_accepted_never_runs :
    (∃ s, Reach strict qOver (init [1, 2]) s ∧ s.approvals = [1] ∧ s.pending = true) ∧
    ∀ s, Reach strict qOver (init [1, 2]) s → s.ran = [] := by
  refine ⟨⟨_, Reach.step Reach.refl (Step.approve _ 1 7 rfl rfl rfl), rfl, rfl⟩, ?_⟩
  intro s h
  cases hx : s.ran with
  | nil => rfl
  | cons _ _ =>
      exact absurd (runs_only_if_feasible rfl rfl h (by simp [hx])) not_feasible_qOver

end TrustTasks.TaskConsent
