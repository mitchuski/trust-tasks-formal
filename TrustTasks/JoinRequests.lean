/-
The `vtc/join-requests` lifecycle (upstream trustoverip/dtgwg-trust-tasks-tf
main, 101a51d8d), and `vtc/member-onboarding/0.1` read over it.

States, from `status/0.1` (`payload.schema.json`, response `status`):
`pending`, `deferred`, `approved`, `rejected`, `withdrawn`.

Rules, quoted:

* `decide/0.1`, Conformance: "if it is not `pending`, return `notPending` — a
  request already decided, withdrawn, or deferred cannot be re-decided through
  this task. Otherwise apply the decision: on `approved`, admit the applicant
  and set status to `approved`; on `rejected`, set status to `rejected`".
* `submit/0.1`, Conformance: "Otherwise create a pending request".
* `submit/0.3`, Deciding item 2: for a criterion whose `admission` is
  `review`, a consumer "**MUST** answer `refer` and **MUST NOT** admit on the
  submission"; item 3: under `automatic` it "**MUST** answer `allow` and admit
  the applicant, unless it refuses or refers"; item 1 answers `requestMore` or
  `deny` for a submission that does not meet its criterion. The verdict
  effects are `allow`, `deny`, `refer`, `requestMore`
  (`_shared/0.1/ceremony.schema.json`, `VerdictEffect`); the request row's
  `decision` is written by "both rejection paths — a policy auto-deny at submit
  and an admin's later refusal" (`_shared/0.1/join-request.schema.json`). This
  file reads `allow`/`deny`/`refer`/`requestMore` as `approved`/`rejected`/
  `pending`/`deferred` (`status/0.1`: `needs` and `presentationDefinition`
  "when deferred", the members `requestMore` carries).
* `supplement/0.1`: "the request **MUST** be one the community has deferred";
  otherwise `notAwaitingEvidence`, or `alreadyDecided` when "approved, rejected
  or withdrawn"; its verdict "**MAY** be any of the outcomes a submission can
  produce".
* `withdraw/0.1`, summary: "An applicant withdraws their own pending or
  deferred join request"; `alreadyDecided` for "approved, rejected or already
  withdrawn".

Shown: `approved`, `rejected` and `withdrawn` are final; every run admits at
most once, and ends `approved` exactly when it admitted once; under `review`
every admission is a `decide`; `withdraw` and `decide` cannot both close one
request (steps atomic); `deferred` has applicant exits (`supplement`,
`withdraw`), so the ceremony's note "`deferred` is a reachable state with no
defined exit" (`ceremony.json`, step `supplement`) is now stale. Each rule is
shown needed.

Two defects. (1) The ceremony pins the retired `submit/0.1`, under which every
decided request passes through `decide`. Under `submit/0.3` a request admitted
or refused by `submit` or `supplement` never can, since `decide` answers
`notPending`; the completion predicate, which needs `decide`
(Onboarding.lean, `published_is_apply_and_decide`), then never holds. A
completion that reads the deciding verdict wherever it was given holds exactly
when the request was decided, on either version. (2) `withdraw/0.1`
(Authorization): "A community maintainer who wants to end a request uses the
maintainer-facing decision task instead"; but `decide` refuses a deferred
request, so a deferred request stays open until the applicant acts. Letting
`decide` reject (never approve: `submit/0.3` item 1) a deferred request closes
it and keeps every property above.

Not modelled: more than one request per applicant, identities and proofs,
criteria and their content (only the admission mode), the hidden-vetting
challenge, `status` polls, `requestId` resolution, replay windows
(`issuedAt`), `maxDuration`, retention sweeps, and ceremony steps other than
`apply` and `decide`. A step is taken as present when its task succeeded; a
refused `decide` (`notPending`) is not a decision.
-/

namespace TrustTasks.JoinRequests

inductive Status
  | pending
  | deferred
  | approved
  | rejected
  | withdrawn
  deriving DecidableEq, Repr

/-- `VerdictEffect`. -/
inductive Effect
  | allow
  | deny
  | refer
  | requestMore
  deriving DecidableEq, Repr

def Effect.status : Effect → Status
  | .allow => .approved
  | .deny => .rejected
  | .refer => .pending
  | .requestMore => .deferred

/-- `decide`'s `decision`. -/
inductive Decision
  | approved
  | rejected
  deriving DecidableEq, Repr

def Decision.status : Decision → Status
  | .approved => .approved
  | .rejected => .rejected

/-- The governing criterion's `admission`. -/
inductive Admission
  | automatic
  | review
  deriving DecidableEq, Repr

inductive Op
  /-- `submit/0.1`: always `pending`. -/
  | submit01
  /-- `submit/0.3` with the verdict it returned. -/
  | submit03 (e : Effect)
  /-- `decide/0.1` (administrator). -/
  | decide (d : Decision)
  /-- `supplement/0.1` with the verdict it returned. -/
  | supplement (e : Effect)
  /-- `withdraw/0.1` (applicant). -/
  | withdraw
  deriving DecidableEq, Repr

/-- The rules, each switchable so its need can be shown. `closeDeferred` is
the proposed fix (off today). -/
structure Rules where
  /-- `decide`: `notPending`. -/
  decidePending : Bool
  /-- `supplement`: `notAwaitingEvidence` / `alreadyDecided`. -/
  supplementDeferred : Bool
  /-- `withdraw`: `alreadyDecided`. -/
  withdrawOpen : Bool
  /-- `submit/0.3` item 2: under `review`, never `allow`. -/
  reviewNoAllow : Bool
  /-- Fix: `decide` may reject a deferred request. -/
  closeDeferred : Bool

def today : Rules := ⟨true, true, true, true, false⟩
def fixed : Rules := ⟨true, true, true, true, true⟩

/-- A verdict the consumer may not give. -/
def Rules.blocks (r : Rules) (a : Admission) (e : Effect) : Bool :=
  r.reviewNoAllow && a == .review && e == .allow

def Status.isOpen : Status → Bool
  | .pending | .deferred => true
  | _ => false

def isFinal : Option Status → Bool
  | some .approved | some .rejected | some .withdrawn => true
  | _ => false

/-- One step on one request (`none`: no request yet). `none` as a result: the
task is refused and nothing changes. -/
def step (r : Rules) (a : Admission) : Option Status → Op → Option (Option Status)
  | none, .submit01 => some (some .pending)
  | none, .submit03 e => if r.blocks a e then none else some (some e.status)
  | some s, .decide d =>
      if s = .pending ∨ r.decidePending = false ∨
          (r.closeDeferred = true ∧ s = .deferred ∧ d = .rejected)
      then some (some d.status) else none
  | some s, .supplement e =>
      if (s = .deferred ∨ r.supplementDeferred = false) ∧ r.blocks a e = false
      then some (some e.status) else none
  | some s, .withdraw =>
      if s.isOpen = true ∨ r.withdrawOpen = false then some (some .withdrawn) else none
  | _, _ => none

/-- The successful steps of a run, each with the state it led to. -/
def run (r : Rules) (a : Admission) : Option Status → List Op → List (Op × Option Status)
  | _, [] => []
  | s, op :: ops =>
      match step r a s op with
      | some t => (op, t) :: run r a t ops
      | none => run r a s ops

def final (r : Rules) (a : Admission) : Option Status → List Op → Option Status
  | s, [] => s
  | s, op :: ops =>
      match step r a s op with
      | some t => final r a t ops
      | none => final r a s ops

/-- Steps that admitted. -/
def admissions (r : Rules) (a : Admission) (s : Option Status) (ops : List Op) : Nat :=
  ((run r a s ops).filter (fun p => p.2 == some .approved)).length

/-- Steps that closed the request. -/
def closings (r : Rules) (a : Admission) (s : Option Status) (ops : List Op) : Nat :=
  ((run r a s ops).filter (fun p => isFinal p.2)).length

/-- The three refusal rules in force. -/
structure Rules.Good (r : Rules) : Prop where
  dp : r.decidePending = true
  sd : r.supplementDeferred = true
  wo : r.withdrawOpen = true

theorem today_good : today.Good := ⟨rfl, rfl, rfl⟩
theorem fixed_good : fixed.Good := ⟨rfl, rfl, rfl⟩

/-! ### Soundness of the rules as written -/

/-- `approved`, `rejected` and `withdrawn` are final: every task on them is
refused. -/
theorem final_absorbing {r : Rules} (hr : r.Good) (a : Admission) {s : Option Status}
    (hs : isFinal s = true) (op : Op) : step r a s op = none := by
  obtain ⟨dp, sd, wo, rn, cd⟩ := r
  obtain ⟨h1, h2, h3⟩ := hr
  simp only at h1 h2 h3
  subst h1 h2 h3
  rcases s with _ | s
  · cases hs
  · cases s <;> cases hs <;> cases op <;> simp [step, Status.isOpen]

theorem run_from_final {r : Rules} (hr : r.Good) (a : Admission) {s : Option Status}
    (hs : isFinal s = true) (ops : List Op) : run r a s ops = [] ∧ final r a s ops = s := by
  induction ops with
  | nil => exact ⟨rfl, rfl⟩
  | cons op ops ih => simp only [run, final, final_absorbing hr a hs op]; exact ih

/-- At most one step closes a request: in particular `withdraw` and `decide`
cannot both succeed on it, whichever comes first. -/
theorem closings_le_one {r : Rules} (hr : r.Good) (a : Admission) (s : Option Status)
    (ops : List Op) : closings r a s ops ≤ 1 := by
  induction ops generalizing s with
  | nil => simp [closings, run]
  | cons op ops ih =>
      unfold closings run
      split
      · next t _ =>
          cases ht : isFinal t
          · simp only [List.filter_cons, ht]; exact ih t
          · simp [ht, (run_from_final hr a ht ops).1]
      · exact ih s

private theorem approved_final : isFinal (some .approved) = true := rfl

/-- Admission happens through exactly one step: a run from a request not yet
admitted admits at most once, and ends `approved` exactly when it admitted. -/
theorem admission_once {r : Rules} (hr : r.Good) (a : Admission) (s : Option Status)
    (hs : s ≠ some .approved) (ops : List Op) :
    admissions r a s ops ≤ 1 ∧ (admissions r a s ops = 1 ↔ final r a s ops = some .approved) := by
  induction ops generalizing s with
  | nil => simp [admissions, run, final, hs]
  | cons op ops ih =>
      unfold admissions run final
      split
      · next t _ =>
          by_cases ht : t = some .approved
          · subst ht
            simp [(run_from_final hr a approved_final ops).1,
              (run_from_final hr a approved_final ops).2]
          · have hne : (t == some Status.approved) = false := by simp [ht]
            simp only [List.filter_cons, hne]
            exact ih t ht
      · exact ih s hs

theorem admitted_once {r : Rules} (hr : r.Good) (a : Admission) (ops : List Op) :
    final r a none ops = some .approved ↔ admissions r a none ops = 1 :=
  (admission_once hr a none (by simp) ops).2.symm

def Op.isDecideApproved : Op → Bool
  | .decide .approved => true
  | _ => false

/-- Under `review` (`submit/0.3` item 2), every admission is an
administrator's `decide`. -/
theorem review_admits_by_decide {r : Rules} (hr : r.Good) (hn : r.reviewNoAllow = true)
    (s : Option Status) (hs : s ≠ some .approved) (ops : List Op)
    (h : final r .review s ops = some .approved) :
    (run r .review s ops).any (fun p => p.1.isDecideApproved) = true := by
  induction ops generalizing s with
  | nil => exact absurd h hs
  | cons op ops ih =>
      unfold run
      unfold final at h
      split at h
      · next t hst =>
          simp only [List.any_cons, Bool.or_eq_true]
          by_cases ht : t = some .approved
          · left
            subst ht
            obtain ⟨dp, sd, wo, rn, cd⟩ := r
            obtain ⟨h1, h2, h3⟩ := hr
            simp only at h1 h2 h3 hn
            subst h1 h2 h3 hn
            rcases s with _ | s
            · cases op <;> simp [step] at hst
              next e => cases e <;> simp_all [Rules.blocks, Effect.status]
            · cases op <;> simp [step] at hst
              next d => cases d <;> simp_all [Decision.status, Op.isDecideApproved]
              next e => cases e <;> simp_all [Rules.blocks, Effect.status]
          · right; exact ih t ht h
      · next hst => exact ih s hs h

/-- `deferred` has exits: `supplement` with any verdict the criterion allows,
and `withdraw`. The ceremony's note that it has none is stale. -/
theorem deferred_exits (a : Admission) :
    step today a (some .deferred) .withdraw = some (some .withdrawn) ∧
    step today a (some .deferred) (.supplement .deny) = some (some .rejected) ∧
    step today a (some .deferred) (.supplement .refer) = some (some .pending) ∧
    step today .automatic (some .deferred) (.supplement .allow) = some (some .approved) := by
  cases a <;> decide

/-! ### Each rule is needed -/

/-- Without `notPending`, an admitted applicant is then refused, and a
withdrawn request is decided. -/
theorem notPending_needed :
    let r : Rules := { today with decidePending := false }
    final r .automatic none [.submit01, .decide .approved, .decide .rejected] = some .rejected ∧
    admissions r .automatic none [.submit01, .decide .approved, .decide .rejected] = 1 ∧
    final r .automatic none [.submit01, .withdraw, .decide .approved] = some .approved := by
  decide

/-- Without `supplement`'s state rule, a refused applicant supplements their
way in. -/
theorem supplementDeferred_needed :
    let r : Rules := { today with supplementDeferred := false }
    final r .automatic none [.submit01, .decide .rejected, .supplement .allow] = some .approved ∧
    closings r .automatic none [.submit01, .decide .rejected, .supplement .allow] = 2 := by
  decide

/-- Without `withdraw`'s `alreadyDecided`, an admission is followed by a
withdrawal of the same request: two closings. -/
theorem withdrawOpen_needed :
    let r : Rules := { today with withdrawOpen := false }
    final r .automatic none [.submit01, .decide .approved, .withdraw] = some .withdrawn ∧
    closings r .automatic none [.submit01, .decide .approved, .withdraw] = 2 := by
  decide

/-- Without `submit/0.3` item 2, a `review` criterion admits on the
submission, with no administrator. -/
theorem reviewNoAllow_needed :
    let r : Rules := { today with reviewNoAllow := false }
    final r .review none [.submit03 .allow] = some .approved ∧
    (run r .review none [.submit03 .allow]).any (fun p => p.1.isDecideApproved) = false := by
  decide

/-- Nonvacuity: deferred, supplemented, referred and approved by an
administrator, under `review`; and a withdrawal. -/
theorem lifecycle_nonvacuous :
    final today .review none [.submit03 .requestMore, .supplement .refer, .decide .approved] =
      some .approved ∧
    admissions today .review none
      [.submit03 .requestMore, .supplement .refer, .decide .approved] = 1 ∧
    final today .review none [.submit01, .withdraw] = some .withdrawn := by
  decide

/-! ### Defect 1: the ceremony over `submit/0.3` -/

def Op.isSubmit : Op → Bool
  | .submit01 | .submit03 _ => true
  | _ => false

def Op.isDecide : Op → Bool
  | .decide _ => true
  | _ => false

def Op.isV03 : Op → Bool
  | .submit03 _ => true
  | _ => false

/-- The published completion, `apply ∧ decide` (Onboarding.lean,
`published_is_apply_and_decide`), on a run. -/
def published (tr : List (Op × Option Status)) : Bool :=
  tr.any (fun p => p.1.isSubmit) && tr.any (fun p => p.1.isDecide)

def decided : Option Status → Bool
  | some .approved | some .rejected => true
  | _ => false

private theorem step_v01 {r : Rules} (hr : r.Good) {a : Admission} {s t : Option Status}
    {op : Op} (h : step r a s op = some t) (hv : op.isV03 = false)
    (hs : s ≠ some .deferred) :
    t ≠ some .deferred ∧ (decided t = true → op.isDecide = true) ∧
      (s = none → op.isSubmit = true) := by
  obtain ⟨dp, sd, wo, rn, cd⟩ := r
  obtain ⟨h1, h2, h3⟩ := hr
  simp only at h1 h2 h3
  subst h1 h2 h3
  rcases s with _ | s
  · cases op with
    | submit01 => simp [step] at h; subst h; simp [decided, Op.isSubmit]
    | submit03 e => simp [Op.isV03] at hv
    | _ => simp [step] at h
  · cases op with
    | decide d =>
        cases d <;> simp [step] at h <;>
          (obtain ⟨_, rfl⟩ := h; simp [decided, Op.isDecide, Decision.status])
    | supplement e => cases s <;> simp_all [step]
    | withdraw =>
        cases s <;> simp [step, Status.isOpen] at h <;> (subst h; simp [decided])
    | submit01 => simp [step] at h
    | submit03 e => simp [step] at h

/-- Under `submit/0.1` the published completion is sound for the lifecycle:
every decided request completes. -/
theorem ceremony_v01_completes {r : Rules} (hr : r.Good) (a : Admission) (ops : List Op)
    (hv : ops.all (fun op => !op.isV03) = true) (hd : decided (final r a none ops) = true) :
    published (run r a none ops) = true := by
  -- Invariant from any state that is not `deferred`: a decided end has a
  -- `decide` in the run, and from `none` a non-empty run starts with a submit.
  have key : ∀ (ops : List Op) (s : Option Status), ops.all (fun op => !op.isV03) = true →
      s ≠ some .deferred → decided s = false → decided (final r a s ops) = true →
      (run r a s ops).any (fun p => p.1.isDecide) = true ∧
      (s = none → (run r a s ops).any (fun p => p.1.isSubmit) = true) := by
    intro ops
    induction ops with
    | nil => intro s _ _ hs hd; simp [final] at hd; rw [hs] at hd; cases hd
    | cons op ops ih =>
        intro s hv hs hsd hd
        simp only [List.all_cons, Bool.and_eq_true] at hv
        have hop : op.isV03 = false := by simpa using hv.1
        unfold run
        unfold final at hd
        split at hd
        · next t hst =>
            obtain ⟨htd, hdec, hsub⟩ := step_v01 hr hst hop hs
            simp only [List.any_cons, Bool.or_eq_true]
            refine ⟨?_, fun hn => Or.inl (hsub hn)⟩
            cases hdt : decided t
            · exact Or.inr (ih t hv.2 htd hdt hd).1
            · exact Or.inl (hdec hdt)
        · next hst =>
            refine ⟨(ih s hv.2 hs hsd hd).1, fun hn => ?_⟩
            subst hn
            -- from `none`, a refused first op leaves `none`
            exact (ih none hv.2 (by simp) rfl hd).2 rfl
  obtain ⟨h1, h2⟩ := key ops none hv (by simp) rfl hd
  simp [published, h1, h2 rfl]

/-- Under `submit/0.3` it is not: a request admitted or refused at submission,
or by a supplement, is decided, and no continuation ever completes it. -/
theorem ceremony_v03_never_completes (ops : List Op) :
    let r := today
    decided (final r .automatic none (.submit03 .allow :: ops)) = true ∧
    published (run r .automatic none (.submit03 .allow :: ops)) = false ∧
    decided (final r .automatic none (.submit03 .deny :: ops)) = true ∧
    published (run r .automatic none (.submit03 .deny :: ops)) = false ∧
    decided (final r .automatic none (.submit03 .requestMore :: .supplement .allow :: ops)) = true ∧
    published (run r .automatic none
      (.submit03 .requestMore :: .supplement .allow :: ops)) = false := by
  have hA := run_from_final today_good .automatic (s := some .approved) rfl ops
  have hR := run_from_final today_good .automatic (s := some .rejected) rfl ops
  have e1 : step today .automatic none (.submit03 .allow) = some (some .approved) := by decide
  have e2 : step today .automatic none (.submit03 .deny) = some (some .rejected) := by decide
  have e3 : step today .automatic none (.submit03 .requestMore) = some (some .deferred) := by
    decide
  have e4 : step today .automatic (some .deferred) (.supplement .allow) =
      some (some .approved) := by decide
  simp only [run, final, e1, e2, e3, e4, hA.1, hA.2, hR.1, hR.2]
  decide

/-- A step that decided: a `decide`, or a `submit`/`supplement` whose verdict
is `allow` or `deny`. A completion that reads it is the declared read of
spec#52 (Ceremony.lean) applied to the verdict as well as to `decision`. -/
def Op.isDeciding : Op → Bool
  | .decide _ => true
  | .submit03 .allow | .submit03 .deny => true
  | .supplement .allow | .supplement .deny => true
  | _ => false

def proposed (tr : List (Op × Option Status)) : Bool :=
  tr.any (fun p => p.1.isSubmit) && tr.any (fun p => p.1.isDeciding)

private theorem step_deciding {r : Rules} (hr : r.Good) {a : Admission} {s t : Option Status}
    {op : Op} (h : step r a s op = some t) :
    (decided t = true ↔ op.isDeciding = true) ∧ (s = none → op.isSubmit = true) := by
  obtain ⟨dp, sd, wo, rn, cd⟩ := r
  obtain ⟨h1, h2, h3⟩ := hr
  simp only at h1 h2 h3
  subst h1 h2 h3
  rcases s with _ | s
  · cases op with
    | submit03 e =>
        cases e <;> cases rn <;> cases a <;> simp [step, Rules.blocks, Effect.status] at h <;>
          (subst h; simp [decided, Op.isDeciding, Op.isSubmit])
    | submit01 => simp [step] at h; subst h; simp [decided, Op.isDeciding, Op.isSubmit]
    | _ => simp [step] at h
  · cases op with
    | decide d =>
        cases d <;> simp [step] at h <;> (obtain ⟨_, rfl⟩ := h; simp [decided, Op.isDeciding,
          Decision.status])
    | supplement e =>
        cases e <;> simp [step] at h <;> (obtain ⟨_, rfl⟩ := h; simp [decided, Op.isDeciding,
          Effect.status])
    | withdraw =>
        simp [step] at h; obtain ⟨_, rfl⟩ := h; simp [decided, Op.isDeciding]
    | submit01 => simp [step] at h
    | submit03 e => simp [step] at h

/-- The fix: on either submit version, the proposed completion holds exactly
when the request was decided. -/
theorem proposed_iff_decided {r : Rules} (hr : r.Good) (a : Admission) (ops : List Op) :
    proposed (run r a none ops) = decided (final r a none ops) := by
  have key : ∀ (ops : List Op) (s : Option Status), decided s = false →
      (run r a s ops).any (fun p => p.1.isDeciding) = decided (final r a s ops) ∧
      (s = none → decided (final r a s ops) = true →
        (run r a s ops).any (fun p => p.1.isSubmit) = true) := by
    intro ops
    induction ops with
    | nil => intro s hs; simp [run, final, hs]
    | cons op ops ih =>
        intro s hs
        unfold run final
        split
        · next t hst =>
            obtain ⟨hdec, hsub⟩ := step_deciding hr hst
            simp only [List.any_cons]
            refine ⟨?_, fun hn _ => by simp [hsub hn]⟩
            cases hdt : decided t
            · have hn : op.isDeciding = false := by
                cases h : op.isDeciding
                · rfl
                · rw [← hdec] at h; rw [hdt] at h; cases h
              rw [hn, Bool.false_or]; exact (ih t hdt).1
            · have hfin : isFinal t = true := by
                rcases t with _ | t
                · cases hdt
                · cases t <;> first | rfl | cases hdt
              rw [(hdec.1 hdt), Bool.true_or, (run_from_final hr a hfin ops).2, hdt]
        · next => exact ih s hs
  obtain ⟨h1, h2⟩ := key ops none rfl
  unfold proposed
  rw [h1]
  cases hd : decided (final r a none ops)
  · simp
  · simp [h2 rfl hd]

/-- Nonvacuity of the fix: it completes an admission at submission and a
deferred-then-approved request, and not a request still referred or one
withdrawn. -/
theorem proposed_nonvacuous :
    proposed (run today .automatic none [.submit03 .allow]) = true ∧
    proposed (run today .review none
      [.submit03 .requestMore, .supplement .refer, .decide .approved]) = true ∧
    proposed (run today .review none [.submit03 .refer]) = false ∧
    proposed (run today .automatic none [.submit01, .withdraw]) = false := by
  decide

/-! ### Defect 2: the community cannot close a deferred request -/

/-- `decide` refuses a deferred request whatever it decides, so a run of
administrator steps leaves it deferred: it closes only if the applicant acts. -/
theorem community_cannot_close_deferred (a : Admission) (ds : List Decision) :
    final today a (some .deferred) (ds.map Op.decide) = some .deferred := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simpa [final, step, today] using ih

/-- The fix lets an administrator reject a deferred request, never approve it
(`submit/0.3` item 1: a submission that does not meet its criterion is not
admitted), and `fixed` keeps every property proved above for `Rules.Good`
(`fixed_good`). -/
theorem fixed_closes_deferred (a : Admission) :
    step fixed a (some .deferred) (.decide .rejected) = some (some .rejected) ∧
    step fixed a (some .deferred) (.decide .approved) = none := by
  cases a <;> decide

end TrustTasks.JoinRequests
