/-
A model of a MyTerms (IEEE Std 7012-2025) handshake carried as a Trust Tasks
family, `myterms/propose`, and of a ceremony that puts a comprehension
exchange in front of it.

The shape follows the outline on trustoverip/dtgwg-trust-tasks-spec#43:
the individual's agent proposes one agreement from a neutral roster; the
entity's agent answers `accepted` (with a contract identifier), `alternative`
(one agreement from the same roster) or `rejected`; one follow-up, citing the
answered request by `respondsTo`, may take the alternative; any further round
is refused.

What is modelled: the order of requests and responses in one engagement, who
issues each, which roster agreements they name, and which outcomes the entity
may give. What is not: signatures (a request's `issuer` is taken as
authenticated by the envelope), digests, time, transport, the roster's
neutrality, and the meaning of the agreements themselves.

The question this model answers is the one asked on
trustoverip/dtgwg-trust-tasks-tf#904: can a ceremony's completion check tell
accepted, alternative and rejected apart by reading one required, closed
`decision` member? `decision_member_suffices` says yes, under the response
well-formedness rule; `presence_completion_unsound` shows that checking only
that a response is present does not.
-/

namespace TrustTasks.MyTerms

/-- Parties and request identifiers are opaque. -/
abbrev Party := Nat
abbrev ReqId := Nat
/-- An agreement is a roster code (in the outline, a `p7012:` IRI). -/
abbrev Agreement := Nat
abbrev Roster := List Agreement

inductive Decision
  | accepted
  | alternative
  | rejected
  deriving DecidableEq, Repr

/-- `myterms/propose` request. `issuer` is the individual's agent, `recipient`
the entity's. `respondsTo` is present only on the one follow-up. -/
structure Req where
  id : ReqId
  issuer : Party
  recipient : Party
  agreement : Agreement
  respondsTo : Option ReqId
  deriving DecidableEq, Repr

/-- `myterms/propose#response`. -/
structure Resp where
  issuer : Party
  decision : Decision
  agreement : Option Agreement
  alternative : Option Agreement
  contractId : Option Nat
  deriving DecidableEq, Repr

/-- The response schema's rule: which members accompany which decision
(§5.3.1 a–c, §5.2.3). -/
def Resp.wf (r : Resp) : Prop :=
  match r.decision with
  | .accepted => r.agreement.isSome ∧ r.contractId.isSome ∧ r.alternative = none
  | .alternative => r.alternative.isSome ∧ r.agreement = none ∧ r.contractId = none
  | .rejected => r.agreement = none ∧ r.alternative = none ∧ r.contractId = none

/-- One step of an engagement: a request and, if the operation was performed,
its response. `none` is a trust-task-error (`notInRoster`, `roundsExhausted`,
`indeterminate`, …): the operation was not performed. -/
abbrev Step := Req × Option Resp
abbrev Run := List Step

/-- The entity may answer request `q` with `r` after history `h`. -/
def Ok (R : Roster) (h : Run) (q : Req) (r : Resp) : Prop :=
  q.agreement ∈ R ∧
  r.wf ∧
  r.issuer = q.recipient ∧
  (r.decision = .accepted → r.agreement = some q.agreement) ∧
  (∀ a, r.alternative = some a → a ∈ R) ∧
  match q.respondsTo with
  | none => True
  | some i =>
      (∃ q0 r0, (q0, some r0) ∈ h ∧ q0.id = i ∧ q0.respondsTo = none ∧
        r0.decision = .alternative ∧ r0.alternative = some q.agreement ∧
        q.issuer = q0.issuer ∧ q.recipient = q0.recipient) ∧
      r.decision ≠ .alternative ∧
      (∀ q1 r1, (q1, some r1) ∈ h → q1.respondsTo ≠ some i)

/-- Admissible runs: every performed step satisfies `Ok`; a refusal performs
nothing and may occur at any point. -/
inductive Adm (R : Roster) : Run → Prop
  | nil : Adm R []
  | perform {h : Run} {q : Req} {r : Resp} :
      Adm R h → Ok R h q r → Adm R (h ++ [(q, some r)])
  | refuse {h : Run} {q : Req} :
      Adm R h → Adm R (h ++ [(q, none)])

/-- Every performed step of an admissible run satisfied `Ok` against some
prefix of the run. -/
theorem performed_ok {R : Roster} {run : Run} (hA : Adm R run) :
    ∀ q r, (q, some r) ∈ run → ∃ h, (∀ s, s ∈ h → s ∈ run) ∧ Ok R h q r := by
  induction hA with
  | nil => intro q r hm; cases hm
  | @perform h q' r' _ hok ih =>
      intro q r hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨h0, hsub, hk⟩ := ih q r hm
        exact ⟨h0, fun s hs => List.mem_append.mpr (Or.inl (hsub s hs)), hk⟩
      · have he : (q, some r) = (q', some r') := List.mem_singleton.mp hm
        cases he
        exact ⟨h, fun s hs => List.mem_append.mpr (Or.inl hs), hok⟩
  | @refuse h q' _ ih =>
      intro q r hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨h0, hsub, hk⟩ := ih q r hm
        exact ⟨h0, fun s hs => List.mem_append.mpr (Or.inl (hsub s hs)), hk⟩
      · have he := List.mem_singleton.mp hm
        cases he

/-! ### The answer to #904's question -/

/-- Under the schema rule, `decision` alone decides whether a contract exists. -/
theorem decision_iff_contract (r : Resp) (hw : r.wf) :
    r.decision = .accepted ↔ r.contractId.isSome := by
  unfold Resp.wf at hw
  constructor
  · intro hd
    rw [hd] at hw
    exact hw.2.1
  · intro hc
    cases hdec : r.decision with
    | accepted => rfl
    | alternative =>
        rw [hdec] at hw
        rw [hw.2.2] at hc
        cases hc
    | rejected =>
        rw [hdec] at hw
        rw [hw.2.2] at hc
        cases hc

/-- Reading the one member `decision = accepted` on a performed step gives:
a contract identifier, an agreement equal to the one the request named, and
that agreement in the roster. -/
theorem decision_member_suffices {R : Roster} {run : Run} (hA : Adm R run)
    {q : Req} {r : Resp} (hm : (q, some r) ∈ run) (hd : r.decision = .accepted) :
    r.contractId.isSome ∧ r.agreement = some q.agreement ∧ q.agreement ∈ R := by
  obtain ⟨_, _, hR, hw, _, hacc, _, _⟩ := performed_ok hA q r hm
  exact ⟨(decision_iff_contract r hw).mp hd, hacc hd, hR⟩

/-- Completion as #904's ceremony states it today: the seal step has a
response. -/
def completesByPresence (run : Run) : Prop := ∃ q r, (q, some r) ∈ run

/-- Completion reading the closed `decision` member. -/
def completesByDecision (run : Run) : Prop :=
  ∃ q r, (q, some r) ∈ run ∧ r.decision = .accepted

/-- A rejected proposal: admissible, complete by presence, and no contract. -/
def rejectedRun : Run :=
  [({ id := 1, issuer := 10, recipient := 20, agreement := 7, respondsTo := none },
    some { issuer := 20, decision := .rejected, agreement := none,
           alternative := none, contractId := none })]

theorem rejectedRun_adm : Adm [7, 8] rejectedRun := by
  have := Adm.perform (R := [7, 8]) (h := []) Adm.nil
    (q := { id := 1, issuer := 10, recipient := 20, agreement := 7, respondsTo := none })
    (r := { issuer := 20, decision := .rejected, agreement := none,
            alternative := none, contractId := none })
    (by
      refine ⟨by decide, ?_, rfl, ?_, ?_, trivial⟩
      · exact ⟨rfl, rfl, rfl⟩
      · intro h; cases h
      · intro a h; cases h)
  simpa [rejectedRun] using this

/-- Presence-only completion accepts an engagement in which nothing was
agreed: the completion check must read `decision`. -/
theorem presence_completion_unsound :
    Adm [7, 8] rejectedRun ∧ completesByPresence rejectedRun ∧
      ¬ ∃ q r, (q, some r) ∈ rejectedRun ∧ r.contractId.isSome := by
  refine ⟨rejectedRun_adm, ⟨_, _, List.mem_singleton.mpr rfl⟩, ?_⟩
  rintro ⟨q, r, hm, hc⟩
  have he := List.mem_singleton.mp hm
  cases he
  cases hc

/-! ### One round (§5.2.2) and who may take the alternative -/

/-- A performed follow-up was made by the original proposer, to the same
entity, takes exactly the alternative that entity offered, and is not itself
answered with another alternative. -/
theorem followup_bound {R : Roster} {run : Run} (hA : Adm R run)
    {q : Req} {r : Resp} {i : ReqId} (hm : (q, some r) ∈ run) (hi : q.respondsTo = some i) :
    (∃ q0 r0, (q0, some r0) ∈ run ∧ q0.id = i ∧ r0.decision = .alternative ∧
      r0.alternative = some q.agreement ∧ q.issuer = q0.issuer ∧ q.recipient = q0.recipient) ∧
    r.decision ≠ .alternative := by
  obtain ⟨h, hsub, _, _, _, _, _, hf⟩ := performed_ok hA q r hm
  rw [hi] at hf
  obtain ⟨⟨q0, r0, h0, hid, _, hd, halt, hiss, hrec⟩, hna, _⟩ := hf
  exact ⟨⟨q0, r0, hsub _ h0, hid, hd, halt, hiss, hrec⟩, hna⟩

/-- Performed follow-ups to request `i`. -/
def followups (i : ReqId) (run : Run) : List Step :=
  run.filter (fun s => s.2.isSome && s.1.respondsTo == some i)

/-- At most one follow-up is performed per answered request. -/
theorem at_most_one_followup {R : Roster} {run : Run} (hA : Adm R run) (i : ReqId) :
    (followups i run).length ≤ 1 := by
  induction hA with
  | nil => simp [followups]
  | @perform h q r _ hok ih =>
      unfold followups at ih ⊢
      rw [List.filter_append, List.length_append]
      by_cases hq : q.respondsTo = some i
      · obtain ⟨_, _, _, _, _, hf⟩ := hok
        rw [hq] at hf
        obtain ⟨_, _, hnone⟩ := hf
        have hempty : h.filter (fun s => s.2.isSome && s.1.respondsTo == some i) = [] := by
          rw [List.filter_eq_nil_iff]
          intro s hs
          rcases s with ⟨q1, o1⟩
          cases o1 with
          | none => simp
          | some r1 =>
              have := hnone q1 r1 hs
              simp [this]
        rw [hempty]
        simp [hq]
      · have : [(q, some r)].filter (fun s => s.2.isSome && s.1.respondsTo == some i) = [] := by
          simp [hq]
        rw [this]
        simpa using ih
  | @refuse h q _ ih =>
      unfold followups at ih ⊢
      rw [List.filter_append, List.length_append]
      simpa using ih

/-! ### Counter-deployments: each rule is needed -/

/-- `Ok` without the issuer binding on the follow-up. -/
def OkNoIssuer (R : Roster) (h : Run) (q : Req) (r : Resp) : Prop :=
  q.agreement ∈ R ∧ r.wf ∧ r.issuer = q.recipient ∧
  (r.decision = .accepted → r.agreement = some q.agreement) ∧
  (∀ a, r.alternative = some a → a ∈ R) ∧
  match q.respondsTo with
  | none => True
  | some i =>
      (∃ q0 r0, (q0, some r0) ∈ h ∧ q0.id = i ∧ q0.respondsTo = none ∧
        r0.decision = .alternative ∧ r0.alternative = some q.agreement ∧
        q.recipient = q0.recipient) ∧
      r.decision ≠ .alternative ∧
      (∀ q1 r1, (q1, some r1) ∈ h → q1.respondsTo ≠ some i)

def offerReq : Req := { id := 1, issuer := 10, recipient := 20, agreement := 7, respondsTo := none }
def offerResp : Resp :=
  { issuer := 20, decision := .alternative, agreement := none, alternative := some 8, contractId := none }
def offerToTen : Step := (offerReq, some offerResp)

/-- A third party (30) takes the alternative offered to party 10. -/
def hijack : Req := { id := 2, issuer := 30, recipient := 20, agreement := 8, respondsTo := some 1 }
def hijackResp : Resp :=
  { issuer := 20, decision := .accepted, agreement := some 8, alternative := none, contractId := some 99 }

/-- Without the issuer binding, the entity may record a contract with a party
that never proposed: the alternative offered to one individual is accepted on
behalf of another. With it, `Ok` refuses the same step. -/
theorem issuer_binding_needed :
    OkNoIssuer [7, 8] [offerToTen] hijack hijackResp ∧
    ¬ Ok [7, 8] [offerToTen] hijack hijackResp := by
  constructor
  · refine ⟨by decide, ⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, ?_, ?_⟩
    · intro a h; cases h
    · refine ⟨⟨offerToTen.1, _, List.mem_singleton.mpr rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
      · intro h; cases h
      · intro q1 r1 hm
        have he := List.mem_singleton.mp hm
        cases he
        intro h; cases h
  · rintro ⟨_, _, _, _, _, ⟨q0, r0, hm, _, _, _, _, hiss, _⟩, _, _⟩
    have he := List.mem_singleton.mp hm
    cases he
    cases hiss

/-- `Ok` without the one-follow-up rule. -/
def OkNoRounds (R : Roster) (h : Run) (q : Req) (r : Resp) : Prop :=
  q.agreement ∈ R ∧ r.wf ∧ r.issuer = q.recipient ∧
  (r.decision = .accepted → r.agreement = some q.agreement) ∧
  (∀ a, r.alternative = some a → a ∈ R) ∧
  match q.respondsTo with
  | none => True
  | some i =>
      (∃ q0 r0, (q0, some r0) ∈ h ∧ q0.id = i ∧ q0.respondsTo = none ∧
        r0.decision = .alternative ∧ r0.alternative = some q.agreement ∧
        q.issuer = q0.issuer ∧ q.recipient = q0.recipient) ∧
      r.decision ≠ .alternative

def take1Req : Req := { id := 2, issuer := 10, recipient := 20, agreement := 8, respondsTo := some 1 }
def take1Resp : Resp :=
  { issuer := 20, decision := .rejected, agreement := none, alternative := none, contractId := none }
def take1 : Step := (take1Req, some take1Resp)
def take2 : Req := { id := 3, issuer := 10, recipient := 20, agreement := 8, respondsTo := some 1 }
def take2Resp : Resp :=
  { issuer := 20, decision := .accepted, agreement := some 8, alternative := none, contractId := some 5 }

/-- Without the one-follow-up rule a second follow-up to the same answer is
performed: a rejected follow-up is retried until accepted, which is the
negotiation §5.2.2 rules out. With it, `Ok` refuses the retry. -/
theorem round_limit_needed :
    OkNoRounds [7, 8] [offerToTen, take1] take2 take2Resp ∧
    ¬ Ok [7, 8] [offerToTen, take1] take2 take2Resp := by
  constructor
  · refine ⟨by decide, ⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, ?_, ?_⟩
    · intro a h; cases h
    · refine ⟨⟨offerReq, offerResp, List.mem_cons_self .., rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
      intro h; cases h
  · rintro ⟨_, _, _, _, _, _, _, hnone⟩
    exact hnone take1Req take1Resp (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)) rfl

/-! ### The ceremony: comprehension in front of the agreement -/

/-- A comprehension exchange (`understanding/exchange`, its own family): who
answered, who recorded the outcome, and whether it showed understanding. -/
structure Exchange where
  issuer : Party
  recipient : Party
  understood : Bool
  deriving DecidableEq, Repr

/-- The ceremony's completion: a passed exchange, and an accepted proposal
between the same two parties. -/
def ceremonyComplete (x : Exchange) (run : Run) : Prop :=
  x.understood = true ∧
  ∃ q r, (q, some r) ∈ run ∧ r.decision = .accepted ∧
    q.issuer = x.issuer ∧ q.recipient = x.recipient

/-- Completion yields a contract between the party that showed understanding
and the party that recorded it, for an agreement in the roster. -/
theorem ceremony_sound {R : Roster} {run : Run} (hA : Adm R run) {x : Exchange}
    (hc : ceremonyComplete x run) :
    ∃ q r, (q, some r) ∈ run ∧ r.contractId.isSome ∧ q.agreement ∈ R ∧
      q.issuer = x.issuer ∧ q.recipient = x.recipient ∧ x.understood = true := by
  obtain ⟨hu, q, r, hm, hd, hi, hr⟩ := hc
  obtain ⟨hcid, _, hR⟩ := decision_member_suffices hA hm hd
  exact ⟨q, r, hm, hcid, hR, hi, hr, hu⟩

/-- Completion without binding the exchange's parties to the proposal's: an
exchange passed by one party (11) completes a ceremony for an agreement
proposed by another (10), so the contract holder never showed understanding. -/
def acceptedRun : Run :=
  [({ id := 1, issuer := 10, recipient := 20, agreement := 7, respondsTo := none },
    some { issuer := 20, decision := .accepted, agreement := some 7,
           alternative := none, contractId := some 3 })]

def ceremonyCompleteUnbound (x : Exchange) (run : Run) : Prop :=
  x.understood = true ∧ ∃ q r, (q, some r) ∈ run ∧ r.decision = .accepted

theorem exchange_binding_needed :
    ceremonyCompleteUnbound ⟨11, 20, true⟩ acceptedRun ∧
    ¬ ceremonyComplete ⟨11, 20, true⟩ acceptedRun := by
  constructor
  · exact ⟨rfl, _, _, List.mem_singleton.mpr rfl, rfl⟩
  · rintro ⟨_, q, r, hm, _, hi, _⟩
    have he := List.mem_singleton.mp hm
    cases he
    cases hi

/-! ### Non-vacuity: the soundness theorems apply to a full engagement -/

/-- Propose 7 → alternative 8 → follow-up taking 8 → accepted. -/
def fullRun : Run :=
  [offerToTen,
   ({ id := 2, issuer := 10, recipient := 20, agreement := 8, respondsTo := some 1 },
    some { issuer := 20, decision := .accepted, agreement := some 8,
           alternative := none, contractId := some 42 })]

theorem fullRun_adm : Adm [7, 8] fullRun := by
  have h1 : Adm [7, 8] [offerToTen] := by
    have := Adm.perform (R := [7, 8]) (h := []) Adm.nil (q := offerReq) (r := offerResp)
      (by
        refine ⟨by decide, ⟨rfl, rfl, rfl⟩, rfl, ?_, ?_, trivial⟩
        · intro h; cases h
        · intro a h; cases h; decide)
    exact this
  have := Adm.perform (R := [7, 8]) h1
    (q := { id := 2, issuer := 10, recipient := 20, agreement := 8, respondsTo := some 1 })
    (r := { issuer := 20, decision := .accepted, agreement := some 8,
            alternative := none, contractId := some 42 })
    (by
      refine ⟨by decide, ⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, ?_, ?_⟩
      · intro a h; cases h
      · refine ⟨⟨offerToTen.1, _, List.mem_singleton.mpr rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
        · intro h; cases h
        · intro q1 r1 hm
          have he := List.mem_singleton.mp hm
          cases he
          intro h; cases h)
  simpa [fullRun] using this

theorem ceremony_sound_nonvacuous :
    ∃ q r, (q, some r) ∈ fullRun ∧ r.contractId.isSome ∧ q.agreement ∈ [7, 8] ∧
      q.issuer = 10 ∧ q.recipient = 20 := by
  have hc : ceremonyComplete ⟨10, 20, true⟩ fullRun :=
    ⟨rfl, { id := 2, issuer := 10, recipient := 20, agreement := 8, respondsTo := some 1 },
      { issuer := 20, decision := .accepted, agreement := some 8, alternative := none, contractId := some 42 },
      List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl), rfl, rfl, rfl⟩
  obtain ⟨q, r, hm, hcid, hR, hi, hr, _⟩ := ceremony_sound fullRun_adm hc
  exact ⟨q, r, hm, hcid, hR, hi, hr⟩

end TrustTasks.MyTerms
