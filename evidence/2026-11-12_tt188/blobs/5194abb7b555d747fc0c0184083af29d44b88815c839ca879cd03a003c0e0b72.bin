/-
Counting vetting statements toward admission (upstream
trustoverip/dtgwg-trust-tasks-tf main, 101a51d8d).

Rules, quoted:

* `vtc/join-requests/manifest/0.4`, vetting table: `minStatements`
  "Statements needed, counting each vetter once however many DIDs they hold";
  `minByMethod` "Per-method floors within `minStatements`"; `acceptedMethods`
  "Methods whose statements count at all"; `maxStatementAge` "A statement
  older than this at decision time does not count"; `eligibleVetters.role`
  "The role a statement's issuer must hold for it to count"; `independence`
  "Caps per declared vetter–applicant relationship …; whether all statements
  must carry the same identity commitment". Its schema:
  `maxByDeclaredRelationship` "The most counted statements that may come from
  vetters declaring each relationship"; `requireConsistentIdentityCommitment`
  "every counted statement must carry the same identity commitment".
* `vetting/session/0.1` (statement profile): with a `pairwise` issuer scope "a
  community **MUST NOT** count a statement that declares one".
* `vtc/vetting/revoke-statement/0.1`, community items 2, 3, 4 and 7: a notice
  for a held statement is refused on `issuerMismatch` or `digestMismatch`;
  "Otherwise **MUST** record the notice, keyed by `statementId` and
  `statementDigestMultibase`, together with the sender … A notice for a
  statement the community has not yet seen is recorded all the same"; a
  statement does not count "whenever it holds a notice whose `statementId`,
  digest and sender all match the statement's `id`, digest and `issuer`. A
  notice matching on some of these and not all has no effect"; "On a repeated
  notice for a statement it has already recorded, **MUST** return the original
  `recordedAt` and change nothing."
* `vtc/join-requests/vetting/show/0.1` records the decision's facts:
  per statement `counted`, and over them `commitmentsConsistent` ("Every
  counted statement carries the same identity commitment"), `independenceOk`
  ("No declared-relationship cap was exceeded") and `satisfied` ("Count,
  method floors, consistency and independence all held").

Shown: a satisfied requirement gives at least `minStatements` distinct
vetters, each with a statement that is eligible, of an accepted method, within
age, not pairwise and not withdrawn by a matching notice; each of those rules
is needed; and a manifest whose `minByMethod` names a method not in
`acceptedMethods` is unsatisfiable, as `manifest/0.4` community item 4 and
applicant item 1 already say (a confirmation, not a defect).

Two defects. (1) The caps and the commitment rule are stated over "counted"
statements, and `vetting/show/0.1` records them as checks that can fail over
everything that passed the per-statement rules. Read that way, presenting one
more eligible statement (a vetter declaring `family` under `family: 0`, or one
whose commitment differs) turns a satisfied application into an unsatisfied
one, although the applicant cannot see eligibility ("current vetter
eligibility … is visible only to the community", `manifest/0.4` applicant
item 1). Read as "some set of counted statements meets every check", it is
monotone and as sound. (2) With item 3's key (`statementId`, digest) as what
makes a notice "repeated" (item 7), a notice for a statement not yet seen,
sent by another present or former member holding the statement, takes the
key; the issuer's own notice is then a repeat, changes nothing, and the
statement keeps counting. Keying item 7 on all three of item 4's fields
makes the issuer's notice always take effect.

Not modelled: signatures, digests as computed (taken as opaque numbers),
`statementType`, `requiredClaims` beyond the commitment, document classes,
invitations, hidden vetting, time beyond a statement's age, how the community
links a vetter's DIDs (`owner` is given; it agrees with the true person on
every non-pairwise DID), and re-evaluation of pending applications (item 5).
Two held statements with one `id` are assumed not to occur.
-/

namespace TrustTasks.VettingCount

inductive Method
  | inPerson
  | video
  | priorAcquaintance
  deriving DecidableEq, Repr

inductive Relationship
  | none
  | communityColleague
  | sameEmployer
  | family
  | otherPersonal
  deriving DecidableEq, Repr

inductive Scope
  | pairwise
  | directed
  | «public»
  deriving DecidableEq, Repr

def allMethods : List Method := [.inPerson, .video, .priorAcquaintance]
def allRelationships : List Relationship :=
  [.none, .communityColleague, .sameEmployer, .family, .otherPersonal]

theorem mem_allMethods (m : Method) : m ∈ allMethods := by cases m <;> simp [allMethods]
theorem mem_allRelationships (r : Relationship) : r ∈ allRelationships := by
  cases r <;> simp [allRelationships]

/-- A presented Vetting Statement. DIDs, ids, digests and commitments are
numbers. -/
structure Statement where
  id : Nat
  digest : Nat
  issuer : Nat
  scope : Scope
  method : Method
  rel : Relationship
  commitment : Nat
  /-- Age at decision time. -/
  age : Nat
  deriving DecidableEq, Repr

/-- A `revoke-statement` notice. -/
structure Notice where
  sid : Nat
  digest : Nat
  sender : Nat
  deriving DecidableEq, Repr

/-- A criterion's `vetting` object. -/
structure Vetting where
  minStatements : Nat
  minByMethod : Method → Nat
  accepted : Method → Bool
  maxAge : Option Nat
  cap : Relationship → Option Nat
  consistent : Bool

/-- What the community holds when it decides. -/
structure Ctx where
  /-- The DID holds the community's VAC for the eligible role. -/
  eligible : Nat → Bool
  /-- The vetter the community takes a DID to belong to. -/
  owner : Nat → Nat
  notices : List Notice

/-- The rules, each switchable so its need can be shown. -/
structure Rules where
  perVetter : Bool
  method : Bool
  age : Bool
  eligible : Bool
  scope : Bool
  /-- Item 4: a notice must match on sender as well as id and digest. -/
  matchSender : Bool

def spec : Rules := ⟨true, true, true, true, true, true⟩

def noticeMatches (r : Rules) (s : Statement) (n : Notice) : Bool :=
  n.sid == s.id && n.digest == s.digest && (!r.matchSender || n.sender == s.issuer)

def withdrawn (r : Rules) (ns : List Notice) (s : Statement) : Bool := ns.any (noticeMatches r s)

def ageOk (V : Vetting) (s : Statement) : Bool :=
  match V.maxAge with
  | none => true
  | some m => Nat.ble s.age m

/-- The per-statement rules. -/
def counts (r : Rules) (V : Vetting) (c : Ctx) (s : Statement) : Bool :=
  (!r.method || V.accepted s.method) && (!r.age || ageOk V s) &&
    (!r.eligible || c.eligible s.issuer) && (!r.scope || s.scope != .pairwise) &&
    !withdrawn r c.notices s

def dedup : List Nat → List Nat
  | [] => []
  | x :: xs => if xs.contains x then dedup xs else x :: dedup xs

/-- How many count: distinct vetters, or (rule off) statements. -/
def units (r : Rules) (c : Ctx) (T : List Statement) : Nat :=
  if r.perVetter then (dedup (T.map (fun s => c.owner s.issuer))).length else T.length

def allSame : List Nat → Bool
  | [] => true
  | x :: xs => xs.all (· == x)

def capOk (T : List Statement) (ρ : Relationship) : Option Nat → Bool
  | none => true
  | some k => Nat.ble (T.filter (fun s => s.rel == ρ)).length k

/-- Count, method floors, independence caps and consistency, over a set `T`
of statements taken as counted. -/
def checks (r : Rules) (V : Vetting) (c : Ctx) (T : List Statement) : Bool :=
  Nat.ble V.minStatements (units r c T) &&
    allMethods.all (fun m => Nat.ble (V.minByMethod m) (units r c (T.filter (·.method == m)))) &&
    allRelationships.all (fun ρ => capOk T ρ (V.cap ρ)) &&
    (!V.consistent || allSame (T.map (·.commitment)))

/-- Reading 1 (`vetting/show/0.1`): the checks over every statement that
passes the per-statement rules. -/
def globalSat (r : Rules) (V : Vetting) (c : Ctx) (ss : List Statement) : Bool :=
  checks r V c (ss.filter (counts r V c))

/-- Reading 2: some set of statements that pass the per-statement rules meets
every check. -/
def SubsetSat (r : Rules) (V : Vetting) (c : Ctx) (ss : List Statement) : Prop :=
  ∃ T, T.Sublist (ss.filter (counts r V c)) ∧ checks r V c T = true

/-! ### Soundness -/

theorem mem_dedup {x : Nat} {l : List Nat} : x ∈ dedup l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons y ys ih =>
      unfold dedup
      by_cases h : ys.contains y = true
      · rw [if_pos h, ih]
        have hy : y ∈ ys := by simpa using h
        constructor
        · intro hx; exact List.mem_cons_of_mem _ hx
        · intro hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hy
          · exact hx
      · rw [if_neg h]; simp [ih]

theorem nodup_dedup (l : List Nat) : (dedup l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons y ys ih =>
      unfold dedup
      by_cases h : ys.contains y = true
      · rw [if_pos h]; exact ih
      · rw [if_neg h]
        refine List.nodup_cons.mpr ⟨?_, ih⟩
        intro hy
        exact h (by simpa using mem_dedup.mp hy)

/-- What one counted statement is, under the rules as written. -/
theorem counts_spec {V : Vetting} {c : Ctx} {s : Statement} (h : counts spec V c s = true) :
    V.accepted s.method = true ∧ ageOk V s = true ∧ c.eligible s.issuer = true ∧
      s.scope ≠ .pairwise ∧
      ∀ n ∈ c.notices, ¬ (n.sid = s.id ∧ n.digest = s.digest ∧ n.sender = s.issuer) := by
  simp only [counts, spec, Bool.not_true, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun n hn ⟨e1, e2, e3⟩ => ?_⟩
  have : withdrawn spec c.notices s = true :=
    List.any_eq_true.mpr ⟨n, hn, by simp [noticeMatches, spec, e1, e2, e3]⟩
  exact Bool.false_ne_true (h5.symm.trans this)

/-- Any set of counted statements meeting the checks gives `minStatements`
distinct vetters, each with a counted statement among those presented. -/
theorem checks_sound {V : Vetting} {c : Ctx} {ss T : List Statement}
    (hT : T.Sublist (ss.filter (counts spec V c))) (h : checks spec V c T = true) :
    ∃ vs : List Nat, vs.Nodup ∧ V.minStatements ≤ vs.length ∧
      ∀ v ∈ vs, ∃ s ∈ ss, c.owner s.issuer = v ∧ counts spec V c s = true := by
  simp only [checks, Bool.and_eq_true] at h
  refine ⟨dedup (T.map (fun s => c.owner s.issuer)), nodup_dedup _, ?_, ?_⟩
  · have := h.1.1.1
    simp only [units, spec, if_true] at this
    exact Nat.le_of_ble_eq_true this
  · intro v hv
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (mem_dedup.mp hv)
    have hs' := hT.subset hs
    obtain ⟨hss, hc⟩ := List.mem_filter.mp hs'
    exact ⟨s, hss, rfl, hc⟩

/-- Soundness, reading 1: a satisfied requirement gives `minStatements`
distinct vetters with a counted statement each, and (`counts_spec`) every
counted statement is eligible, of an accepted method, in age, not pairwise
and not withdrawn by a matching notice. -/
theorem global_sound {V : Vetting} {c : Ctx} {ss : List Statement}
    (h : globalSat spec V c ss = true) :
    ∃ vs : List Nat, vs.Nodup ∧ V.minStatements ≤ vs.length ∧
      ∀ v ∈ vs, ∃ s ∈ ss, c.owner s.issuer = v ∧ counts spec V c s = true :=
  checks_sound (List.Sublist.refl _) h

/-- Soundness, reading 2. -/
theorem subset_sound {V : Vetting} {c : Ctx} {ss : List Statement} (h : SubsetSat spec V c ss) :
    ∃ vs : List Nat, vs.Nodup ∧ V.minStatements ≤ vs.length ∧
      ∀ v ∈ vs, ∃ s ∈ ss, c.owner s.issuer = v ∧ counts spec V c s = true :=
  let ⟨_, hT, hc⟩ := h; checks_sound hT hc

/-- The vetters are distinct people, not only distinct as the community sees
them, wherever the community's linking of DIDs is right on non-pairwise
DIDs: the pairwise rule is what makes that assumption enough. -/
theorem global_sound_persons {V : Vetting} {c : Ctx} {ss : List Statement}
    (person : Nat → Nat)
    (hlink : ∀ s ∈ ss, s.scope ≠ .pairwise → person s.issuer = c.owner s.issuer)
    (h : globalSat spec V c ss = true) :
    ∃ vs : List Nat, vs.Nodup ∧ V.minStatements ≤ vs.length ∧
      ∀ v ∈ vs, ∃ s ∈ ss, person s.issuer = v ∧ counts spec V c s = true := by
  obtain ⟨vs, hn, hl, hv⟩ := global_sound h
  refine ⟨vs, hn, hl, fun v hmem => ?_⟩
  obtain ⟨s, hs, ho, hc⟩ := hv v hmem
  exact ⟨s, hs, by rw [hlink s hs (counts_spec hc).2.2.2.1, ho], hc⟩

/-- A notice from anyone but the statement's issuer never withdraws it. -/
theorem third_party_notice_no_effect (s : Statement) (n : Notice) (h : n.sender ≠ s.issuer) :
    noticeMatches spec s n = false := by
  simp [noticeMatches, spec, h]

/-! ### Each rule is needed -/

/-- The example criterion of `manifest/0.4` (`minStatements` 2, `inPerson` 1,
`family` 0, `sameEmployer` 1, consistent commitments, `P120D`). -/
def example4 : Vetting where
  minStatements := 2
  minByMethod := fun m => if m = .inPerson then 1 else 0
  accepted := fun _ => true
  maxAge := some 120
  cap := fun ρ => if ρ = .family then some 0 else if ρ = .sameEmployer then some 1 else none
  consistent := true

/-- Two vetters (DIDs 1, 2) eligible; DID 3 eligible too. -/
def ctx0 : Ctx := ⟨fun d => d == 1 || d == 2 || d == 3, fun d => d, []⟩

def st (id issuer : Nat) (m : Method) (ρ : Relationship) (cm : Nat) : Statement :=
  ⟨id, id + 100, issuer, .directed, m, ρ, cm, 10⟩

def good : List Statement := [st 1 1 .inPerson .none 7, st 2 2 .video .none 7]

/-- Nonvacuity: the example criterion is met by two vetters, under both
readings. -/
theorem nonvacuous : globalSat spec example4 ctx0 good = true ∧ SubsetSat spec example4 ctx0 good :=
  ⟨by decide, ⟨_, List.Sublist.refl _, by decide⟩⟩

/-- One vetter holding two DIDs meets a minimum of two when statements, not
vetters, are counted. -/
theorem perVetter_needed :
    let c : Ctx := ⟨fun _ => true, fun _ => 1, []⟩
    let ss := [st 1 1 .inPerson .none 7, st 2 2 .video .none 7]
    globalSat spec example4 c ss = false ∧
      globalSat { spec with perVetter := false } example4 c ss = true := by
  decide

/-- The eligibility, method and age rules are each needed: a statement
failing only that rule makes up the count without it. -/
theorem filters_needed :
    let V : Vetting := { example4 with accepted := fun m => m != .video }
    let bad1 := [st 1 1 .inPerson .none 7, st 2 9 .video .none 7]   -- DID 9 not eligible
    let bad2 := [st 1 1 .inPerson .none 7, st 2 2 .video .none 7]   -- `video` not accepted
    let bad3 := [st 1 1 .inPerson .none 7, ⟨2, 102, 2, .directed, .video, .none, 7, 400⟩]
    globalSat spec example4 ctx0 bad1 = false ∧
      globalSat { spec with eligible := false } example4 ctx0 bad1 = true ∧
    globalSat spec V ctx0 bad2 = false ∧
      globalSat { spec with method := false } V ctx0 bad2 = true ∧
    globalSat spec example4 ctx0 bad3 = false ∧
      globalSat { spec with age := false } example4 ctx0 bad3 = true := by
  decide

/-- The pairwise rule is needed: one person's member DID (1) and pairwise DID
(2), which the community cannot link, count as two vetters without it. -/
theorem pairwise_needed :
    let ss := [st 1 1 .inPerson .none 7, ⟨2, 102, 2, .pairwise, .video, .none, 7, 10⟩]
    globalSat spec example4 ctx0 ss = false ∧
      globalSat { spec with scope := false } example4 ctx0 ss = true := by
  decide

/-- Item 4's sender match is needed: a third party's notice naming a
statement's id and digest removes it otherwise. -/
theorem matchSender_needed :
    let c : Ctx := { ctx0 with notices := [⟨2, 102, 5⟩] }
    globalSat spec example4 c good = true ∧
      globalSat { spec with matchSender := false } example4 c good = false := by
  decide

/-- The issuer's own notice does withdraw. -/
theorem issuer_notice_withdraws :
    let c : Ctx := { ctx0 with notices := [⟨2, 102, 2⟩] }
    globalSat spec example4 c good = false := by
  decide

/-! ### Confirmation: a floor on a method not accepted -/

/-- A `minByMethod` floor of at least one on a method outside
`acceptedMethods` can never be met, under either reading: what
`manifest/0.4` community item 4 forbids publishing and applicant item 1
treats as unsatisfiable. -/
theorem floor_outside_accepted_unsat {V : Vetting} {c : Ctx} {ss : List Statement}
    {m : Method} (hm : V.accepted m = false) (hf : 1 ≤ V.minByMethod m) :
    ¬ SubsetSat spec V c ss := by
  rintro ⟨T, hT, h⟩
  simp only [checks, Bool.and_eq_true] at h
  have hfl := List.all_eq_true.mp h.1.1.2 m (mem_allMethods m)
  have hempty : T.filter (·.method == m) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    have hc := (List.mem_filter.mp (hT.subset hs)).2
    have hacc := (counts_spec hc).1
    intro heq
    have : s.method = m := by simpa using heq
    rw [this, hm] at hacc
    cases hacc
  rw [hempty] at hfl
  simp [units, spec, dedup] at hfl
  omega

theorem floor_outside_accepted_unsat_global {V : Vetting} {c : Ctx} {ss : List Statement}
    {m : Method} (hm : V.accepted m = false) (hf : 1 ≤ V.minByMethod m) :
    globalSat spec V c ss = false := by
  cases h : globalSat spec V c ss
  · rfl
  · exact absurd ⟨_, List.Sublist.refl _, h⟩ (floor_outside_accepted_unsat hm hf)

/-! ### Defect 1: the caps and the commitment rule over every counted statement -/

/-- Reading 1 is not monotone: one more eligible statement, from a vetter
declaring `family` under `family: 0`, or carrying another commitment, turns a
satisfied application into an unsatisfied one. Reading 2 still holds. -/
theorem global_not_monotone :
    let fam := st 3 3 .video .family 7
    let other := st 3 3 .video .none 8
    globalSat spec example4 ctx0 good = true ∧
    globalSat spec example4 ctx0 (good ++ [fam]) = false ∧
    globalSat spec example4 ctx0 (good ++ [other]) = false ∧
    SubsetSat spec example4 ctx0 (good ++ [fam]) ∧
    SubsetSat spec example4 ctx0 (good ++ [other]) :=
  ⟨by decide, by decide, by decide,
   ⟨good, by decide, by decide⟩, ⟨good, by decide, by decide⟩⟩

/-- Reading 2 is monotone: presenting more never loses a satisfied
requirement. -/
theorem subset_monotone {r : Rules} {V : Vetting} {c : Ctx} {ss ss' : List Statement}
    (hs : ss.Sublist ss') (h : SubsetSat r V c ss) : SubsetSat r V c ss' :=
  let ⟨T, hT, hc⟩ := h; ⟨T, hT.trans (hs.filter _), hc⟩

/-- And it accepts everything reading 1 accepts. -/
theorem global_implies_subset {r : Rules} {V : Vetting} {c : Ctx} {ss : List Statement}
    (h : globalSat r V c ss = true) : SubsetSat r V c ss :=
  ⟨_, List.Sublist.refl _, h⟩

/-! ### Defect 2: a notice that takes the key first -/

/-- Community items 1, 2, 3 and 7. `key` says when a stored notice makes `n`
a repeat. `none`: refused. -/
def receive (key : Notice → Notice → Bool) (member : Nat → Bool) (held : List Statement)
    (store : List Notice) (n : Notice) : Option (List Notice) :=
  if member n.sender = false then none
  else if held.any (fun s => s.id == n.sid && (s.issuer != n.sender || s.digest != n.digest))
  then none
  else if store.any (key n) then some store
  else some (n :: store)

/-- Item 3's key. -/
def keyItem3 (n m : Notice) : Bool := n.sid == m.sid && n.digest == m.digest

/-- The fix: item 4's three fields. -/
def keyFull (n m : Notice) : Bool := keyItem3 n m && n.sender == m.sender

def vStmt : Statement := st 2 2 .video .none 7

/-- Another member (5) holding the statement sends a notice for it before it
is submitted; the issuer's (2) notice, before or after submission, is then a
repeat, and the statement still counts. -/
theorem squat_swallows_withdrawal :
    let member : Nat → Bool := fun d => d == 2 || d == 5
    let squat : Notice := ⟨vStmt.id, vStmt.digest, 5⟩
    let own : Notice := ⟨vStmt.id, vStmt.digest, vStmt.issuer⟩
    receive keyItem3 member [] [] squat = some [squat] ∧
    receive keyItem3 member [] [squat] own = some [squat] ∧
    receive keyItem3 member [vStmt] [squat] own = some [squat] ∧
    globalSat spec example4 { ctx0 with notices := [squat] } good = true := by
  decide

/-- With `keyFull`, the issuer's notice for its own statement always takes
effect, whatever was recorded before. -/
theorem keyFull_issuer_effective (member : Nat → Bool) (held : List Statement)
    (store : List Notice) (s : Statement) (hm : member s.issuer = true)
    (hheld : ∀ h ∈ held, h.id = s.id → h.issuer = s.issuer ∧ h.digest = s.digest) :
    ∃ store', receive keyFull member held store ⟨s.id, s.digest, s.issuer⟩ = some store' ∧
      withdrawn spec store' s = true := by
  have hany : held.any (fun h => h.id == s.id &&
      (h.issuer != s.issuer || h.digest != s.digest)) = false := by
    cases ha : held.any (fun h => h.id == s.id &&
        (h.issuer != s.issuer || h.digest != s.digest))
    · rfl
    · obtain ⟨h, hh, hb⟩ := List.any_eq_true.mp ha
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hb
      obtain ⟨e1, e2⟩ := hheld h hh hb.1
      rcases hb.2 with hb | hb <;> exact absurd (by assumption) hb
  unfold receive
  simp only [hm, hany]
  cases hs : store.any (keyFull ⟨s.id, s.digest, s.issuer⟩)
  · refine ⟨⟨s.id, s.digest, s.issuer⟩ :: store, by simp, ?_⟩
    simp [withdrawn, noticeMatches, spec]
  · refine ⟨store, by simp, ?_⟩
    obtain ⟨m, hm', hk⟩ := List.any_eq_true.mp hs
    simp only [keyFull, keyItem3, Bool.and_eq_true, beq_iff_eq] at hk
    obtain ⟨⟨e1, e2⟩, e3⟩ := hk
    exact List.any_eq_true.mpr ⟨m, hm', by simp [noticeMatches, spec, ← e1, ← e2, ← e3]⟩

/-- `keyFull` keeps item 7: a repeated notice from the same sender changes
nothing. -/
theorem keyFull_idempotent (member : Nat → Bool) (held : List Statement)
    (store : List Notice) (n : Notice) (store' : List Notice)
    (h : receive keyFull member held store n = some store') :
    receive keyFull member held store' n = some store' := by
  unfold receive at h ⊢
  split at h
  · cases h
  · next hm =>
    split at h
    · cases h
    · next hh =>
      rw [if_neg hm, if_neg hh]
      split at h
      · cases h; next hs => rw [if_pos hs]
      · cases h
        have : (n :: store).any (keyFull n) = true := by
          simp [keyFull, keyItem3]
        rw [if_pos this]

end TrustTasks.VettingCount
