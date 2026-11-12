/-
ACL delegation only narrows, read against upstream
trustoverip/dtgwg-trust-tasks-tf main (101a51d8d): `specs/acl/grant/0.3`,
`acl/change-role/0.3`, `acl/revoke/0.3`, `acl/update/0.3` and
`acl/_shared/0.3/CONVENTIONS.md`.

CONVENTIONS §9: a grant's "resulting entry MUST NOT exceed the granter on any
axis"; "The maintainer records the granter in `delegatedBy`. A delegated entry
**MUST NOT retain authority its delegator has since lost**: when the
delegator's entry narrows or is removed, the maintainer re-evaluates the
entries it delegated — withdrawing, narrowing, or queuing them for review
under its own policy — and MUST NOT leave them in force by default."
grant/0.3 consumer item 4 (the bound), item 5 ("Refuse a grant whose subject
is the granter itself"), item 9 ("Re-evaluate the entry whenever the
`delegatedBy` granter's own entry narrows or is removed ... the maintainer's
policy decides whether that withdraws, narrows or queues for review — it
**MUST NOT** silently leave the entry in force"); revoke/0.3 item 6
("Re-evaluate the entries whose `delegatedBy` is the subject"); change-role/0.3
item 5 (likewise); update/0.3 item 5 ("Evaluate the **amended** entry against
the amending party's stored entry"), item 6 (no self-amendment) and item 10
("An amendment does not change `delegatedBy` unless the maintainer's policy
re-delegates the entry to the amending party"). grant/0.3 Definitions:
`delegatedBy` is "The granter whose authority bounds the entry".

What is modelled: entries numbered in creation order, each with one finite
set of capabilities standing for every axis (the bound is per axis, and each
result here needs only one), its `delegatedBy` (an older entry, so the
entries form a forest), and whether it is live. Re-evaluation narrows each
affected entry to what its delegator holds (one of the three outcomes §9
allows; withdrawal is narrowing to nothing). It is triggered for the
delegates of the changed entry and, since their narrowing is itself a
narrowing of a delegator (grant item 9, §9), for theirs in turn.

Results. Under the rules, every entry stays within the entry its
`delegatedBy` names (`within_preserved`), and re-evaluation only touches what
exceeds (`cascade_minimal`). The granter bound and re-evaluation are each
needed; re-evaluating only direct delegates, as revoke item 6 and
change-role item 5 read alone, is not enough (`one_level_insufficient`), but
grant item 9 and §9 already require the transitive re-evaluation, so this is
confirmed, not a defect. The no-self-grant rules (grant item 5, update item
6) play no part here: a self-grant has no subject without a live entry, and
a self-amendment bounded by the amender's own entry can only narrow.

Defect. An amendment is bounded by the amending party, not by the entry's
`delegatedBy`, and does not change `delegatedBy` by default. A conforming
widening by a third party leaves an entry exceeding the entry that is said to
bound it, and when the amending party is then removed, nothing re-evaluates
the widened entry, which keeps authority no live entry delegated to it
(`amend_escapes_delegator`). Bounding the amendment also by the `delegatedBy`
entry restores the invariant (`within_preserved` with `amendBound`).

Reading. §9's "queuing them for review" keeps the invariant only if a queued
entry confers nothing while queued; grant item 9's "MUST NOT silently leave
the entry in force" admits a queued entry left in force with notice, which
retains what its delegator lost (`queued_in_force_retains`).

Not modelled: roles and ceilings, the separate axes and their shapes,
qualifiers and containment, additive capabilities, expiry, purposes, keys,
approve authority, re-delegation permission, `lastAuthorityProtected`,
compare-and-swap, the policy choice between the three outcomes, and
re-delegation on amendment (update item 10's alternative).
-/

namespace TrustTasks.AclDelegation

structure Entry where
  caps : List Nat
  delegatedBy : Option Nat
  live : Bool
  deriving DecidableEq, Repr

/-- The ACL: entry `j` for every number; unused numbers are not live. -/
abbrev Acl := Nat → Entry

def gone : Entry := ⟨[], none, false⟩

/-- The authority an entry confers. -/
def auth (s : Acl) (j : Nat) : List Nat := if (s j).live then (s j).caps else []

def Sub (l m : List Nat) : Prop := ∀ c, c ∈ l → c ∈ m

instance (l m : List Nat) : Decidable (Sub l m) :=
  inferInstanceAs (Decidable (∀ c, c ∈ l → c ∈ m))

/-- The invariant: every entry is within the entry its `delegatedBy` names. -/
def Within (s : Acl) : Prop :=
  ∀ j g, (s j).delegatedBy = some g → Sub (auth s j) (auth s g)

/-- `delegatedBy` names an older entry. -/
def Forest (s : Acl) : Prop := ∀ j g, (s j).delegatedBy = some g → g < j

def set (s : Acl) (i : Nat) (x : Entry) : Acl := fun k => if k = i then x else s k

/-! ### Re-evaluation -/

def underF (s : Acl) (i : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, j =>
      match (s j).delegatedBy with
      | none => false
      | some g => decide (g < j) && (g == i || underF s i n g)

/-- `j` lies strictly below `i` in the delegation forest. -/
def under (s : Acl) (i j : Nat) : Bool := underF s i (j + 1) j

def effF (s : Acl) (i : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, j =>
      match (s j).delegatedBy with
      | none => auth s j
      | some g =>
          if g < j ∧ under s i j = true then (auth s j).filter (fun c => (effF s i n g).contains c)
          else auth s j

/-- After entry `i` changes: every entry below `i` narrowed to what its
delegator holds once re-evaluated itself. -/
def eff (s : Acl) (i j : Nat) : List Nat := effF s i (j + 1) j

def cascade (s : Acl) (i : Nat) : Acl := fun j => { s j with caps := eff s i j }

/-- Re-evaluating only the direct delegates of `i`. -/
def oneLevel (s : Acl) (i : Nat) : Acl := fun j =>
  if (s j).delegatedBy = some i then
    { s j with caps := (s j).caps.filter (fun c => (auth s i).contains c) }
  else s j

inductive Reeval
  | none
  | oneLevel
  | transitive
  deriving DecidableEq, Repr

def reeval : Reeval → Acl → Nat → Acl
  | .none, s, _ => s
  | .oneLevel, s, i => oneLevel s i
  | .transitive, s, i => cascade s i

structure Rules where
  /-- grant item 4 / CONVENTIONS §9: within the granter. -/
  grantBound : Bool
  re : Reeval
  /-- The fix: an amendment is also within the `delegatedBy` entry. -/
  amendBound : Bool
  deriving DecidableEq, Repr

/-- The rules as written. -/
def written : Rules := ⟨true, .transitive, false⟩

/-- The rules with the fix. -/
def fixed : Rules := ⟨true, .transitive, true⟩

inductive Step (r : Rules) : Acl → Acl → Prop
  /-- `acl/grant`: granter `g`, new subject `j`. -/
  | grant (s : Acl) (g j : Nat) (caps : List Nat) : (s j).live = false → g < j →
      (r.grantBound = true → Sub caps (auth s g)) →
      Step r s (set s j ⟨caps, some g, true⟩)
  /-- `acl/revoke` narrowing, an `acl/update` narrowing, or a demotion. -/
  | narrow (s : Acl) (i : Nat) (caps : List Nat) : Sub caps (s i).caps →
      Step r s (reeval r.re (set s i { s i with caps := caps }) i)
  /-- `acl/revoke` removal. -/
  | remove (s : Acl) (i : Nat) :
      Step r s (reeval r.re (set s i { s i with live := false }) i)
  /-- `acl/update` by amending party `a`: it covers the entry as it stands and
  the amended entry. -/
  | amend (s : Acl) (a j : Nat) (caps : List Nat) : (s j).live = true →
      Sub (auth s j) (auth s a) → Sub caps (auth s a) →
      (r.amendBound = true → ∀ g, (s j).delegatedBy = some g → Sub caps (auth s g)) →
      Step r s (reeval r.re (set s j { s j with caps := caps }) j)

inductive Reach (r : Rules) (s0 : Acl) : Acl → Prop
  | refl : Reach r s0 s0
  | step {s s' : Acl} : Reach r s0 s → Step r s s' → Reach r s0 s'

/-! ### Unfolding lemmas -/

theorem underF_stable (s : Acl) (i : Nat) :
    ∀ n m j, j < n → j < m → underF s i n j = underF s i m j := by
  intro n
  induction n with
  | zero => intro _ _ h; cases h
  | succ n ih =>
      intro m j hn hm
      cases m with
      | zero => cases hm
      | succ m =>
          simp only [underF]
          cases hd : (s j).delegatedBy with
          | none => rfl
          | some g =>
              by_cases hg : g < j
              · show (decide (g < j) && (g == i || underF s i n g)) = (decide (g < j) && (g == i || underF s i m g))
                rw [ih m g (by omega) (by omega)]
              · simp [hg]

theorem under_eq {s : Acl} {i j g : Nat} (h : (s j).delegatedBy = some g) :
    under s i j = (decide (g < j) && (g == i || under s i g)) := by
  unfold under
  conv => lhs; unfold underF
  simp only [h]
  by_cases hg : g < j
  · rw [underF_stable s i j (g + 1) g hg (by omega)]
  · simp [hg]

theorem under_lt {s : Acl} {i : Nat} : ∀ j, under s i j = true → i < j := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
      intro hu
      cases hd : (s j).delegatedBy with
      | none => unfold under underF at hu; simp [hd] at hu
      | some g =>
          rw [under_eq hd] at hu
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hu
          obtain ⟨hg, h | h⟩ := hu
          · omega
          · have := ih g hg h; omega

theorem effF_stable (s : Acl) (i : Nat) :
    ∀ n m j, j < n → j < m → effF s i n j = effF s i m j := by
  intro n
  induction n with
  | zero => intro _ _ h; cases h
  | succ n ih =>
      intro m j hn hm
      cases m with
      | zero => cases hm
      | succ m =>
          simp only [effF]
          cases hd : (s j).delegatedBy with
          | none => rfl
          | some g =>
              by_cases hg : g < j
              · show (if g < j ∧ under s i j = true then
                    (auth s j).filter (fun c => (effF s i n g).contains c) else auth s j) =
                  (if g < j ∧ under s i j = true then
                    (auth s j).filter (fun c => (effF s i m g).contains c) else auth s j)
                rw [ih m g (by omega) (by omega)]
              · simp [hg]

theorem eff_none {s : Acl} {i j : Nat} (h : (s j).delegatedBy = none) : eff s i j = auth s j := by
  unfold eff effF; simp [h]

theorem eff_some {s : Acl} {i j g : Nat} (h : (s j).delegatedBy = some g) :
    eff s i j = if g < j ∧ under s i j = true then
      (auth s j).filter (fun c => (eff s i g).contains c) else auth s j := by
  unfold eff
  conv => lhs; unfold effF
  simp only [h]
  by_cases hg : g < j
  · rw [effF_stable s i j (g + 1) g hg (by omega)]
  · simp [hg]

theorem eff_not_under {s : Acl} {i j : Nat} (h : under s i j = false) : eff s i j = auth s j := by
  cases hd : (s j).delegatedBy with
  | none => exact eff_none hd
  | some g => rw [eff_some hd]; simp [h]

theorem eff_sub (s : Acl) (i j : Nat) : Sub (eff s i j) (auth s j) := by
  intro c hc
  cases hd : (s j).delegatedBy with
  | none => rw [eff_none hd] at hc; exact hc
  | some g =>
      rw [eff_some hd] at hc
      split at hc
      · exact (List.mem_filter.mp hc).1
      · exact hc

theorem auth_cascade (s : Acl) (i j : Nat) : auth (cascade s i) j = eff s i j := by
  unfold auth cascade
  cases hl : (s j).live
  · simp only [Bool.false_eq_true, if_false]
    cases he : eff s i j with
    | nil => rfl
    | cons c _ =>
        have := eff_sub s i j c (by simp [he])
        simp [auth, hl] at this
  · rfl

/-! ### Soundness of the rules -/

/-- Re-evaluation below `i` restores the invariant after `i` changes, when the
changed entry is still within its own delegator and everything else was
within before. -/
theorem cascade_within {s0 : Acl} {i : Nat} {x : Entry} (hW : Within s0) (hF : Forest s0)
    (hx : x.delegatedBy = (s0 i).delegatedBy)
    (hi : ∀ g, x.delegatedBy = some g → Sub (auth (set s0 i x) i) (auth (set s0 i x) g)) :
    Within (cascade (set s0 i x) i) := by
  intro j g hj
  have hj' : (set s0 i x j).delegatedBy = some g := hj
  rw [auth_cascade, auth_cascade]
  have hgj : g < j := by
    unfold set at hj'
    split at hj'
    · subst_vars; exact hF _ _ (hx ▸ hj')
    · exact hF _ _ hj'
  cases hu : under (set s0 i x) i j
  · rw [eff_not_under hu]
    rw [under_eq hj'] at hu
    simp only [decide_eq_true hgj, Bool.true_and, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hu
    obtain ⟨hgi, hug⟩ := hu
    rw [eff_not_under hug]
    by_cases hji : j = i
    · subst hji
      unfold set at hj'; simp only [if_true] at hj'
      exact hi g hj'
    · have h1 : auth (set s0 i x) j = auth s0 j := by simp [auth, set, hji]
      have h2 : auth (set s0 i x) g = auth s0 g := by simp [auth, set, hgi]
      have h3 : (s0 j).delegatedBy = some g := by simpa [set, hji] using hj'
      rw [h1, h2]; exact hW j g h3
  · rw [eff_some hj', if_pos ⟨hgj, hu⟩]
    intro c hc
    have := (List.mem_filter.mp hc).2
    exact List.contains_iff_mem.mp this

theorem set_forest {s : Acl} {i : Nat} {x : Entry} (hF : Forest s)
    (hx : ∀ g, x.delegatedBy = some g → g < i) : Forest (set s i x) := by
  intro j g h
  unfold set at h
  split at h
  · subst_vars; exact hx g h
  · exact hF j g h

theorem cascade_forest {s : Acl} {i : Nat} (hF : Forest s) : Forest (cascade s i) :=
  fun j g h => hF j g h

/-- The rules (transitive re-evaluation, granter bound) keep every entry within
its delegator, with or without the fix, as long as amendments respect it. -/
theorem step_within {r : Rules} {s s' : Acl} (hb : r.grantBound = true)
    (hre : r.re = .transitive) (ha : r.amendBound = true)
    (hW : Within s) (hF : Forest s) (st : Step r s s') : Within s' ∧ Forest s' := by
  cases st with
  | grant g j caps hl hgj hcap =>
      refine ⟨?_, set_forest hF (fun g' h => by cases h; exact hgj)⟩
      intro k g' hk
      by_cases hkj : k = j
      · subst hkj
        simp only [set, if_true] at hk
        cases hk
        have hgk : g ≠ k := by omega
        intro c hc
        simp only [auth, set, if_true] at hc
        have := hcap hb c hc
        simpa [auth, set, hgk] using this
      · have hk' : (s k).delegatedBy = some g' := by simpa [set, hkj] using hk
        intro c hc
        have hc' : c ∈ auth s k := by simpa [auth, set, hkj] using hc
        have := hW k g' hk' c hc'
        by_cases hgj' : g' = j
        · subst hgj'; simp [auth, hl] at this
        · simpa [auth, set, hgj'] using this
  | narrow i caps hsub =>
      rw [hre]
      refine ⟨cascade_within hW hF rfl ?_, cascade_forest (set_forest hF (fun g h => hF i g h))⟩
      intro g hg
      have hgi : g ≠ i := by have := hF i g hg; omega
      intro c hc
      have hc' : c ∈ auth s i := by
        simp only [auth, set, if_true] at hc
        split at hc
        · simp only [auth]; rename_i hl; simp only [hl, if_true]; exact hsub c hc
        · cases hc
      have := hW i g hg c hc'
      simpa [auth, set, hgi] using this
  | remove i =>
      rw [hre]
      refine ⟨cascade_within hW hF rfl ?_, cascade_forest (set_forest hF (fun g h => hF i g h))⟩
      intro g _ c hc
      simp [auth, set] at hc
  | amend a j caps hl _ _ hfix =>
      rw [hre]
      refine ⟨cascade_within hW hF rfl ?_, cascade_forest (set_forest hF (fun g h => hF j g h))⟩
      intro g hg
      have hgj : g ≠ j := by have := hF j g hg; omega
      intro c hc
      simp only [auth, set, if_true, hl] at hc
      have := hfix ha g hg c hc
      simpa [auth, set, hgj] using this

/-- With the fix, every reachable ACL keeps every entry within the entry its
`delegatedBy` names. -/
theorem within_preserved {s0 s : Acl} (hW : Within s0) (hF : Forest s0)
    (h : Reach fixed s0 s) : Within s ∧ Forest s := by
  induction h with
  | refl => exact ⟨hW, hF⟩
  | step _ st ih => exact step_within rfl rfl rfl ih.1 ih.2 st

/-- On an ACL that already satisfies the invariant, re-evaluation changes
nothing: it withdraws only what exceeds. -/
theorem cascade_minimal {s : Acl} (hW : Within s) (i : Nat) :
    ∀ j, auth (cascade s i) j = auth s j := by
  intro j
  rw [auth_cascade]
  induction j using Nat.strongRecOn with
  | ind j ih =>
      cases hd : (s j).delegatedBy with
      | none => exact eff_none hd
      | some g =>
          rw [eff_some hd]
          split
          · rename_i hc
            rw [ih g hc.1]
            apply List.filter_eq_self.mpr
            intro c hcm
            exact List.contains_iff_mem.mpr (hW j g hd c hcm)
          · rfl

/-! ### Soundness applies to a real run -/

/-- Entry 0, a root holding capabilities 1 and 2. -/
def root : Acl := fun j => if j = 0 then ⟨[1, 2], none, true⟩ else gone

theorem root_within : Within root := by
  intro j g h
  unfold root at h
  split at h <;> cases h

theorem root_forest : Forest root := by
  intro j g h
  unfold root at h
  split at h <;> cases h

/-- 0 grants {1, 2} to 1, 1 grants {1, 2} to 2, then 0 is narrowed to {1}:
both delegates are re-evaluated down to {1}. -/
theorem within_nonvacuous :
    ∃ s, Reach fixed root s ∧ Within s ∧ auth s 1 = [1] ∧ auth s 2 = [1] := by
  have h1 := Reach.step (Reach.refl (r := fixed) (s0 := root))
    (Step.grant root 0 1 [1, 2] rfl (by decide) (fun _ => by decide))
  have h2 := Reach.step h1 (Step.grant _ 1 2 [1, 2] rfl (by decide) (fun _ => by decide))
  have h3 := Reach.step h2 (Step.narrow _ 0 [1] (by decide))
  exact ⟨_, h3, (within_preserved root_within root_forest h3).1, by decide, by decide⟩

/-! ### Each rule is needed -/

/-- Without the granter bound (grant item 4), entry 1 is created with a
capability its granter lacks. -/
theorem grant_bound_needed :
    ∃ s, Reach { fixed with grantBound := false } root s ∧ ¬ Within s := by
  refine ⟨_, Reach.step Reach.refl (Step.grant root 0 1 [3] rfl (by decide) (fun h => by cases h)), ?_⟩
  intro hW
  have := hW 1 0 rfl 3 (by decide)
  revert this; decide

/-- Without re-evaluation (grant item 9, revoke item 6), the delegate of a
narrowed entry keeps what its delegator lost. -/
theorem reeval_needed :
    ∃ s, Reach { fixed with re := .none } root s ∧ ¬ Within s := by
  have h1 := Reach.step (Reach.refl (r := { fixed with re := .none }) (s0 := root))
    (Step.grant root 0 1 [1, 2] rfl (by decide) (fun _ => by decide))
  refine ⟨_, Reach.step h1 (Step.narrow _ 0 [1] (by decide)), ?_⟩
  intro hW
  have := hW 1 0 rfl 2 (by decide)
  revert this; decide

/-- Re-evaluating only direct delegates is not enough: 0 → 1 → 2, 0 narrowed,
1 re-evaluated, 2 keeps what 1 lost. Grant item 9 and §9 trigger on 1's
narrowing too, which is the transitive re-evaluation. -/
theorem one_level_insufficient :
    ∃ s, Reach { fixed with re := .oneLevel } root s ∧ ¬ Within s ∧
      auth s 1 = [1] ∧ auth s 2 = [1, 2] := by
  have h1 := Reach.step (Reach.refl (r := { fixed with re := .oneLevel }) (s0 := root))
    (Step.grant root 0 1 [1, 2] rfl (by decide) (fun _ => by decide))
  have h2 := Reach.step h1 (Step.grant _ 1 2 [1, 2] rfl (by decide) (fun _ => by decide))
  refine ⟨_, Reach.step h2 (Step.narrow _ 0 [1] (by decide)), ?_, by decide, by decide⟩
  intro hW
  have := hW 2 1 rfl 2 (by decide)
  revert this; decide

/-! ### The defect: amendment by a party other than the delegator -/

/-- Entry 0, a root holding {1}; entry 1, a root holding {1, 2}; entry 2,
delegated {1} by 0. -/
def twoRoots : Acl := fun j =>
  if j = 0 then ⟨[1], none, true⟩
  else if j = 1 then ⟨[1, 2], none, true⟩
  else if j = 2 then ⟨[1], some 0, true⟩
  else gone

theorem twoRoots_within : Within twoRoots := by
  intro j g h c hc
  unfold twoRoots at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; subst_vars
        simp [auth, twoRoots] at hc ⊢; exact hc
      · cases h

/-- As written: 1 covers entry 2 and amends it to {1, 2} (update items 5 and
10: bounded by the amending party, `delegatedBy` unchanged). Entry 2 now
exceeds 0, the entry said to bound it. Then 1 is removed: no entry is
delegated by 1, so nothing is re-evaluated, and entry 2 keeps capability 2,
which no live entry delegated to it. -/
theorem amend_escapes_delegator :
    ∃ s, Reach written twoRoots s ∧ (s 2).delegatedBy = some 0 ∧
      2 ∈ auth s 2 ∧ 2 ∉ auth s 0 ∧ (s 1).live = false ∧
      (∀ j, (s j).delegatedBy ≠ some 1) := by
  have h1 := Reach.step (Reach.refl (r := written) (s0 := twoRoots))
    (Step.amend twoRoots 1 2 [1, 2] rfl (by decide) (by decide) (fun h => by cases h))
  refine ⟨_, Reach.step h1 (Step.remove _ 1), by decide, by decide, by decide, by decide, ?_⟩
  intro j h
  have h0 : (twoRoots j).delegatedBy = some 1 := by
    revert h
    unfold set
    by_cases h1 : j = 1 <;> by_cases h2 : j = 2 <;> simp [h1, h2, reeval, written, cascade]
  revert h0
  unfold twoRoots
  repeat' split
  all_goals simp [gone]

/-- With the fix, the amendment is refused: {1, 2} is not within entry 0. -/
theorem fix_refuses_amend :
    ¬ ∀ g, (twoRoots 2).delegatedBy = some g → Sub [1, 2] (auth twoRoots g) := by
  intro h
  have := h 0 rfl 2 (by decide)
  revert this; decide

/-! ### Reading: a queued entry left in force -/

inductive Status
  | active
  | queued
  deriving DecidableEq, Repr

/-- What a queued entry confers: everything (left in force) or nothing. -/
def conferred (inForce : Bool) (st : Status) (caps : List Nat) : List Nat :=
  match st with
  | .active => caps
  | .queued => if inForce then caps else []

/-- Entry 0 narrowed from {1, 2} to {1}; its delegate holding {1, 2} queued for
review. Left in force, the delegate keeps capability 2, which its delegator
has lost; suspended while queued, it keeps nothing. -/
theorem queued_in_force_retains :
    ¬ Sub (conferred true .queued [1, 2]) (conferred true .active [1]) ∧
    Sub (conferred false .queued [1, 2]) (conferred false .active [1]) := by
  refine ⟨?_, fun c h => by simp [conferred] at h⟩
  intro h
  have := h 2 (by decide)
  revert this; decide

end TrustTasks.AclDelegation
