/-
Trustee key generation and threshold decryption for sealed and
tallied-encrypted elections, read against upstream
trustoverip/dtgwg-trust-tasks-tf main (101a51d8d). A confirmation model: the
counting the rules rely on holds as written; no defect was found.

`voting/_shared/0.1/CONVENTIONS.md` §9 (l. 257-258): "`t` is
`trustees.threshold` and `n` the number of trustees. `2 ≤ t ≤ n`
(VTI-VOT-062)". The schema's `Trustees.dids` is `uniqueItems`
(`voting.schema.json` l. 284), and `vtc/elections/create/0.5` item 3 refuses a
manifest breaking "`2 ≤ threshold ≤` their number".

§9.6 (l. 315-335): "Dealing opens when all `n` have enrolled"; "Confirming
opens when all `n` have dealt"; item 4 "A justified complaint is void";
item 5 "When every trustee has confirmed and every complaint is justified or
void, or else at `votingOpensAt`, the **qualified** dealers are those with no
unjustified complaint. [...] If fewer than `t` dealers qualify, or fewer than
`t` trustees have confirmed, [...] the ceremony has **failed** [...]. With at
most `t − 1` corrupt trustees, `t` qualified dealers include an honest one
[...]: a corrupt trustee complaining of every other dealer at the last moment
fails the ceremony rather than leaving its own dealing the key."

`voting/trustees/confirm/0.1` item 6 (l. 88): "Refuse with `malformedRequest`
a complaint naming a trustee index the manifest does not have, or the trustee
itself." `voting/trustees/justify/0.1` item 5 (l. 89): "Refuse with
`voting/trustees/justify:noComplaint` unless `recipient` complained of
`dealer`."

§9.7 (l. 403) and `voting/trustees/decrypt/0.1` item 6 (l. 88): "When every
target has `t` verified partials of distinct trustees, open each sealed
ballot [...]". Decrypt states no `alreadyDecrypted` refusal: a trustee may
append more than one `partials` entry, so the distinctness is load-bearing.

What is modelled: trustees as distinct indices; who confirmed, who complained
of whom, which complaints are justified; the qualified set and the formation
rule; for decryption, the trustees whose verified partials the board holds.
Corruption is any list of indices of length below `t`.

Edge cases checked: a complaint against oneself (refused by confirm item 6;
the honesty theorem does not need that rule: such a complaint can only
disqualify its author); a dealer both complained of and justified (qualified,
`justified_restores`); `t > n` (no key ever forms, `no_key_when_t_gt_n`, so
create item 3's bound is for liveness, not safety).

Not modelled: the group, polynomials, commitments, shares and every proof
(each verified step is taken as the trustee's own, §9.6 replay items 1-4);
transport keys; the ballot box's and the community's roles; the authorization
of targets (§9.7); timing (`votingOpensAt` is the deadline path of item 5,
with whatever complaints stand); several DIDs held by one party; and the
purpose of the "fewer than `t` trustees have confirmed" rule, which no
theorem here needs.
-/

namespace TrustTasks.VotingTrustees

/-- A trustee index (`trustees.dids`, from 1). -/
abbrev Trustee := Nat

/-- Pigeonhole: a duplicate-free list inside `m` is no longer than `m`. -/
theorem length_le_of_nodup_subset :
    ∀ {l m : List Trustee}, l.Nodup → (∀ x ∈ l, x ∈ m) → l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, m, hl, h => by
      rw [List.nodup_cons] at hl
      have ha : a ∈ m := h a (List.mem_cons_self ..)
      have ih := length_le_of_nodup_subset (m := m.erase a) hl.2 (fun x hx => by
        have hne : x ≠ a := fun e => hl.1 (e ▸ hx)
        exact (List.mem_erase_of_ne hne).2 (h x (List.mem_cons_of_mem _ hx)))
      rw [List.length_erase_of_mem ha] at ih
      have : 0 < m.length := List.length_pos_of_mem ha
      simp only [List.length_cons]; omega

/-- At least `t` distinct indices, fewer than `t` corrupt: one is honest. -/
theorem exists_honest {l C : List Trustee} {t : Nat} (hl : l.Nodup)
    (ht : t ≤ l.length) (hC : C.length < t) : ∃ x ∈ l, x ∉ C :=
  Classical.byContradiction fun h => by
    have hsub : ∀ x ∈ l, x ∈ C := fun x hx =>
      Classical.byContradiction fun hn => h ⟨x, hx, hn⟩
    have := length_le_of_nodup_subset hl hsub
    omega

/-! ### Generating the election key (§9.6) -/

/-- The board's ceremony at formation. `complaints` are `(complainer, dealer)`
pairs; `justified` the complaints a verifying justification voids. -/
structure Ceremony where
  trustees : List Trustee
  t : Nat
  confirmed : List Trustee
  complaints : List (Trustee × Trustee)
  justified : List (Trustee × Trustee)
  deriving DecidableEq, Repr

/-- The rules on the inputs: distinct trustees (`uniqueItems`), each confirms
once (confirm item 5), a complaint is by a confirmed trustee against another
trustee (confirm item 6), a justification answers a complaint (justify
item 5). -/
def Adm (c : Ceremony) : Prop :=
  c.trustees.Nodup ∧ c.confirmed.Nodup ∧ (∀ j ∈ c.confirmed, j ∈ c.trustees) ∧
  (∀ p ∈ c.complaints, p.1 ∈ c.confirmed ∧ p.2 ∈ c.trustees ∧ p.1 ≠ p.2) ∧
  (∀ p ∈ c.justified, p ∈ c.complaints)

/-- `d` has a complaint against it that no justification voids. -/
def unjustified (c : Ceremony) (d : Trustee) : Bool :=
  c.complaints.any fun p => p.2 == d && !(c.justified.contains p)

/-- Item 5: "the **qualified** dealers are those with no unjustified
complaint". -/
def qualified (c : Ceremony) : List Trustee :=
  c.trustees.filter fun d => !unjustified c d

/-- Item 5: the key forms unless fewer than `t` dealers qualify or fewer
than `t` trustees have confirmed. -/
def Formed (c : Ceremony) : Prop :=
  c.t ≤ c.confirmed.length ∧ c.t ≤ (qualified c).length

instance (c : Ceremony) : Decidable (Formed c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Formation without item 5's qualified-dealer count. -/
def FormedNoQualifiedCheck (c : Ceremony) : Prop := c.t ≤ c.confirmed.length

theorem qualified_nodup {c : Ceremony} (h : c.trustees.Nodup) : (qualified c).Nodup :=
  List.nodup_iff_pairwise_ne.2 ((List.nodup_iff_pairwise_ne.1 h).filter _)

theorem mem_qualified {c : Ceremony} {d : Trustee} :
    d ∈ qualified c ↔ d ∈ c.trustees ∧ unjustified c d = false := by
  simp [qualified, List.mem_filter]

/-- Soundness of formation: at least `t` distinct qualified dealers, each a
trustee, every complaint against each one justified. -/
theorem formed_sound {c : Ceremony} (hA : Adm c) (hf : Formed c) :
    c.t ≤ (qualified c).length ∧ (qualified c).Nodup ∧
    ∀ d ∈ qualified c, d ∈ c.trustees ∧
      ∀ p ∈ c.complaints, p.2 = d → p ∈ c.justified := by
  refine ⟨hf.2, qualified_nodup hA.1, fun d hd => ?_⟩
  obtain ⟨hdt, hu⟩ := mem_qualified.1 hd
  refine ⟨hdt, fun p hp hpd => ?_⟩
  have hall := List.any_eq_false.1 hu p hp
  simp only [hpd, beq_self_eq_true, Bool.true_and, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.not_eq_false] at hall
  exact List.mem_of_elem_eq_true hall

/-- Item 5's claim: with fewer than `t` corrupt trustees, a formed key has an
honest qualified dealer. Needs only distinct trustees, not confirm item 6:
a self-complaint can only disqualify its author. -/
theorem formed_has_honest_dealer {c : Ceremony} (hN : c.trustees.Nodup)
    (hf : Formed c) {C : List Trustee} (hC : C.length < c.t) :
    ∃ d ∈ qualified c, d ∉ C :=
  exists_honest (qualified_nodup hN) hf.2 hC

/-- No key forms when `t > n`: create item 3's bound is for liveness. -/
theorem no_key_when_t_gt_n {c : Ceremony} (hN : c.trustees.Nodup)
    (ht : c.trustees.length < c.t) : ¬ Formed c := by
  intro hf
  have := length_le_of_nodup_subset (qualified_nodup hN)
    (fun d hd => (mem_qualified.1 hd).1)
  have := hf.2
  omega

/-- Item 5's scenario: three trustees, `t = 2`, trustee 3 corrupt; at the
deadline it has complained of both other dealers, unanswered. -/
def lastMoment : Ceremony :=
  { trustees := [1, 2, 3], t := 2, confirmed := [1, 2, 3],
    complaints := [(3, 1), (3, 2)], justified := [] }

/-- The "fewer than `t` dealers qualify" rule is needed: without it the key
forms from the corrupt trustee's dealing alone, which it then knows. With it,
the ceremony fails. -/
theorem qualified_check_needed :
    Adm lastMoment ∧ FormedNoQualifiedCheck lastMoment ∧
    qualified lastMoment = [3] ∧ ¬ Formed lastMoment := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    by unfold FormedNoQualifiedCheck; decide,
    by decide, by decide⟩

/-- Nonvacuity: the honest dealers answer with shares that check, the
complaints are void, every dealer qualifies, and the key forms. -/
def justifiedInTime : Ceremony := { lastMoment with justified := [(3, 1), (3, 2)] }

theorem justified_restores :
    Adm justifiedInTime ∧ qualified justifiedInTime = [1, 2, 3] ∧
    Formed justifiedInTime := by
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide⟩

/-! ### Decrypting (§9.7) -/

/-- "`t` verified partials of distinct trustees": the board holds verified
partials (decrypt item 5 refuses others) from the trustees listed in
`partials`, possibly repeated. -/
def Opens (ts : List Trustee) (t : Nat) (partials : List Trustee) : Prop :=
  ∃ S : List Trustee, S.Nodup ∧ t ≤ S.length ∧ ∀ j ∈ S, j ∈ partials ∧ j ∈ ts

/-- Counting partials without distinctness. -/
def OpensNoDistinct (t : Nat) (partials : List Trustee) : Prop := t ≤ partials.length

/-- Soundness: opening uses a partial of an honest trustee whenever fewer
than `t` are corrupt. -/
theorem opens_has_honest {ts P C : List Trustee} {t : Nat} (h : Opens ts t P)
    (hC : C.length < t) : ∃ j ∈ P, j ∈ ts ∧ j ∉ C := by
  obtain ⟨S, hS, ht, hSP⟩ := h
  obtain ⟨j, hj, hjC⟩ := exists_honest hS ht hC
  exact ⟨j, (hSP j hj).1, (hSP j hj).2, hjC⟩

/-- Fewer than `t` corrupt trustees cannot open anything on their own,
however many partials they send. -/
theorem corrupt_cannot_open {ts P C : List Trustee} {t : Nat}
    (hP : ∀ j ∈ P, j ∈ C) (hC : C.length < t) : ¬ Opens ts t P := by
  intro h
  obtain ⟨j, hj, _, hjC⟩ := opens_has_honest h hC
  exact hjC (hP j hj)

/-- Distinctness is needed: corrupt trustee 3 sends its partial twice;
counted without distinctness, two partials meet `t = 2`. -/
theorem distinct_needed :
    OpensNoDistinct 2 [3, 3] ∧ ¬ Opens [1, 2, 3] 2 [3, 3] := by
  refine ⟨by unfold OpensNoDistinct; decide, corrupt_cannot_open (C := [3]) (by decide) (by decide)⟩

/-- Nonvacuity: partials from trustees 1 and 3 open at `t = 2`. -/
theorem opens_nonvacuous : Opens [1, 2, 3] 2 [1, 3] :=
  ⟨[1, 3], by decide, by decide, by decide⟩

end TrustTasks.VotingTrustees
