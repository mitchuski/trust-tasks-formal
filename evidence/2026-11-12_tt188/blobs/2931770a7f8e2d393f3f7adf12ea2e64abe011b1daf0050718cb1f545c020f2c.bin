/-
DID rollback against append-only publishing, read against upstream
trustoverip/dtgwg-trust-tasks-tf main (101a51d8d).

`did-management/did/publish/0.1` (retired, superseded by `did/register`),
l. 70: "A submission with a strictly newer log entry advances `versionCount`
and replaces the held content; for `did:webvh` and other append-only methods,
the consumer MUST verify the new chain is a valid extension of the prior one
before accepting." l. 29: "a persisted, publicly-resolvable change to the
identity's history"; l. 31: "the new state resolves immediately".

`did-management/did/register/0.1`, which subsumes publish, l. 99: "A second
call from the same owner with a *new* log entry is an update —
`versionCount` advances, the new log replaces the old". Its consumer item 2
(l. 118) validates the log ("walks the log chain and verifies each entry's
signature against `parameters.updateKeys`"); it states no extension check.

`did-management/did/rollback/0.1`: l. 5 "reverts the slot's log chain to a
prior published version, discarding the entries above that point"; l. 49
"discards log entries newer than `targetVersion` [...] to recover from a
mistaken publish or a key compromise"; l. 39 `invalidTargetVersion` when
"`targetVersion` is greater than the current `versionCount` or less than 1".
The payload is `mnemonic`, `targetVersion`, `domain`, `ext` (schema,
`additionalProperties: false`): no expected current version or head.
l. 24: "which entries it discards depends on when it executes rather than on
anything in the payload". l. 81: "Consumers MUST require freshness on the
producer's session". Nothing restricts rollback to entries not yet resolved;
l. 5 and l. 49 say it discards published ones.

This file shows: under publish alone every log held is a prefix of every
later one, so a version once resolvable never changes; rollback followed by
a publish puts a different entry at a version that was resolvable
(`rollback_rewrites_published`), and any rollback that discards an entry
permits this (`any_discard_permits_rewrite`); register's rule as written
permits the same rewrite without rollback (`extension_check_needed`); a
rollback executed after a publish it never saw discards that entry
(`delayed_rollback_discards_unseen`). Fix for the last: the request carries
the head it expects. An expected `versionCount` suffices when only publishes
intervene (`count_cas_sound`) but not when another rollback does
(`count_cas_insufficient`); an expected head digest that commits to the
chain does (`head_cas_sound`). For the rewrite, the only rule found here is
refusing rollback past resolved entries; since every published entry
resolves at once (publish l. 31), that rule makes every rollback a no-op
(`guarded_rollback_noop`), against rollback's stated purpose. It is a
design choice for the task force, not a fix.

What is modelled: a slot's log as a list of entries, version `i + 1` at
position `i`; an entry stands for its content, so a head digest is modelled
as the whole log (a digest that chains over every earlier entry, as webvh's
entry hashes are meant to). Not modelled: signatures, keys and the
validity of each entry, ownership and admin authority, disabled slots (whose
entries are withheld from resolution), `force` replacement, deletion,
witnesses, resolvers' caches, and time beyond the order of steps.
-/

namespace TrustTasks.DidRollback

/-- An entry; equal entries are equal content. -/
abbrev Entry := Nat

/-- A slot's log; version `i + 1` is at position `i`. -/
abbrev Log := List Entry

def Prefix (a b : Log) : Prop := ∃ s, b = a ++ s

/-- Publish (l. 70): accept a valid extension of the prior chain. -/
inductive Publish : Log → Log → Prop
  | extend (L ext : Log) : ext ≠ [] → Publish L (L ++ ext)

/-- Rollback (l. 39, 49): trim to `targetVersion`, in range. -/
inductive Rollback : Log → Log → Prop
  | trim (L : Log) (k : Nat) : 1 ≤ k → k ≤ L.length → Rollback L (L.take k)

/-- Register's update as written (l. 99): a new log replaces the old and
`versionCount` advances; no extension check. -/
inductive Replace : Log → Log → Prop
  | replace (L L' : Log) : L.length < L'.length → Replace L L'

def Both (L L' : Log) : Prop := Publish L L' ∨ Rollback L L'

/-- Runs of a step relation. -/
inductive Run (S : Log → Log → Prop) : Log → Log → Prop
  | refl (L : Log) : Run S L L
  | step {L M N : Log} : Run S L M → S M N → Run S L N

theorem prefix_trans {a b c : Log} : Prefix a b → Prefix b c → Prefix a c
  | ⟨s, hs⟩, ⟨u, hu⟩ => ⟨s ++ u, by rw [hu, hs, List.append_assoc]⟩

/-! ### Publish alone is append-only -/

theorem publish_append_only {L0 L : Log} (h : Run Publish L0 L) : Prefix L0 L := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | step _ s ih =>
      cases s with
      | extend ext _ => exact prefix_trans ih ⟨ext, rfl⟩

/-- Under publish alone, a version once resolvable keeps its entry. -/
theorem publish_version_stable {L1 L2 : Log} (h : Run Publish L1 L2) {i : Nat}
    {a : Entry} (ha : L1[i]? = some a) : L2[i]? = some a := by
  obtain ⟨s, rfl⟩ := publish_append_only h
  have hi : i < L1.length := by
    rcases Nat.lt_or_ge i L1.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at ha; cases ha
  rw [List.getElem?_append_left hi]; exact ha

/-! ### Rollback rewrites a published version -/

/-- Four entries published one by one, version 4 resolvable as entry `4`;
rolled back to version 3; a different entry `5` published as version 4.
Every publish passes the extension check. -/
theorem rollback_rewrites_published :
    Run Both [] [1, 2, 3, 4] ∧ Run Both [1, 2, 3, 4] [1, 2, 3, 5] ∧
    [1, 2, 3, 4][3]? = some 4 ∧ [1, 2, 3, 5][3]? = some 5 := by
  have p : ∀ L e, Both L (L ++ [e]) := fun L e => Or.inl (Publish.extend L [e] (by simp))
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact .step (.step (.step (.step (.refl _) (p [] 1)) (p [1] 2)) (p [1, 2] 3)) (p [1, 2, 3] 4)
  · have r : Both [1, 2, 3, 4] [1, 2, 3] :=
      Or.inr (Rollback.trim [1, 2, 3, 4] 3 (by decide) (by decide))
    exact .step (.step (.refl _) r) (p [1, 2, 3] 5)

/-- Any rollback that discards an entry lets that version be rewritten with
any other entry, through publish's extension check. -/
theorem any_discard_permits_rewrite {L : Log} {k : Nat} (h1 : 1 ≤ k)
    (hk : k < L.length) (e : Entry) :
    Run Both L (L.take k ++ [e]) ∧ (L.take k ++ [e])[k]? = some e := by
  refine ⟨.step (.step (.refl _) (Or.inr (Rollback.trim L k h1 (Nat.le_of_lt hk))))
    (Or.inl (Publish.extend _ [e] (by simp))), ?_⟩
  have : (L.take k).length = k := by rw [List.length_take]; omega
  rw [List.getElem?_append_right (by omega), this, Nat.sub_self]; rfl

/-- Publish's extension check is needed: register's rule as written replaces
version 2 with no rollback at all. -/
theorem extension_check_needed :
    Run Replace [1, 2] [1, 9, 3] ∧ [1, 2][1]? = some 2 ∧ [1, 9, 3][1]? = some 9 ∧
    ¬ Prefix [1, 2] [1, 9, 3] := by
  refine ⟨.step (.refl _) (Replace.replace _ _ (by decide)), rfl, rfl, ?_⟩
  rintro ⟨s, hs⟩
  cases s <;> simp at hs

/-- The range rule (l. 39) is needed: a target of 0 would discard the
genesis entry the DID is derived from. -/
theorem range_rule_needed : ([1, 2, 3] : Log).take 0 = [] := rfl

/-! ### A delayed rollback -/

/-- Today a rollback executes on the log it finds: it discards
`L.drop k` whatever the requester saw. -/
def acceptedToday (L : Log) (k : Nat) : Prop := 1 ≤ k ∧ k ≤ L.length

/-- The owner sees `[1, 2, 3]` and asks to roll back to version 2; entry `4`
is published before the rollback executes; the rollback is in range and
discards `4`, which the owner never saw. -/
theorem delayed_rollback_discards_unseen :
    Run Publish [1, 2, 3] [1, 2, 3, 4] ∧ acceptedToday [1, 2, 3, 4] 2 ∧
    4 ∈ ([1, 2, 3, 4] : Log).drop 2 ∧ 4 ∉ ([1, 2, 3] : Log) := by
  refine ⟨.step (.refl _) (Publish.extend _ [4] (by simp)), ⟨by decide, by decide⟩,
    by decide, by decide⟩

/-! ### The fix: the request carries the head it expects -/

/-- With an expected `versionCount`: refused unless the count matches. -/
def acceptedCount (L : Log) (expected k : Nat) : Prop :=
  acceptedToday L k ∧ L.length = expected

/-- With an expected head digest committing to the chain (modelled as the
log itself): refused unless the log is the one the requester saw. -/
def acceptedHead (L seen : Log) (k : Nat) : Prop := acceptedToday L k ∧ L = seen

/-- If only publishes intervene, a matching count means nothing was
published since the requester looked: everything discarded was seen. -/
theorem count_cas_sound {seen L : Log} {k : Nat} (h : Run Publish seen L)
    (ha : acceptedCount L seen.length k) : L = seen ∧ L.drop k = seen.drop k := by
  obtain ⟨s, rfl⟩ := publish_append_only h
  have hs : s.length = 0 := by
    have := ha.2; simp only [List.length_append] at this; omega
  rw [List.length_eq_zero_iff.1 hs, List.append_nil]; exact ⟨rfl, rfl⟩

/-- The count refuses the delayed rollback. -/
theorem count_cas_refuses_delayed : ¬ acceptedCount [1, 2, 3, 4] 3 2 := by
  intro h; cases h.2

/-- The count is not enough when another rollback intervenes: the owner saw
`[1, 2, 3]`, another rollback to 2 and a publish of `9` follow, the count
is still 3, and the rollback discards `9`, never seen. -/
theorem count_cas_insufficient :
    Run Both [1, 2, 3] [1, 2, 9] ∧ acceptedCount [1, 2, 9] 3 2 ∧
    9 ∈ ([1, 2, 9] : Log).drop 2 ∧ 9 ∉ ([1, 2, 3] : Log) := by
  refine ⟨.step (.step (.refl _) (Or.inr (Rollback.trim [1, 2, 3] 2 (by decide) (by decide))))
    (Or.inl (Publish.extend [1, 2] [9] (by simp))),
    ⟨⟨by decide, by decide⟩, rfl⟩, by decide, by decide⟩

/-- An expected head refuses both: whatever ran in between, what is
discarded is exactly what the requester saw above the target. -/
theorem head_cas_sound {L seen : Log} {k : Nat} (ha : acceptedHead L seen k) :
    L.drop k = seen.drop k := by rw [ha.2]

theorem head_cas_refuses :
    ¬ acceptedHead [1, 2, 3, 4] [1, 2, 3] 2 ∧ ¬ acceptedHead [1, 2, 9] [1, 2, 3] 2 := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> cases h.2

/-- Nonvacuity: an undelayed rollback passes both. -/
theorem cas_nonvacuous :
    acceptedCount [1, 2, 3] 3 2 ∧ acceptedHead [1, 2, 3] [1, 2, 3] 2 :=
  ⟨⟨⟨by decide, by decide⟩, rfl⟩, ⟨⟨by decide, by decide⟩, rfl⟩⟩

/-! ### Refusing rollback past resolved entries -/

/-- A slot with the highest version ever resolved. Publish resolves at once
(l. 31); a guarded rollback may not go below what was resolved. -/
inductive Guarded : Log × Nat → Log × Nat → Prop
  | publish (L ext : Log) (w : Nat) : ext ≠ [] →
      Guarded (L, w) (L ++ ext, max w (L ++ ext).length)
  | rollback (L : Log) (w k : Nat) : 1 ≤ k → k ≤ L.length → w ≤ k →
      Guarded (L, w) (L.take k, w)

inductive GRun : Log × Nat → Log × Nat → Prop
  | refl (s : Log × Nat) : GRun s s
  | step {a b c : Log × Nat} : GRun a b → Guarded b c → GRun a c

/-- Guarded, the log is append-only again, and every log held stays within
what was resolved. -/
theorem guarded_append_only {L0 L : Log} {w : Nat} (h : GRun (L0, L0.length) (L, w)) :
    Prefix L0 L ∧ L.length ≤ w := by
  generalize hs : (L, w) = s at h
  induction h generalizing L w with
  | refl => cases hs; exact ⟨⟨[], by simp⟩, Nat.le_refl _⟩
  | step _ g ih =>
      cases g with
      | publish M ext w' _ =>
          cases hs
          obtain ⟨hp, _⟩ := ih rfl
          exact ⟨prefix_trans hp ⟨ext, rfl⟩, Nat.le_max_right _ _⟩
      | rollback M w' k _ hk hw =>
          cases hs
          obtain ⟨hp, hl⟩ := ih rfl
          have hk' : k = M.length := by omega
          rw [hk', List.take_length]
          exact ⟨hp, hl⟩

/-- Since every published entry resolves at once, the guard makes every
rollback a no-op: it rules out the rewrite only by ruling out rollback. -/
theorem guarded_rollback_noop {L0 L : Log} {w k : Nat}
    (h : GRun (L0, L0.length) (L, w)) (hk : k ≤ L.length) (hw : w ≤ k) :
    L.take k = L := by
  have hl := (guarded_append_only h).2
  have hk' : k = L.length := by omega
  rw [hk', List.take_length]

/-- The guard refuses the rollback of `rollback_rewrites_published`. -/
theorem guarded_refuses_rewrite : ¬ Guarded ([1, 2, 3, 4], 4) ([1, 2, 3], 4) := by
  intro g
  generalize hs : (([1, 2, 3], 4) : Log × Nat) = s at g
  cases g with
  | publish _ ext _ _ =>
      have := congrArg (fun p => p.1.length) hs
      simp at this
  | rollback _ _ k _ hk hw =>
      have h1 := congrArg (fun p => p.1.length) hs
      simp at h1 hk
      omega

end TrustTasks.DidRollback
