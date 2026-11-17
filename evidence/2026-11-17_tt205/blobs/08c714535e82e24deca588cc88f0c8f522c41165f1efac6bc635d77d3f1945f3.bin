/-
Two invariants of the `mages` Trust Task family, a PRIVATE family whose Type
URIs sit under https://tasks.mages.city/spec/mages/. Both specifications are
drafts (status `draft`, version 0.1); this file reads the draft text as it
stood on 2026-11-17.

## M5. City Key: four-state determination

`mages/city-key/present/0.1`, Verification:

  "`ok` is true when no state is `mismatch`. **`ok` means nothing was
  contradicted, not that everything was checked.** A consumer **MUST** branch
  on `states` and `unverified`, and **MUST NOT** turn `ok` into a permission."

  "5. **Hold.** Where the key declares `holds`, the state is always
  `unavailable`: the held items never reach the City, so the root is
  declared, not re-derived."

The reference reader (mages_city `gate/citykey.mjs`, `verifyKey`) gives each
of six claims (`kappa`, `packetProofs`, `packetsRoot`, `did`, `holds`,
`chains`) a state from three facts:

  state = (claimed, checkable, agrees) =>
    !claimed ? 'absent' : !checkable ? 'unavailable' : agrees ? 'match' : 'mismatch'

with the comment "`absent` (nothing was claimed) and `unavailable` (a claim
was made but the material to check it was not supplied) are NOT `match` ...
Collapsing them is how an unchecked claim comes to read as a checked one."
`kappa` and `packetProofs` are always checkable; `holds` never is.
`unverified` is the claims whose state is `absent` or `unavailable`.

Modelled: the three facts per claim as booleans, the state function, `ok` as
the spec defines it (no state is `mismatch`), and `unverified`.
Not modelled: the hashes themselves (κ canonicalisation, the packet-root
fold, `did:key` derivation, chain faces), which are taken as the `agrees`
bit; the code's `ok`, which is computed from the raw comparison values
rather than from `states` (the two differ on a malformed `chains` member
presented with faces: its state is `mismatch` while the code's `ok` stays
true; this file reads the spec's `ok`); `findings`, walks, and the
outer `present` wrapper's extra unverified entries.

## M1. Constellation commit

`mages/constellation/commit/0.1`, Conformance:

  "A conforming **consumer** (the stars chain) **MUST**, in this order, after
  framework and schema validation:
  1. Refuse a request whose `payload.moon` is not the moon now open
     (`notThisMoon`).
  2. Refuse a constellation in which a leaf repeats (`duplicateStar`). Over
     42 stars, an empty list, a passive type, or a non-hex leaf fail the
     payload schema (`malformedRequest`).
  3. Refuse a hidden star that does not re-derive (`hiddenStarNotFound`).
  4. Refuse a nonce whose work falls short of the chain's difficulty
     (`workInsufficient`).
  5. Refuse a second commit for the same mark and moon (`alreadyCommitted`).
     ...
  6. Append each star in the order given, then one `egg/find` row ...;
     record the mark and moon as committed; and answer with a `#response`."

Modelled: the chain as its open moon, the (mark, moon) pairs already
committed, and its rows; a request as a mark, a moon, a list of stars (type,
leaf) and two given bits for the hidden star and the proof of work; the
consumer's refusals in the order above, schema validation first; a moon
advancing between commits.
Not modelled: hashes and links (`hash = sha256(prev | leaf | mark | seq)`),
the egg re-derivation and the proof of work themselves (each is the given
bit), leaf hex syntax (leaves are naturals), places, the rate limit, the
envelope and signatures, mark squatting (any party may name any mark, as the
draft says), and the bit-for-bit retry absorption of SPEC §7.2 item 11: in
this model a retry of an accepted document is refused as any second commit
is.
-/

namespace TrustTasks.Mages

/-! ## M5. City Key -/

namespace CityKey

inductive State
  | absent
  | unavailable
  | «match»
  | mismatch
  deriving DecidableEq, Repr

/-- The reference reader's `state` helper. -/
def state (claimed checkable agrees : Bool) : State :=
  if !claimed then .absent
  else if !checkable then .unavailable
  else if agrees then .«match»
  else .mismatch

inductive Claim
  | kappa
  | packetProofs
  | packetsRoot
  | did
  | holds
  | chains
  deriving DecidableEq, Repr

def Claim.all : List Claim := [.kappa, .packetProofs, .packetsRoot, .did, .holds, .chains]

theorem Claim.mem_all (c : Claim) : c ∈ Claim.all := by
  cases c <;> simp [Claim.all]

/-- What the reader saw of one presented key: per claim, whether the key
makes it, whether the material to check it was given, and whether the
re-derivation agreed. -/
structure Obs where
  claimed : Claim → Bool
  given : Claim → Bool
  agrees : Claim → Bool

/-- Checkability per claim: κ and packet proofs always (they need only the
key and the packets given), the Hold never, the rest when material is given. -/
def checkable (o : Obs) : Claim → Bool
  | .kappa => true
  | .packetProofs => true
  | .holds => false
  | c => o.given c

def determine (o : Obs) (c : Claim) : State :=
  state (o.claimed c) (checkable o c) (o.agrees c)

/-- Spec: `ok` is true when no state is `mismatch`. -/
def ok (o : Obs) : Bool :=
  Claim.all.all fun c => determine o c != .mismatch

def unverified (o : Obs) : List Claim :=
  Claim.all.filter fun c => determine o c == .absent || determine o c == .unavailable

/-- `match` comes only from a claim that was made, checked, and agreed. -/
theorem state_match_iff (cl ch ag : Bool) :
    state cl ch ag = .«match» ↔ cl = true ∧ ch = true ∧ ag = true := by
  cases cl <;> cases ch <;> cases ag <;> decide

/-- `absent` is exactly an unmade claim, so never `match`. -/
theorem absent_never_match (cl ch ag : Bool) :
    (state cl ch ag = .absent ↔ cl = false) ∧ state false ch ag ≠ .«match» := by
  cases cl <;> cases ch <;> cases ag <;> decide

/-- `unavailable` is exactly a claim made without the material to check it,
so never `match`. -/
theorem unavailable_never_match (cl ch ag : Bool) :
    (state cl ch ag = .unavailable ↔ cl = true ∧ ch = false) ∧ state true false ag ≠ .«match» := by
  cases cl <;> cases ch <;> cases ag <;> decide

/-- On a presented key: a claim reads `match` only when it was claimed,
checkable, and the re-derivation agreed. -/
theorem determine_match_checked (o : Obs) (c : Claim) (h : determine o c = .«match») :
    o.claimed c = true ∧ checkable o c = true ∧ o.agrees c = true :=
  (state_match_iff _ _ _).1 h

/-- The Hold is never `match`: it is `absent` or `unavailable`. -/
theorem holds_never_match (o : Obs) :
    determine o .holds ≠ .«match» ∧
    (determine o .holds = .absent ∨ determine o .holds = .unavailable) := by
  unfold determine checkable state
  cases o.claimed .holds <;> simp

/-- A declared Hold is always on the `unverified` list. -/
theorem holds_claimed_unverified (o : Obs) (h : o.claimed .holds = true) :
    Claim.holds ∈ unverified o := by
  simp [unverified, Claim.all, determine, checkable, state, h]

theorem ok_iff_no_mismatch (o : Obs) :
    ok o = true ↔ ∀ c, determine o c ≠ .mismatch := by
  simp only [ok, List.all_eq_true, bne_iff_ne, ne_eq]
  exact ⟨fun h c => h c (Claim.mem_all c), fun h c _ => h c⟩

theorem mem_unverified_iff (o : Obs) (c : Claim) :
    c ∈ unverified o ↔ determine o c = .absent ∨ determine o c = .unavailable := by
  simp [unverified, List.mem_filter, Claim.mem_all]

/-- The spec's example request: a key stating κ, a DID with its public key,
and a packets root, presented with no packets and no faces. Every check that
could run agreed. -/
def exampleKey : Obs where
  claimed
    | .kappa | .did | .packetsRoot => true
    | _ => false
  given
    | .did => true
    | _ => false
  agrees
    | .kappa | .did => true
    | _ => false

/-- `ok` is not a permission: the example key is `ok`, yet its packets root
was claimed and never checked, and four claims are unverified. -/
theorem ok_not_permission :
    ok exampleKey = true ∧
    determine exampleKey .packetsRoot = .unavailable ∧
    unverified exampleKey = [.packetProofs, .packetsRoot, .holds, .chains] := by
  decide

/-- A two-valued reading: anything not contradicted reads as `match`. -/
def collapse : State → State
  | .mismatch => .mismatch
  | _ => .«match»

/-- Collapsing is unsound where the four states are sound: on the example
key the collapsed reading shows the packets root as `match`, though the root
was never re-derived (it was not checkable), while the four-state reading
reports it `unavailable` and lists it as unverified. Contrast
`determine_match_checked`. -/
theorem collapse_accepts_unchecked :
    collapse (determine exampleKey .packetsRoot) = .«match» ∧
    checkable exampleKey .packetsRoot = false ∧
    determine exampleKey .packetsRoot = .unavailable ∧
    Claim.packetsRoot ∈ unverified exampleKey := by
  decide

end CityKey

/-! ## M1. Constellation commit -/

namespace Constellation

/-- Star types: the thirteen deliberate types of the draft's Definitions, and
two passive ones that never leave the browser. -/
inductive StarType
  | thumbUp | proverbWrite | promiseMake | promiseKeep | recordLeave
  | noteLeave | guideWalk | islandQuest | islandStone | artefactPresent
  | workshopPresence | proverbInscribe | spellbookInscribe
  | workshopEnter | keyCharge
  deriving DecidableEq, Repr

def StarType.deliberate : StarType → Bool
  | .workshopEnter | .keyCharge => false
  | _ => true

structure Star where
  type : StarType
  leaf : Nat
  deriving DecidableEq, Repr

structure Request where
  mark : Nat
  moon : Nat
  stars : List Star
  /-- the hidden star re-derives (step 3) -/
  eggOk : Bool
  /-- the nonce meets the difficulty (step 4) -/
  workOk : Bool
  deriving DecidableEq, Repr

inductive Refusal
  | malformedRequest
  | notThisMoon
  | duplicateStar
  | hiddenStarNotFound
  | workInsufficient
  | alreadyCommitted
  deriving DecidableEq, Repr

inductive Row
  | star (mark moon : Nat) (s : Star)
  | eggFind (mark moon : Nat)
  deriving DecidableEq, Repr

structure Chain where
  openMoon : Nat
  committed : List (Nat × Nat)
  rows : List Row
  deriving DecidableEq, Repr

def leaves (r : Request) : List Nat := r.stars.map (·.leaf)

/-- The payload schema: 1 to 42 stars, deliberate types only. -/
def schemaOk (r : Request) : Bool :=
  1 ≤ r.stars.length && r.stars.length ≤ 42 && r.stars.all (·.type.deliberate)

def newRows (r : Request) : List Row :=
  r.stars.map (Row.star r.mark r.moon) ++ [Row.eggFind r.mark r.moon]

/-- The consumer, refusals in the draft's order after schema validation. -/
def commit (c : Chain) (r : Request) : Except Refusal Chain :=
  if schemaOk r = false then .error .malformedRequest
  else if r.moon ≠ c.openMoon then .error .notThisMoon
  else if ¬ (leaves r).Nodup then .error .duplicateStar
  else if r.eggOk = false then .error .hiddenStarNotFound
  else if r.workOk = false then .error .workInsufficient
  else if (r.mark, r.moon) ∈ c.committed then .error .alreadyCommitted
  else .ok { c with committed := (r.mark, r.moon) :: c.committed, rows := c.rows ++ newRows r }

/-- A chain moves by an accepted commit or by a new moon opening. -/
inductive Step : Chain → Chain → Prop
  | commit (c c' : Chain) (r : Request) : commit c r = .ok c' → Step c c'
  | newMoon (c : Chain) (m : Nat) : Step c { c with openMoon := m }

inductive Reach : Chain → Prop
  | init (m : Nat) : Reach ⟨m, [], []⟩
  | step (c c' : Chain) : Reach c → Step c c' → Reach c'

theorem commit_ok_eq {c c' : Chain} {r : Request} (h : commit c r = .ok c') :
    schemaOk r = true ∧ r.moon = c.openMoon ∧ (leaves r).Nodup ∧ r.eggOk = true ∧
    r.workOk = true ∧ (r.mark, r.moon) ∉ c.committed ∧
    c' = { c with committed := (r.mark, r.moon) :: c.committed, rows := c.rows ++ newRows r } := by
  unfold commit at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  cases h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

/-- Every accepted commit appends between 2 and 43 rows (its stars and one
`egg/find` row) after the rows already there, over stars that are all
deliberate and whose leaves are distinct. -/
theorem commit_accepted_bounds {c c' : Chain} {r : Request} (h : commit c r = .ok c') :
    c'.rows = c.rows ++ newRows r ∧
    2 ≤ (newRows r).length ∧ (newRows r).length ≤ 43 ∧
    (leaves r).Nodup ∧ (∀ s ∈ r.stars, s.type.deliberate = true) := by
  obtain ⟨hs, -, hn, -, -, -, rfl⟩ := commit_ok_eq h
  simp only [schemaOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨⟨h1, h42⟩, hd⟩ := hs
  refine ⟨rfl, ?_, ?_, hn, hd⟩ <;>
    simp only [newRows, List.length_append, List.length_map, List.length_singleton] <;> omega

/-- The chain is append-only, and the committed set only grows. -/
theorem step_append_only {c c' : Chain} (h : Step c c') :
    c.rows <+: c'.rows ∧ ∀ p ∈ c.committed, p ∈ c'.committed := by
  cases h with
  | commit _ r hc =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := commit_ok_eq hc
    exact ⟨⟨_, rfl⟩, fun p hp => List.mem_cons_of_mem _ hp⟩
  | newMoon => exact ⟨List.prefix_refl _, fun _ hp => hp⟩

/-- After any sequence of accepted commits and new moons, each (mark, moon)
has been committed at most once. -/
theorem one_commit_per_mark_moon {c : Chain} (h : Reach c) : c.committed.Nodup := by
  induction h with
  | init => exact List.nodup_nil
  | step c c' _ hs ih =>
    cases hs with
    | commit _ r hc =>
      obtain ⟨-, -, -, -, -, hnot, rfl⟩ := commit_ok_eq hc
      exact List.nodup_cons.2 ⟨hnot, ih⟩
    | newMoon => exact ih

/-- Once a (mark, moon) is committed, no later commit under it is accepted,
whatever its stars, egg or nonce. -/
theorem second_commit_refused {c c' c'' : Chain} {r r' : Request}
    (h : commit c r = .ok c') (hm : r'.mark = r.mark) (hn : r'.moon = r.moon) :
    commit c' r' ≠ .ok c'' := by
  intro h'
  obtain ⟨-, -, -, -, -, -, rfl⟩ := commit_ok_eq h
  obtain ⟨-, -, -, -, -, hnot, -⟩ := commit_ok_eq h'
  exact hnot (by simp [hm, hn])

/-- The draft's example: three stars in the moon of 9 November 2026 (moon
20261109 here), the hidden star found and the work met. -/
def honest : Request where
  mark := 7
  moon := 20261109
  stars := [⟨.thumbUp, 1⟩, ⟨.proverbWrite, 2⟩, ⟨.guideWalk, 3⟩]
  eggOk := true
  workOk := true

/-- Non-vacuity: on a fresh chain with that moon open the honest commit is
accepted, appends four rows and spends the mark's constellation for the moon;
the same commit again is refused `alreadyCommitted`. -/
theorem honest_commit_accepted :
    commit ⟨20261109, [], []⟩ honest =
      .ok ⟨20261109, [(7, 20261109)], newRows honest⟩ ∧
    (newRows honest).length = 4 ∧
    commit ⟨20261109, [(7, 20261109)], newRows honest⟩ honest = .error .alreadyCommitted :=
  ⟨by rfl, rfl, by rfl⟩

end Constellation

end TrustTasks.Mages
