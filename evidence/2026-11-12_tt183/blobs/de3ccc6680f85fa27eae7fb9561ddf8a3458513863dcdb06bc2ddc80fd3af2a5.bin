import TrustTasks.MyTerms

/-
A model of a ceremony definition's completion predicate, and of a proposed
change to it that lets completion read one declared member of a step's
success response and binds every step's parties to one role binding.

Context: trustoverip/dtgwg-trust-tasks-tf#904, open item 7 of the
2026-10-28 review: "The ceremony's completion predicate still can't read
response content. A refused seal still 'completes' the ceremony; only the
relying-party note catches it. Letting completion read `decision` is a
ceremony-schema change in the canonical spec."

What today's format says (dtgwg-trust-tasks-tf `ceremonies/ceremony.meta.schema.json`,
`$defs.Predicate`): a step name in a completion predicate "is satisfied when
that step is present in the enactment", and the `optional` member's
description says a completed enactment is checkable "from document metadata
alone, with no interpretation of any task's payload semantics". The step's
`issuer` and `recipient` are role names, bound to VIDs at enactment.
SPEC §4.9.4 (Evidence That a Cited Exchange Completed) gives the four checks
that make a terminal document outcome evidence for one exchange; check 3
requires a declared success response, check 4 that it verifies under the
initiating document's `recipient`.

What is modelled: an enactment as the list of terminal documents the verifier
holds, one or more per step; each document's kind (success response, error
response, next step), the parties of its exchange, and its payload as a list
of (JSON Pointer, string value) pairs. A ceremony definition as an ordered
list of steps, each with an issuer role, a recipient role and, under the
proposal, an optional declared (member, value) its completion reads. The
completion predicate is the `allOf` over every step, which is what
`understanding/proof-of-understanding/0.1` uses.

What is not: the other combinators (`anyOf`, `threshold`), optional steps,
`perRole` multiplicity and `maxRounds`, `prev` ordering, `maxDuration`,
nested ceremonies, the receipt and evidence levels, signatures and digests.
Each `Doc` is taken to have already passed §4.9.4 checks 1, 2 and 4 for its
own exchange: `requester` is the initiating document's `issuer`, and
`responder` is its `recipient`, under whose key the terminal document verifies.
-/

namespace TrustTasks.Ceremony

open TrustTasks.MyTerms (Party)

abbrev StepName := String
abbrev Role := String
/-- A JSON Pointer into the terminal document, e.g. `/payload/decision`. -/
abbrev Path := String
abbrev Val := String

/-- The reply that ends (or, for a next step, holds open) one step's exchange
(SPEC §4.12, §8, §8.6). Only `response` is a success response. -/
inductive Kind
  | response
  | error
  | nextStep
  deriving DecidableEq, Repr

/-- One step of a ceremony definition. `reads` is the proposed member: the
success-response member and the value completion requires there. `none`
reads nothing, which is today's behaviour for every step. -/
structure StepDef where
  name : StepName
  issuer : Role
  recipient : Role
  reads : Option (Path × Val) := none
  deriving Repr

/-- A ceremony definition: its steps, the opening step first. -/
structure Def where
  steps : List StepDef
  deriving Repr

/-- A terminal document of one step, as the verifier holds it. -/
structure Doc where
  step : StepName
  kind : Kind
  requester : Party
  responder : Party
  payload : List (Path × Val)
  deriving Repr

abbrev Enactment := List Doc

/-- The document carries the declared value at the declared member. -/
def Doc.reads (t : Doc) : Option (Path × Val) → Prop
  | none => True
  | some (p, v) => t.payload.lookup p = some v

instance : (t : Doc) → (r : Option (Path × Val)) → Decidable (t.reads r)
  | _, none => isTrue trivial
  | t, some (p, v) => inferInstanceAs (Decidable (t.payload.lookup p = some v))

/-! ### Today's completion and the proposed one -/

/-- Today: every step reached a success response. No content is read and no
party is compared across steps. -/
def completeToday (d : Def) (e : Enactment) : Prop :=
  ∀ s ∈ d.steps, ∃ t ∈ e, t.step = s.name ∧ t.kind = .response

/-- One step done under the role binding `β`: a success response carrying the
declared value, exchanged between the parties `β` gives the step's roles. -/
def stepDone (β : Role → Party) (e : Enactment) (s : StepDef) : Prop :=
  ∃ t ∈ e, t.step = s.name ∧ t.kind = .response ∧ t.reads s.reads ∧
    t.requester = β s.issuer ∧ t.responder = β s.recipient

/-- Proposed: one role binding for the whole enactment, under which every step
reached a success response carrying its declared value. Since the opening
step is one of the steps, the binding is the one the opening step fixes. -/
def complete (d : Def) (e : Enactment) : Prop :=
  ∃ β : Role → Party, ∀ s ∈ d.steps, stepDone β e s

/-- The proposal with the declared read but without the party binding. -/
def completeUnbound (d : Def) (e : Enactment) : Prop :=
  ∀ s ∈ d.steps, ∃ t ∈ e, t.step = s.name ∧ t.kind = .response ∧ t.reads s.reads

/-- The proposal only removes completions: every enactment complete under it is
complete today, so existing definitions that declare no read lose nothing
they relied on except completions across mismatched parties. -/
theorem complete_refines_today {d : Def} {e : Enactment} (h : complete d e) :
    completeToday d e := by
  obtain ⟨β, hβ⟩ := h
  intro s hs
  obtain ⟨t, ht, hn, hk, _⟩ := hβ s hs
  exact ⟨t, ht, hn, hk⟩

/-- General soundness: completion gives, for every step, a success response
between the bound parties that carries the step's declared value. -/
theorem complete_sound {d : Def} {e : Enactment} (h : complete d e) :
    ∃ β : Role → Party, ∀ s ∈ d.steps, ∃ t ∈ e, t.step = s.name ∧ t.kind = .response ∧
      (∀ p v, s.reads = some (p, v) → t.payload.lookup p = some v) ∧
      t.requester = β s.issuer ∧ t.responder = β s.recipient := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β, fun s hs => ?_⟩
  obtain ⟨t, ht, hn, hk, hr, hi, hrc⟩ := hβ s hs
  refine ⟨t, ht, hn, hk, fun p v hpv => ?_, hi, hrc⟩
  rw [hpv] at hr
  exact hr

/-! ### Proof of Understanding (dtgwg-trust-tasks-tf#904) -/

/-- `understanding/proof-of-understanding/0.1` as it stands: three steps, all
issued by the joining party to the host, no member read. -/
def pouToday : Def :=
  { steps := [
      { name := "offer", issuer := "joining-party", recipient := "host" },
      { name := "exchange", issuer := "joining-party", recipient := "host" },
      { name := "seal", issuer := "joining-party", recipient := "host" }] }

/-- The same definition with the proposed reads: the exchange step's
`outcome` is `understood` and the seal step's `decision` is `accepted`. -/
def pou : Def :=
  { steps := [
      { name := "offer", issuer := "joining-party", recipient := "host" },
      { name := "exchange", issuer := "joining-party", recipient := "host",
        reads := some ("/payload/outcome", "understood") },
      { name := "seal", issuer := "joining-party", recipient := "host",
        reads := some ("/payload/decision", "accepted") }] }

/-- Joining party 10, host 20, the comprehension passed, the seal refused. -/
def refusedRun : Enactment :=
  [⟨"offer", .response, 10, 20, []⟩,
   ⟨"exchange", .response, 10, 20, [("/payload/outcome", "understood")]⟩,
   ⟨"seal", .response, 10, 20, [("/payload/decision", "refused")]⟩]

/-- Today's completion accepts an enactment whose seal was refused, under both
the definition as it stands and the one with reads declared (today's
predicate ignores them); the proposed completion rejects it, and no seal
response in it says `accepted`. -/
theorem today_completes_refused_seal :
    completeToday pouToday refusedRun ∧ completeToday pou refusedRun ∧
    ¬ complete pou refusedRun ∧
    ¬ ∃ t ∈ refusedRun, t.step = "seal" ∧ t.payload.lookup "/payload/decision" = some "accepted" := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [pouToday, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl, rfl⟩
  · intro s hs
    simp only [pou, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl, rfl⟩
  · rintro ⟨β, hβ⟩
    obtain ⟨t, ht, hn, _, hr, _⟩ :=
      hβ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp only [refusedRun, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp_all [Doc.reads]
  · rintro ⟨t, ht, hn, hd⟩
    simp only [refusedRun, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp_all

/-- Soundness for Proof of Understanding: completion gives an offer, a passed
exchange and an accepted seal, the exchange and the seal between the same
requester and responder as the offer, that is, the same joining party and
the same host. -/
theorem pou_sound {e : Enactment} (h : complete pou e) :
    ∃ o ∈ e, ∃ x ∈ e, ∃ s ∈ e,
      o.step = "offer" ∧ x.step = "exchange" ∧ s.step = "seal" ∧
      o.kind = .response ∧ x.kind = .response ∧ s.kind = .response ∧
      x.payload.lookup "/payload/outcome" = some "understood" ∧
      s.payload.lookup "/payload/decision" = some "accepted" ∧
      x.requester = o.requester ∧ x.responder = o.responder ∧
      s.requester = o.requester ∧ s.responder = o.responder := by
  obtain ⟨β, hβ⟩ := h
  obtain ⟨o, ho, hon, hok, _, hoi, hor⟩ := hβ _ (List.mem_cons_self ..)
  obtain ⟨x, hx, hxn, hxk, hxr, hxi, hxrc⟩ :=
    hβ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain ⟨s, hs, hsn, hsk, hsr, hsi, hsrc⟩ :=
    hβ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  exact ⟨o, ho, x, hx, s, hs, hon, hxn, hsn, hok, hxk, hsk, hxr, hsr,
    hxi.trans hoi.symm, hxrc.trans hor.symm, hsi.trans hoi.symm, hsrc.trans hor.symm⟩

/-- An honest enactment: joining party 10, host 20, passed and accepted. -/
def acceptedRun : Enactment :=
  [⟨"offer", .response, 10, 20, []⟩,
   ⟨"exchange", .response, 10, 20, [("/payload/outcome", "understood")]⟩,
   ⟨"seal", .response, 10, 20, [("/payload/decision", "accepted")]⟩]

theorem acceptedRun_complete : complete pou acceptedRun := by
  refine ⟨fun r => if r = "host" then 20 else 10, ?_⟩
  intro s hs
  simp only [pou, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., rfl, rfl, trivial, by decide, by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, rfl, by decide,
      by decide, by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      rfl, rfl, by decide, by decide, by decide⟩

/-- The soundness theorem applies to an honest enactment. -/
theorem pou_sound_nonvacuous :
    ∃ o ∈ acceptedRun, ∃ x ∈ acceptedRun, ∃ s ∈ acceptedRun,
      o.step = "offer" ∧ x.step = "exchange" ∧ s.step = "seal" ∧
      s.payload.lookup "/payload/decision" = some "accepted" ∧
      x.requester = o.requester ∧ s.requester = o.requester := by
  obtain ⟨o, ho, x, hx, s, hs, h1, h2, h3, _, _, _, _, h4, h5, _, h6, _⟩ :=
    pou_sound acceptedRun_complete
  exact ⟨o, ho, x, hx, s, hs, h1, h2, h3, h4, h5, h6⟩

/-! ### The party binding is needed -/

/-- Party 11 passes the comprehension exchange with host 20; party 10 makes the
offer and has its seal accepted. Every declared value is present. -/
def swappedRun : Enactment :=
  [⟨"offer", .response, 10, 20, []⟩,
   ⟨"exchange", .response, 11, 20, [("/payload/outcome", "understood")]⟩,
   ⟨"seal", .response, 10, 20, [("/payload/decision", "accepted")]⟩]

/-- Reading the declared members without binding parties completes an
enactment in which one party's comprehension completes another party's
agreement: the agreement holder (10) never showed understanding. With the
binding, the same enactment is not complete. This is the ceremony-schema
counterpart of `TrustTasks.MyTerms.exchange_binding_needed`. -/
theorem party_binding_needed :
    completeUnbound pou swappedRun ∧ ¬ complete pou swappedRun := by
  constructor
  · intro s hs
    simp only [pou, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., rfl, rfl, trivial⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, rfl, by decide⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        rfl, rfl, by decide⟩
  · intro h
    obtain ⟨o, ho, x, hx, s, hs, hon, hxn, _, _, _, _, _, _, hxi, _, _, _⟩ := pou_sound h
    simp only [swappedRun, List.mem_cons, List.mem_nil_iff, or_false] at ho hx
    rcases ho with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> simp_all

end TrustTasks.Ceremony
