/-
Who may still assign roles in a Verifiable Trust Community, read against
upstream trustoverip/dtgwg-trust-tasks-tf main (2e3149010).

`vtc/members/role/set/0.1` item 10: a move that ends the subject's
`vtc.roles.assign` "MUST be refused with `lastRoleAssigner` when no other live
holder of it would remain, or when fewer would remain than the community's
consent threshold for authority-conferring grants requires. A community that
could no longer grant or consent to authority could not repair itself."
Item 1: the requester's `vtc.roles.assign` is "read from the signer's live
access-control entry". `vtc/members/purge/0.1` refuses with
`lastAdministrator`, a guard with "no override flag".

`vtc/members/admin-remove/0.1` and `vtc/members/self-remove/0.1` remove a
member, `disposition: purge` included, and state no such guard. What removal
does to the access-control entry is not stated, and the registry reads it
both ways: `vtc/members/admit/0.1` describes a former member as "a removed
member record and no access-control entry"; `vtc/members/make-membership/0.1`
gives the example of "a former member whose entry was kept when he was
removed". This file shows each reading breaks item 10's purpose, and that
item 10's guard on removal, with removal ending the entry, keeps it.

What is modelled: the number of live holders of `vtc.roles.assign`, and, for
the second reading, whether one removed member keeps an entry. Not modelled:
identities beyond that, other capabilities and their qualifiers (items 6 and
9), approval and parking (items 11 to 13), serialisation (item 14, taken as
given: steps are atomic), `vtc/roles/define`, and dispositions other than
their effect on the entry.
-/

namespace TrustTasks.VtcRoles

/-- Item 10's floor: at least one holder, and at least the consent
threshold `t`. -/
def floor (t : Nat) : Nat := max t 1

/-- One step, on the count `n` of live holders of `vtc.roles.assign`.
`set` is `role/set` under items 1 and 10; `remove` is admin- or self-removal
of a holder ending the entry, guarded (`g = true`) by item 10 or not
(today); removing a non-holder leaves the count as it is. -/
inductive Step (t : Nat) (g : Bool) : Nat → Nat → Prop
  /-- Conferring `vtc.roles.assign`: the requester must hold it (item 1). -/
  | confer {n : Nat} : 1 ≤ n → Step t g n (n + 1)
  /-- Ending a holder's `vtc.roles.assign` by `role/set`: item 10. The
  requester is another holder (items 1 and 2), so two are live. -/
  | withdraw {n : Nat} : 2 ≤ n → floor t ≤ n - 1 → Step t g n (n - 1)
  /-- Removing a holder whose entry removal ends. -/
  | remove {n : Nat} : 1 ≤ n → (g = true → floor t ≤ n - 1) → Step t g n (n - 1)
  /-- Anything that does not touch `vtc.roles.assign`. -/
  | other {n : Nat} : Step t g n n

inductive Reach (t : Nat) (g : Bool) (n0 : Nat) : Nat → Prop
  | refl : Reach t g n0 n0
  | step {m n : Nat} : Reach t g n0 m → Step t g m n → Reach t g n0 n

/-! ### Reading 1: removal ends the entry, with no guard (today) -/

/-- The last holder removes themselves (or is removed with `purge`). -/
theorem remove_last_holder (t : Nat) : Step t false 1 0 :=
  Step.remove (Nat.le_refl 1) (fun h => by cases h)

/-- A community with no live holder stays without one: no step can confer
`vtc.roles.assign` again. This is item 10's "could not repair itself",
proved. -/
theorem no_recovery {t : Nat} {g : Bool} {n : Nat} (h : Reach t g 0 n) : n = 0 := by
  induction h with
  | refl => rfl
  | step _ s ih =>
      subst ih
      cases s with
      | confer h1 => cases h1
      | withdraw h2 => cases h2
      | remove h1 => cases h1
      | other => rfl

/-- At two holders and a consent threshold of two, item 10 refuses to end
either holder's power, yet removal takes the community below its threshold
and then to no holder, from which `no_recovery` applies. -/
theorem removal_bypasses_item10 :
    ¬ floor 2 ≤ 2 - 1 ∧ Reach 2 false 2 1 ∧ Reach 2 false 2 0 := by
  have h1 : Reach 2 false 2 1 :=
    Reach.step Reach.refl (Step.remove (by decide) (fun h => by cases h))
  exact ⟨by decide, h1, Reach.step h1 (remove_last_holder 2)⟩

/-! ### The fix: item 10's guard on removal, removal ending the entry -/

/-- With every removal guarded by item 10, a community at or above its floor
stays there. -/
theorem guarded_floor {t n0 n : Nat} (h0 : floor t ≤ n0) (h : Reach t true n0 n) :
    floor t ≤ n := by
  induction h with
  | refl => exact h0
  | step _ s ih =>
      cases s with
      | confer _ => exact Nat.le_succ_of_le ih
      | withdraw _ hf => exact hf
      | remove _ hg => exact hg rfl
      | other => exact ih

/-- Guarded, the last holder cannot be removed, whatever the threshold. -/
theorem guarded_refuses_last (t : Nat) : ¬ Step t true 1 0 := by
  intro s
  cases s with
  | withdraw h2 => cases h2 with | step h => cases h
  | remove _ hg =>
      have := hg rfl
      simp [floor] at this

/-- The guard still lets a holder go when enough remain. -/
theorem guarded_nonvacuous : Reach 1 true 3 2 ∧ Reach 2 true 3 2 :=
  ⟨Reach.step Reach.refl (Step.remove (by decide) (fun _ => by decide)),
   Reach.step Reach.refl (Step.remove (by decide) (fun _ => by decide))⟩

/-! ### Reading 2: removal keeps the entry -/

/-- One subject: whether its member record is live, and whether it holds a
live access-control entry carrying `vtc.roles.assign`. -/
structure Subject where
  member : Bool
  entry : Bool
  deriving DecidableEq, Repr

/-- Item 1 reads the entry, not the membership. -/
def item1 (s : Subject) : Bool := s.entry

/-- Removal as `make-membership`'s example has it: the record goes, the entry
stays. -/
def removeKeepingEntry (s : Subject) : Subject := { s with member := false }

/-- Removal as `admit` describes a former member: no entry. -/
def removeEndingEntry (_ : Subject) : Subject := { member := false, entry := false }

/-- Under the second reading, a removed administrator still passes item 1:
it may still move other members' roles, and it still counts toward item 10's
live holders, so the floor can be met by people the community has removed. -/
theorem removed_still_assigns :
    let a : Subject := ⟨true, true⟩
    (removeKeepingEntry a).member = false ∧ item1 (removeKeepingEntry a) = true := by
  decide

/-- Under the first reading it does not, which is why the fix pairs the
guard with removal ending the entry. -/
theorem removed_ending_entry_cannot_assign (s : Subject) :
    item1 (removeEndingEntry s) = false := rfl

end TrustTasks.VtcRoles
