# Trust Tasks formal models

Lean 4 models of Trust Tasks protocol families and ceremonies. Core Lean only (no Mathlib); the trusted base is the Lean kernel plus `propext`, `Classical.choice` and `Quot.sound`.

## Models

| file | family or ceremony | read at; raised in | result | theorems |
|---|---|---|---|---|
| [MyTerms](TrustTasks/MyTerms.lean) | `myterms/propose` + comprehension ceremony (IEEE 7012) | [spec#43](https://github.com/trustoverip/dtgwg-trust-tasks-spec/issues/43), [tf#904](https://github.com/trustoverip/dtgwg-trust-tasks-tf/issues/904) | a closed `decision` suffices for completion; issuer binding and round limit needed | 13 |
| [Ceremony](TrustTasks/Ceremony.lean) | ceremony completion predicate | [spec#52](https://github.com/trustoverip/dtgwg-trust-tasks-spec/issues/52) | presence-only completion accepts a refused seal; declared read + party binding sound | 7 |
| [Roster](TrustTasks/Roster.lean) | agreements.info roster × `understanding/seal` | [tf#904](https://github.com/trustoverip/dtgwg-trust-tasks-tf/issues/904) at 83af40f | **gap**: a counter seals untested terms; coverage check fixes it; duplicate `id`s | 7 |
| [VtcRoles](TrustTasks/VtcRoles.lean) | `vtc/members/*` role assigners | main 2e3149010; [tf#1218](https://github.com/trustoverip/dtgwg-trust-tasks-tf/issues/1218) | **gap**: removal bypasses the last-assigner guard; removal's effect on the entry read both ways | 8 |
| [Onboarding](TrustTasks/Onboarding.lean) | `vtc/member-onboarding` ceremony | main 2e3149010; [spec#52](https://github.com/trustoverip/dtgwg-trust-tasks-spec/issues/52) | **gap**: `reciprocate` never required; no presence-only predicate states the intent | 6 |
| [Rulings](TrustTasks/Rulings.lean) | four rulings | [spec#31](https://github.com/trustoverip/dtgwg-trust-tasks-spec/issues/31) (#36–#39) | each ruling sound; the rejected alternative fails | 27 |
| [TaskConsent](TrustTasks/TaskConsent.lean) | `task-consent/*` threshold approval | main 101a51d8d; [tf#1219](https://github.com/trustoverip/dtgwg-trust-tasks-tf/issues/1219) | confirmation; **gap**: an unmeetable `minApprovals` is accepted and never runs | 16 |
| [AclDelegation](TrustTasks/AclDelegation.lean) | `acl/*/0.3` delegation | main 101a51d8d; [tf#1220](https://github.com/trustoverip/dtgwg-trust-tasks-tf/issues/1220) | cascade confirmed; **gap**: a third-party amendment escapes `delegatedBy`; "queued" may stay in force | 25 |
| [JoinRequests](TrustTasks/JoinRequests.lean) | `vtc/join-requests/*` lifecycle | main 101a51d8d; [tf#1221](https://github.com/trustoverip/dtgwg-trust-tasks-tf/issues/1221) | **gap**: the ceremony cannot complete under `submit/0.3`; a maintainer cannot close a deferred request | 20 |
| [VettingCount](TrustTasks/VettingCount.lean) | vetting statement counting | main 101a51d8d; [tf#1222](https://github.com/trustoverip/dtgwg-trust-tasks-tf/issues/1222) | **gap**: caps read globally are non-monotone; on one reading a notice swallows the issuer's withdrawal | 24 |
| [DidRollback](TrustTasks/DidRollback.lean) | `did-management/did/*` rollback, register | main 101a51d8d; [tf#1223](https://github.com/trustoverip/dtgwg-trust-tasks-tf/issues/1223) | **gap**: rollback rewrites published versions and depends on timing; register drops the extension check | 17 |
| [VotingTrustees](TrustTasks/VotingTrustees.lean) | `voting/trustees/*` | main 101a51d8d | confirmation: the threshold counting holds as written | 13 |

A **gap** is a counterexample admitted by the rules as written, stated in the file with the spec text it reads and, where one exists, a proven fix. Quoted spec text is from the upstream commit named. Every gap has been raised upstream: `tf#` is an issue or PR on trustoverip/dtgwg-trust-tasks-tf, `spec#` an issue on trustoverip/dtgwg-trust-tasks-spec.

## TrustTasks/MyTerms.lean

IEEE Std 7012-2025 (MyTerms) carried as `myterms/propose`, after the outline on trustoverip/dtgwg-trust-tasks-spec#43, with a comprehension exchange in front of it as in trustoverip/dtgwg-trust-tasks-tf#904. Prior work: trustoverip/dtgwg-trust-tasks-tf#856 and its implementation in mitchuski/star-key (`packages/core/src/vtc/myterms.ts`, `agreements.ts`).

| theorem | what it shows |
|---|---|
| `decision_iff_contract` | under the response rule, `decision = accepted` exactly when a contract identifier is present |
| `decision_member_suffices` | reading `decision = accepted` on a performed step gives a contract, the agreement the request named, and that agreement in the roster |
| `presence_completion_unsound` | a completion check that only sees a response present accepts a rejected engagement |
| `followup_bound` | a performed follow-up is by the original proposer, to the same entity, takes exactly the offered alternative, and is not answered with another alternative |
| `at_most_one_followup` | at most one follow-up is performed per answered request (§5.2.2) |
| `issuer_binding_needed` | without the issuer binding, a third party takes the alternative offered to someone else and gets a contract |
| `round_limit_needed` | without the one-follow-up rule, a rejected follow-up is retried until accepted |
| `ceremony_sound` | ceremony completion gives a contract between the party that passed the exchange and the party that recorded it, for a roster agreement |
| `exchange_binding_needed` | without binding the exchange's parties to the proposal's, one party's comprehension completes another's agreement |
| `ceremony_sound_nonvacuous` | the soundness theorem applies to a full propose → alternative → follow-up → accepted run |

Not modelled: signatures (a request's issuer is taken as authenticated by the envelope), digests, time, transport, the roster's neutrality, `myterms/accepted`, and what the agreements mean.

`contractId` follows the spec#43 outline of `myterms/propose`. In `understanding/seal/0.1` as of #904 head 83af40f the response carries no contract identifier; an accepted response is tied to the agreement it seals by `taskContext` and `taskDigestMultibase` over the request, which plays the same part in `decision_member_suffices`.

## TrustTasks/Ceremony.lean

A ceremony definition's completion predicate, after trustoverip/dtgwg-trust-tasks-tf#904 open item 7: today a step in a completion predicate is satisfied when the step is present (`ceremony.meta.schema.json`, `$defs.Predicate`), so a refused seal completes `understanding/proof-of-understanding/0.1`. The proposal: a step may declare the success-response member and value its completion reads (e.g. `/payload/decision` = `accepted`), and every step's parties come from one role binding, the one the opening step fixes.

| theorem | what it shows |
|---|---|
| `today_completes_refused_seal` | today's completion accepts an enactment whose seal was refused; the proposed completion rejects it |
| `complete_refines_today` | every enactment complete under the proposal is complete today |
| `complete_sound` | completion gives, for every step, a success response between the bound parties carrying the step's declared value |
| `pou_sound` | for Proof of Understanding: an offer, a passed exchange and an accepted seal, the exchange and seal between the offer's two parties |
| `pou_sound_nonvacuous` | the soundness theorem applies to an honest enactment (`acceptedRun_complete`) |
| `party_binding_needed` | reading the declared members without the party binding lets one party's comprehension complete another party's agreement |

Not modelled: the `anyOf` and `threshold` combinators, optional steps, `perRole` multiplicity, `maxRounds`, `prev` ordering, `maxDuration`, nested ceremonies, evidence levels, signatures and digests. Each terminal document is taken to have passed SPEC §4.9.4 checks 1, 2 and 4.

## TrustTasks/Roster.lean

The MyTerms roster as published at agreements.info (the machine-readable JSON of each relationship agreement, version 1.1, read 2026-11-12), read against `understanding/seal/0.1` on trustoverip/dtgwg-trust-tasks-tf#904 (head 83af40f). The SD-BASE line, by `purposes`, is a chain: SD-BASE ⊂ SD-BASE-A ⊂ SD-BASE-AT ⊂ SD-BASE-ATP ⊂ SD-BASE-ATP3. The seal spec notes that a counter can name terms the exchange never tested; this file makes that concrete and proves a completion rule that closes it without a second exchange.

| theorem | what it shows |
|---|---|
| `sealed_in_roster` | under #904's rules, a sealed agreement is in the roster |
| `counter_escapes_exchange` | tested on SD-BASE, countered with SD-BASE-ATP3, follow-up accepted: admissible and complete, and the binding terms permit third-party sharing, tracking and profiling the tested terms do not |
| `covered_sound` | completion that also checks the tested agreement covers every purpose of the sealed one gives a roster agreement the individual was tested on, purpose by purpose |
| `covered_refuses_broad_counter` | that completion refuses the SD-BASE → SD-BASE-ATP3 engagement |
| `covered_admits_narrow_counter` | it still admits a counter to narrower terms (SD-BASE-ATP → SD-BASE-A) with no second exchange |
| `covered_on_accept` | a direct acceptance always passes it |
| `code_not_unique` | two published agreements carry the JSON `id` "SD-BASE" with different purposes, so naming an agreement by `id` does not fix what was agreed |

Not modelled: signatures, digests, issuer binding and round limits (MyTerms.lean, Ceremony.lean), prohibitions as distinct from absent purposes, and the exchange's questions.

## TrustTasks/VtcRoles.lean

Who may still assign roles in a Verifiable Trust Community (upstream main 2e3149010). `vtc/members/role/set/0.1` item 10 refuses a move that would leave no live holder of `vtc.roles.assign`, or fewer than the consent threshold, because "a community that could no longer grant or consent to authority could not repair itself"; `vtc/members/purge/0.1` has a `lastAdministrator` guard with no override. `vtc/members/admin-remove/0.1` and `vtc/members/self-remove/0.1` remove a member (`disposition: purge` included) with no such guard, and the registry reads removal's effect on the access-control entry both ways: `vtc/members/admit/0.1` says a former member has no entry, `vtc/members/make-membership/0.1` gives the example of one whose entry was kept.

| theorem | what it shows |
|---|---|
| `remove_last_holder` | today the last holder of `vtc.roles.assign` can be removed, or remove themselves |
| `no_recovery` | a community with no live holder never regains one: item 10's "could not repair itself", proved |
| `removal_bypasses_item10` | at two holders and a threshold of two, item 10 refuses either demotion, while removal takes the community below its threshold and then to no holder |
| `guarded_floor` | with item 10's guard on removal too, a community at or above its floor stays there |
| `guarded_refuses_last` | guarded, the last holder cannot be removed, at any threshold |
| `guarded_nonvacuous` | the guard still lets a holder go when enough remain |
| `removed_still_assigns` | if removal keeps the entry, a removed administrator still passes item 1 and counts toward item 10's floor |
| `removed_ending_entry_cannot_assign` | if removal ends the entry, it does not; hence the fix pairs the guard with removal ending the entry |

Not modelled: identities beyond the holder count, other capabilities and qualifiers (items 6 and 9), approval and parking (items 11 to 13), serialisation (item 14; steps are atomic), and `vtc/roles/define`.

## TrustTasks/Onboarding.lean

`vtc/member-onboarding/0.1` (upstream main 2e3149010) against trustoverip/dtgwg-trust-tasks-spec#52. Its step descriptions say an enactment completes on a rejection at `decide`, or on an approval followed by `reciprocate`; its completion predicate is `allOf[apply, decide, anyOf[decide, reciprocate]]`, read by presence.

| theorem | what it shows |
|---|---|
| `published_is_apply_and_decide` | the published predicate is `apply ∧ decide`: the `anyOf` is absorbed |
| `reciprocate_never_required` | an approved member who never reciprocates completes, as a rejected applicant does; the intent completes only the second |
| `presence_only_blind` | a presence-only predicate gives the same answer for any two enactments with the same steps present |
| `no_presence_predicate` | no predicate today's schema can state matches the ceremony's intent |
| `proposed_is_intended` | with one declared read of `decide`'s `decision` (spec#52's proposal), the intent is stated exactly |
| `proposed_nonvacuous` | that predicate completes a rejection and a reciprocated approval, and not an unreciprocated approval |

Not modelled: optional steps other than `reciprocate`, rounds, ordering, `maxDuration`, evidence, and every step's content but `decide`'s.

## TrustTasks/Rulings.lean

Four rulings requested on trustoverip/dtgwg-trust-tasks-spec#31, each a small model with the theorem that captures it and a counterexample under the alternative the ruling rejected.

| theorem | what it shows |
|---|---|
| `Hold.hold_next_step_sound` | #36: with a hold answered as a next step, the operation runs at most once however many requests the producer sends, and every error the producer holds means a refused request |
| `Hold.hold_next_step_nonvacuous` | a held request is approved, runs, and is answered |
| `Hold.hold_as_error_runs_twice` | with a hold answered as an error, the producer reissues while the first request is still held, and the operation runs twice |
| `Verdict.verdict_as_data_sound` | #37: a reader recovers every situation from the reply, and a reply is outcome evidence exactly when the task ran, a refusal included |
| `Verdict.verdict_as_data_nonvacuous` | a refusal is read back as a refusal and is citable |
| `Verdict.refusal_as_denied_conflates` | a refusal sent as `permissionDenied` is indistinguishable from "may not ask" |
| `Verdict.refusal_as_code_misread` | a refusal sent as a task-specific code reads as "not performed" to a reader that does not know the code, and is not evidence |
| `Verdict.denial_as_verdict_conflates` | a refusal to run sent as a negative verdict gives a requester that may not ask a citable "refused" |
| `AlreadyInState.set_idempotent` | #38: a repeated set leaves the store unchanged and succeeds, reporting no change |
| `AlreadyInState.set_ok_iff_exists` | a set succeeds exactly when the target exists, and leaves it in the requested state |
| `AlreadyInState.create_ok_iff_created` | a create succeeds exactly when the target did not exist |
| `AlreadyInState.already_in_state_nonvacuous` | create, set, repeated set and duplicate create on one store |
| `AlreadyInState.set_strict_retry_loop` | a set that errors on a state that already holds never succeeds under retry |
| `AlreadyInState.create_lax_misleads` | a create that succeeds on a duplicate tells a second requester it succeeded when the target is the first requester's |
| `AlreadyInState.set_upsert_phantom` | a set that succeeds on a missing target brings a target into being |
| `Defaults.required_sound` | #39: with governance members required, the evaluated constraint is the governance framework's |
| `Defaults.required_refuses_omission` | an omitted governance member is `malformedRequest` |
| `Defaults.required_nonvacuous` | a complete constraint is evaluated as sent, and an approval meeting it passes |
| `Defaults.defaulted_quorum_unsound` | with `policy/_shared/0.3`'s defaults, the requester's own single approval passes where governance requires three others |
| `Defaults.omission_indistinguishable` | the evaluation cannot tell an omission from an explicit choice of the default |
| `Defaults.shared_default_wrong_somewhere` | any default a shared component fixes is wrong for some community |
| `Defaults.default_sound_iff_governance` | a default is harmless for a community exactly when it equals that community's governance value |

Not modelled: see the comment at the head of each section of the file.

## TrustTasks/TaskConsent.lean

Threshold approval in `task-consent/request/0.1` and `task-consent/decision/0.2` (upstream main 101a51d8d). Decision/0.2 states the invariant: nothing executes without a single-use decision by a currently-enrolled approver over the exact digest, with policy and enrolment re-checked at execution.

| theorem | what it shows |
|---|---|
| `execution_sound` | an execution is the first and only one, runs the approved digest, and is carried by at least `minApprovals` distinct approvers who are in the set, are not the excluded requester, and are enrolled at that moment |
| `at_most_once` | item 13: at most one execution, of the approved digest |
| `deny_final` | item 9: once a deny is accepted, the task never runs |
| `granted_closed` | once granted, the request is decided and takes no further decision (`noPending`), so no deny lands between grant and execution |
| `execution_sound_nonvacuous` | two of three approvers (the third the excluded requester) approve and the task runs |
| `distinct_needed` | without idempotent recording, one approver's two approvals meet a threshold of two |
| `consume_at_execution_needed` | with the challenge consumed on receipt, the executor's retry runs the task twice |
| `recheck_needed` | without item 14, an approver revoked after approving still carries the task |
| `deny_closes_needed` | without item 9, a deny is answered and the task still runs |
| `exclusion_needed` | items 5 and 6 at receipt are subsumed by item 14; without both, the requester carries its own task |
| `unmeetable_accepted_never_runs` | a request whose `minApprovals` exceeds its eligible approvers (the schema allows it) is prompted, records approvals, and never runs |
| `runs_only_if_feasible` | a check at request time that enough distinct eligible enrolled approvers exist refuses nothing that could run |

Not modelled: signatures and evidence, per-approver challenges, `actionId`, `statePin`, time and `expiresAt`, policy beyond the approver set and `excludeRequester`, enrolment during the window, `task-consent/granted`, and the consent surface.

## TrustTasks/AclDelegation.lean

`acl/*/0.3` and CONVENTIONS §9 (upstream main 101a51d8d): a delegated entry never exceeds its granter and "MUST NOT retain authority its delegator has since lost". `acl/update/0.3` item 5 bounds an amendment by the amending party only, and item 10 keeps `delegatedBy` unchanged, so an amended entry can exceed the entry that `delegatedBy` says bounds it.

| theorem | what it shows |
|---|---|
| `within_preserved` | with amendments also bounded by `delegatedBy`, every reachable entry stays within the entry its `delegatedBy` names |
| `cascade_within` | re-evaluating the changed entry's delegates, and theirs in turn, restores the invariant |
| `cascade_minimal` | on an ACL that already satisfies it, re-evaluation changes nothing |
| `within_nonvacuous` | 0 → 1 → 2, then 0 is narrowed: both delegates are narrowed |
| `grant_bound_needed` | without grant item 4, an entry exceeds its granter |
| `reeval_needed` | without re-evaluation, a delegate keeps what its delegator lost |
| `one_level_insufficient` | re-evaluating only direct delegates leaves the second level exceeding the first; grant item 9 and §9 already require the cascade |
| `amend_escapes_delegator` | a conforming third-party widening (update items 5 and 10) exceeds `delegatedBy`; once the amender is removed, nothing re-evaluates it |
| `fix_refuses_amend` | bounding the amendment by `delegatedBy` as well refuses it |
| `queued_in_force_retains` | an entry queued for review and left in force (grant item 9 forbids only leaving it "silently") keeps what its delegator lost; one suspended while queued does not |

Not modelled: roles and ceilings, the separate axes and their shapes, qualifiers, additive capabilities, expiry, purposes, keys, approve authority, re-delegation permission, `lastAuthorityProtected`, compare-and-swap, the policy choice among withdraw, narrow and queue, and re-delegation on amendment.

## TrustTasks/JoinRequests.lean

The `vtc/join-requests` lifecycle (upstream main 101a51d8d): `submit/0.1` and `0.3`, `decide/0.1`, `supplement/0.1`, `withdraw/0.1`, over `status/0.1`'s five states, with `vtc/member-onboarding/0.1` read over it. The ceremony pins the retired `submit/0.1`; under `submit/0.3` a request decided at submission or by a supplement never reaches `decide`, which answers `notPending`. And `withdraw/0.1` sends a maintainer to the decision task, which refuses a deferred request.

| theorem | what it shows |
|---|---|
| `final_absorbing` | `approved`, `rejected`, `withdrawn` are final |
| `closings_le_one` | at most one step closes a request: `withdraw` and `decide` cannot both succeed |
| `admission_once` / `admitted_once` | a run admits at most once, and ends `approved` exactly when it did |
| `review_admits_by_decide` | under `review`, every admission is an administrator's `decide` |
| `deferred_exits` | `deferred` has exits (`supplement`, `withdraw`); the ceremony's note saying it has none is stale |
| `notPending_needed`, `supplementDeferred_needed`, `withdrawOpen_needed`, `reviewNoAllow_needed` | each rule is needed |
| `lifecycle_nonvacuous` | deferred → supplemented → referred → approved; and a withdrawal |
| `ceremony_v01_completes` | under `submit/0.1` every decided request completes the ceremony |
| `ceremony_v03_never_completes` | under `submit/0.3` an admission or refusal at submission or by supplement never completes it |
| `proposed_iff_decided` | a completion reading the deciding verdict holds exactly when the request was decided, on either version |
| `proposed_nonvacuous` | it completes those runs, and not a referred or withdrawn one |
| `community_cannot_close_deferred` | administrator steps leave a deferred request deferred |
| `fixed_closes_deferred` | the fix: `decide` may reject, never approve, a deferred request, and keeps every property above |

Not modelled: several requests per applicant, identities, proofs, criteria content, hidden vetting, polls, replay windows, `maxDuration`, retention sweeps, and ceremony steps other than `apply` and `decide`.

## TrustTasks/VettingCount.lean

Counting vetting statements (upstream main 101a51d8d): `vtc/join-requests/manifest/0.4`'s `vetting` object, `vetting/session/0.1`'s pairwise rule, and `vtc/vetting/revoke-statement/0.1`, read with the facts `vetting/show/0.1` records.

| theorem | what it shows |
|---|---|
| `global_sound` / `subset_sound` | a satisfied requirement gives `minStatements` distinct vetters, each with a counted statement |
| `counts_spec` | a counted statement is eligible, of an accepted method, in age, not pairwise, with no matching notice |
| `global_sound_persons` | the vetters are distinct people wherever the community links non-pairwise DIDs correctly |
| `third_party_notice_no_effect` | a notice not from the issuer never withdraws |
| `perVetter_needed`, `filters_needed`, `pairwise_needed`, `matchSender_needed` | each rule is needed (otherwise one vetter with two DIDs meets a minimum of two) |
| `nonvacuous`, `issuer_notice_withdraws` | the manifest's example criterion is met, and the issuer's notice withdraws |
| `floor_outside_accepted_unsat(_global)` | a floor on an unaccepted method is unsatisfiable, as community item 4 and applicant item 1 say |
| `global_not_monotone` | under `vetting/show/0.1`'s reading of the caps and commitment, one more eligible statement fails a passing application |
| `subset_monotone` / `global_implies_subset` | the reading "some counted set meets every check" is monotone and accepts everything the other does |
| `squat_swallows_withdrawal` | reading item 7's "repeated notice" as item 3's key (id and digest), another member's earlier notice makes the issuer's a no-op |
| `keyFull_issuer_effective` / `keyFull_idempotent` | keying on id, digest and sender: the issuer's notice always takes effect, and repeats still change nothing |

Not modelled: signatures, digest computation, `statementType`, claims beyond the commitment, document classes, invitations, hidden vetting, how DIDs are linked (`owner` given), and item 5's re-evaluation. Held statement ids are taken as unique.

## TrustTasks/DidRollback.lean

DID rollback against append-only publishing (upstream main 101a51d8d). `did/publish/0.1` (retired) requires a new chain to be "a valid extension of the prior one"; `did/rollback/0.1` discards published entries above an absolute `targetVersion`, with no expected head in its payload, and says which entries it discards "depends on when it executes"; `did/register/0.1`, which supersedes publish, says only "the new log replaces the old".

| theorem | what it shows |
|---|---|
| `publish_append_only` | under publish alone, every log held is a prefix of every later one |
| `publish_version_stable` | under publish alone, a version once resolvable keeps its entry |
| `rollback_rewrites_published` | publish versions 1–4, roll back to 3, publish a different version 4: two documents at version 4, each resolvable in turn |
| `any_discard_permits_rewrite` | any rollback that discards an entry lets that version be rewritten through publish's check |
| `extension_check_needed` | register's rule as written rewrites version 2 with no rollback |
| `range_rule_needed` | without the lower bound, a rollback to 0 discards the genesis entry |
| `delayed_rollback_discards_unseen` | a rollback executed after a publish it never saw discards that entry |
| `count_cas_sound` / `count_cas_refuses_delayed` | an expected `versionCount` suffices when only publishes intervene |
| `count_cas_insufficient` | it does not when another rollback intervenes |
| `head_cas_sound` / `head_cas_refuses` | an expected head digest committing to the chain discards exactly what the requester saw |
| `cas_nonvacuous` | an undelayed rollback passes both checks |
| `guarded_append_only` / `guarded_refuses_rewrite` | refusing rollback below the highest resolved version restores append-only |
| `guarded_rollback_noop` | since publish resolves at once, that guard makes every rollback a no-op: a design choice, not a fix |

Not modelled: signatures and entry validity, ownership and admin authority, disabled slots, `force`, deletion, witnesses, resolver caches, and time beyond step order.

## TrustTasks/VotingTrustees.lean

Trustee key generation and threshold decryption (upstream main 101a51d8d, `voting/_shared/0.1/CONVENTIONS.md` §9.6–9.7). A confirmation model: the counting the rules rely on holds as written.

| theorem | what it shows |
|---|---|
| `formed_sound` | a formed key has at least `t` distinct qualified dealers, every complaint against each one justified |
| `formed_has_honest_dealer` | with fewer than `t` corrupt trustees, some qualified dealer is honest |
| `qualified_check_needed` | without the "fewer than `t` qualify" rule, a corrupt trustee complaining of everyone at the deadline makes the key its own |
| `justified_restores` | answered complaints are void, all qualify, the key forms |
| `no_key_when_t_gt_n` | with `t > n` no key ever forms (create's bound protects liveness) |
| `opens_has_honest` / `corrupt_cannot_open` | opening needs an honest trustee's partial; fewer than `t` corrupt trustees cannot open |
| `distinct_needed` | counted without distinctness, one trustee's partial sent twice meets `t = 2` |
| `opens_nonvacuous` | partials from two distinct trustees open at `t = 2` |

Not modelled: the group, polynomials, commitments, shares and proofs; transport keys; target authorization; timing; and several DIDs held by one party.

Check: `./check.sh` builds every model, prints each theorem's axiom footprint (`Checks.lean`), fails on `sorry`, on any axiom beyond the three above, or on a theorem missing from `Checks.lean`, and replays the kernel independently (`leanchecker --fresh`).

Prepared with agent assistance under the author's direction and reviewed by the author; every claim is kernel-checked and reproducible from this directory.
