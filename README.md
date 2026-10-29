# Trust Tasks formal models

Lean 4 models of Trust Tasks protocol families and ceremonies. Core Lean only (no Mathlib); the trusted base is the Lean kernel plus `propext`, `Classical.choice` and `Quot.sound`.

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

Check: `lake build`, `lake env lean Checks.lean` (axiom footprints; no `sorry`), `lake env leanchecker --fresh TrustTasks` (independent kernel replay).

Prepared with agent assistance under the author's direction and reviewed by the author; every claim is kernel-checked and reproducible from this directory.
