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

Check: `lake build`, `lake env lean Checks.lean` (axiom footprints; no `sorry`), `lake env leanchecker --fresh TrustTasks` (independent kernel replay).

Prepared with agent assistance under the author's direction and reviewed by the author; every claim is kernel-checked and reproducible from this directory.
