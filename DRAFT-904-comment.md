<!-- draft reply for trustoverip/dtgwg-trust-tasks-tf#904 — not posted; [model link] to fill once the model is public -->

On the open question upthread (a required, closed `decision` as what the ceremony's completion reads): a small Lean model of `myterms/propose`, following the #43 outline, with a comprehension exchange in front of it, says yes, with two conditions. [model link]

- **`decision` is enough** when the response schema ties members to it: `contractId` and `agreement` present exactly on `accepted`, `alternative` exactly on `alternative`. Then `decision = accepted` gives a contract for the agreement the request named, and that agreement is in the roster. A completion check that sees only a response present accepts a rejected engagement, which is the gap the current ceremony text discloses.
- **The follow-up needs an issuer binding.** Without "the follow-up's issuer is the original proposer", a third party can take the alternative offered to someone else and get a contract. The same holds for the ceremony: completion has to bind the exchange's parties to the proposal's, or one party's comprehension completes another's agreement.
- **One follow-up per answered request** is provable from "no performed follow-up to the same `respondsTo` exists yet" (`roundsExhausted`). Without it, a rejected follow-up can be retried until accepted.

Each rule has a concrete run showing it is needed, and the soundness theorem is applied to a full propose → alternative → follow-up → accepted run. Core Lean, standard axioms only; signatures, digests and the roster's neutrality are outside the model.

Related prior work on the same family: #856 (`agreements/*`, IEEE 7012 carried today in `join-requests/submit` extensions), with a running implementation in star-key against join.mages.city. Glad to co-author the `myterms/*` rework alongside the host-governed family and the comprehension family.
