import Lake
open Lake DSL

-- Lean models of Trust Tasks protocol families and ceremonies.
-- Core Lean only: no Mathlib; the trusted base is the kernel plus the
-- three standard axioms.

package TrustTasks where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib TrustTasks where
