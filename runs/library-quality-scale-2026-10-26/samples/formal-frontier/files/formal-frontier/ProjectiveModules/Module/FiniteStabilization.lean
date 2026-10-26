/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.ProjectiveComplement
public import Mathlib.LinearAlgebra.Prod

/-!
# Replacing a finite projective common stabilizer by a finite free one

If `M × T` and `N × T` are linearly equivalent and `T` is finite projective,
then `M` and `N` become linearly equivalent after adjoining the same standard
finite free module. The modules `M` and `N` need not be finite, free or
projective, and their carrier universes are independent.

The proof uses `Module.Projective.exists_finite_complement_linearEquiv`:
choose a complement `Q` with `T × Q` equivalent to `Fin n → R`, adjoin `Q`
to the supplied equivalence, and reassociate and transport the products using
Mathlib's linear equivalences. No projectivity of `Q` is needed. The natural
number `n` is an existential witness, not a prescribed rank or a rank
invariant. No cancellation or nontriviality condition on the ring is used.

## References

- C. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  for the finite-projective direct-summand argument in stabilization.
- Projective Modules' projective-complement formalization and Mathlib's
  product linear-equivalence API.
-/

@[expose] public section

universe uR uM uN uT

namespace Module.Projective

variable {R : Type uR} [Ring R]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N]
variable {T : Type uT} [AddCommGroup T] [Module R T]

/-- An equivalence with a finite projective common stabilizer yields an
equivalence with a common standard finite free stabilizer.

This is the direct-summand argument for finite projectives used in
stabilization; see Weibel, *The K-book*, Chapter II. There are no finiteness,
freeness or projectivity hypotheses on `M` or `N`. -/
theorem exists_free_stabilizer [Module.Finite R T] [Module.Projective R T]
    (e : (M × T) ≃ₗ[R] (N × T)) :
    ∃ n : ℕ, Nonempty ((M × (Fin n → R)) ≃ₗ[R] (N × (Fin n → R))) := by
  obtain ⟨n, Q, addQ, moduleQ, _, ⟨f⟩⟩ :=
    exists_finite_complement_linearEquiv (R := R) (P := T)
  let _ : AddCommGroup Q := addQ
  let _ : Module R Q := moduleQ
  refine ⟨n, ⟨?_⟩⟩
  exact ((LinearEquiv.refl R M).prodCongr f.symm) ≪≫ₗ
    (LinearEquiv.prodAssoc R M T Q).symm ≪≫ₗ
    (e.prodCongr (LinearEquiv.refl R Q)) ≪≫ₗ
    LinearEquiv.prodAssoc R N T Q ≪≫ₗ
    ((LinearEquiv.refl R N).prodCongr f)

end Module.Projective
