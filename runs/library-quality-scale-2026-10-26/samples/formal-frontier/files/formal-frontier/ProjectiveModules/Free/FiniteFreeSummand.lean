/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.SummandCancellation
public import ProjectiveModules.Module.ProjectiveComplement
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Ranks and cancellation of direct summands

Over a semiring with the rank condition, a finite basis of a module equivalent
to a product bounds the size of a finite basis of its first factor. Over a
stably finite semiring, a finite-free module cannot be equivalent to itself
times a nontrivial semimodule. For rings, the same conclusion extends to
finite projective modules, and finite-coordinate product equivalences
characterize both ring conditions.

The forward statements allow independent universes and arbitrary complementary
semimodules. The coordinate characterizations quantify complements in the
ring's universe; their converse uses the kernel/product splitting available
for modules over rings. No splitting of arbitrary semiring surjections into
products is asserted. All modules here are left modules; right modules over
`R` are obtained by using the opposite ring `Rᵐᵒᵖ`, without a commutativity
assumption.

## References

* C. A. Weibel, *The K-book*, Exercises I.1.2–I.1.4 (motivation for finite-free
  direct-summand conditions).
* Mathlib, `Mathlib.LinearAlgebra.InvariantBasisNumber` and
  `Mathlib.LinearAlgebra.FiniteDimensional.Basic` (rank and endomorphism interfaces).
* Projective Modules, `Module.Projective.prodKerEquivOfSurjective` and
  `Module.Projective.exists_finite_complement_linearEquiv` (ring-module splits
  and finite-projective complements).
-/

@[expose] public section

universe uR uM uN uP uι uκ

open Module

namespace RankCondition

/-- Under the rank condition, a finite basis of a direct-summand target has
no more elements than a finite basis of the source. -/
theorem card_le_of_linearEquiv_prod
    (R : Type uR) [Semiring R] [RankCondition R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    (basisM : Basis ι R M) (basisN : Basis κ R N)
    (e : M ≃ₗ[R] (N × P)) : Fintype.card κ ≤ Fintype.card ι := by
  let projection : (ι → R) →ₗ[R] (κ → R) :=
    basisN.equivFun.toLinearMap.comp ((LinearMap.fst R N P).comp
      (e.toLinearMap.comp basisM.equivFun.symm.toLinearMap))
  exact card_le_of_surjective R projection
    (basisN.equivFun.surjective.comp
      ((LinearMap.fst_surjective (R := R) (M := N) (M₂ := P)).comp
        (e.surjective.comp basisM.equivFun.symm.surjective)))

end RankCondition

namespace IsStablyFiniteRing

/-- A finite-free semimodule over a stably finite semiring cancels from a
product with an arbitrary complementary semimodule. -/
theorem subsingleton_of_linearEquiv_prod
    (R : Type uR) [Semiring R] [IsStablyFiniteRing R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    (e : M ≃ₗ[R] (M × P)) : Subsingleton P := by
  let : IsDedekindFiniteMonoid (Module.End R M) := inferInstance
  exact Module.End.subsingleton_of_linearEquiv_prod R e

/-- A finite projective module over a stably finite ring cancels from a
product with an arbitrary complementary module. -/
theorem subsingleton_of_finite_projective_linearEquiv_prod
    (R : Type uR) [Ring R] [IsStablyFiniteRing R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    {P : Type uP} [AddCommGroup P] [Module R P]
    (e : M ≃ₗ[R] (M × P)) : Subsingleton P := by
  classical
  obtain ⟨n, Q, addQ, moduleQ, _, ⟨basis⟩⟩ :=
    Module.Projective.exists_finite_complement_linearEquiv (R := R) (P := M)
  let _ : AddCommGroup Q := addQ
  let _ : Module R Q := moduleQ
  let : Module.Finite R (M × Q) := Module.Finite.equiv basis.symm
  let : Module.Free R (M × Q) := Module.Free.of_equiv basis.symm
  let stabilized : (M × Q) ≃ₗ[R] ((M × Q) × P) :=
    (e.prodCongr (LinearEquiv.refl R Q)).trans <|
      (LinearEquiv.prodAssoc R M P Q).trans <|
        ((LinearEquiv.refl R M).prodCongr (LinearEquiv.prodComm R P Q)).trans <|
          (LinearEquiv.prodAssoc R M Q P).symm
  exact subsingleton_of_linearEquiv_prod R stabilized

end IsStablyFiniteRing

/-- For a ring, the rank condition is equivalent to the finite-coordinate
inequality for every product equivalence with a complement in the ring's
universe. This characterizes the finite-free summand condition of Weibel,
*The K-book*, Exercise I.1.2. -/
theorem rankCondition_iff_le_of_fin_linearEquiv_fin_prod
    (R : Type uR) [Ring R] :
    RankCondition R ↔
      ∀ (m n : ℕ) (P : Type uR) [AddCommGroup P] [Module R P],
        ((Fin m → R) ≃ₗ[R] ((Fin n → R) × P)) → n ≤ m := by
  constructor
  · intro condition m n P _ _ e
    let : RankCondition R := condition
    simpa only [Fintype.card_fin] using
      (RankCondition.card_le_of_linearEquiv_prod R
        (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) e)
  · intro condition
    refine ⟨fun {m n} f hf ↦ ?_⟩
    let : Module.Projective R (Fin n → R) := inferInstance
    let split := Module.Projective.prodKerEquivOfSurjective f hf
    exact condition m n (LinearMap.ker f) split.symm

/-- For a ring, stable finiteness is equivalent to cancellation of finite
coordinate modules from products with complements in the ring's universe.
This is the finite-free direct-summand condition of Weibel, *The K-book*,
Exercises I.1.3–I.1.4. -/
theorem isStablyFiniteRing_iff_subsingleton_of_fin_linearEquiv_fin_prod
    (R : Type uR) [Ring R] :
    IsStablyFiniteRing R ↔
      ∀ (n : ℕ) (P : Type uR) [AddCommGroup P] [Module R P],
        ((Fin n → R) ≃ₗ[R] ((Fin n → R) × P)) → Subsingleton P := by
  constructor
  · intro condition n P _ _ e
    let : IsStablyFiniteRing R := condition
    exact IsStablyFiniteRing.subsingleton_of_linearEquiv_prod R e
  · intro condition
    apply isStablyFiniteRing_iff_injective_of_surjective.mpr
    intro n f hf
    let split := Module.Projective.prodKerEquivOfSurjective f hf
    have : Subsingleton (LinearMap.ker f) :=
      condition n (LinearMap.ker f) split.symm
    exact LinearMap.ker_eq_bot.mp Submodule.eq_bot_of_subsingleton
