/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicQuotient

/-!
# A common primewise source for procyclic maps

Changing the universe of the lifted p-adic coordinates gives a continuous
multiplicative equivalence of primewise products. Precomposing the map
associated to any element of a profinite group with this equivalence gives a
map from a single, fixed source, compatible with continuous homomorphisms.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (primewise quotient models as context for generator maps, not this comparison
  theorem).
- Mathlib, `ULift` equivalences and profinite completion used by
  `ProcyclicQuotient` (maps from completed integers and primewise factors).
-/

@[expose] public section

open Function

universe u v w

namespace ProfiniteGrp

/-- Primality for the p-adic coordinate indexed by a prime. -/
local instance primeFact (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Change the universe of each p-adic coordinate without changing its value. -/
noncomputable def primewisePadicChangeUniverse :
    primewisePadic.{u} ≃ₜ* primewisePadic.{v} := by
  let F (p : Nat.Primes) : ULift.{u} ℤ_[p.1] ≃ₜ+ ULift.{v} ℤ_[p.1] := by
    let homeomorph : ULift.{u} ℤ_[p.1] ≃ₜ ULift.{v} ℤ_[p.1] :=
      (Homeomorph.ulift (X := ℤ_[p.1])).trans
        (Homeomorph.ulift (X := ℤ_[p.1])).symm
    exact ContinuousAddEquiv.mk
      (AddEquiv.ulift.trans AddEquiv.ulift.symm)
      homeomorph.continuous homeomorph.symm.continuous
  exact primewisePadicRingMultiplicativeEquiv.{u}.symm |>.trans
    ((continuousAddEquivPiCongrRight F).toMultiplicative |>.trans
      primewisePadicRingMultiplicativeEquiv.{v})

/-- Universe change preserves the ordinary p-adic value at every prime. -/
@[simp]
theorem primewisePadicChangeUniverse_apply_down
    (x : primewisePadic.{u}) (p : Nat.Primes) :
    ((primewisePadicChangeUniverse.{u,v} x) p).toAdd.down = (x p).toAdd.down := by
  rfl

/-- The primewise integer diagonal commutes with universe change. -/
@[simp]
theorem primewisePadicChangeUniverse_diagonal (n : ℤ) :
    primewisePadicChangeUniverse.{u,v} (primewisePadicDiagonal.{u} n) =
      primewisePadicDiagonal.{v} n := by
  funext p
  apply Multiplicative.toAdd.injective
  apply ULift.down_injective
  simp only [primewisePadicChangeUniverse_apply_down,
    primewisePadicDiagonal_apply]
  rfl

/-- Universe change carries the canonical topological generator to itself. -/
@[simp]
theorem primewisePadicChangeUniverse_generator :
    primewisePadicChangeUniverse.{u,v} primewisePadicGenerator =
      primewisePadicGenerator := by
  exact primewisePadicChangeUniverse_diagonal 1

/-- Changing universe to itself gives the identity. -/
@[simp]
theorem primewisePadicChangeUniverse_self :
    primewisePadicChangeUniverse.{u,u} = ContinuousMulEquiv.refl _ := by
  apply ContinuousMulEquiv.ext
  intro x
  funext p
  apply Multiplicative.toAdd.injective
  apply ULift.down_injective
  exact primewisePadicChangeUniverse_apply_down.{u,u} x p

/-- Reversing universe change gives its inverse. -/
@[simp]
theorem primewisePadicChangeUniverse_symm :
    primewisePadicChangeUniverse.{u,v}.symm =
      primewisePadicChangeUniverse.{v,u} := by
  apply ContinuousMulEquiv.ext
  intro x
  apply primewisePadicChangeUniverse.{u,v}.injective
  funext p
  apply Multiplicative.toAdd.injective
  apply ULift.down_injective
  simp only [primewisePadicChangeUniverse_apply_down,
    ContinuousMulEquiv.apply_symm_apply]

/-- Successive changes of universe agree with direct change. -/
@[simp]
theorem primewisePadicChangeUniverse_trans :
    primewisePadicChangeUniverse.{u,v}.trans primewisePadicChangeUniverse.{v,w} =
      primewisePadicChangeUniverse.{u,w} := by
  apply ContinuousMulEquiv.ext
  intro x
  funext p
  apply Multiplicative.toAdd.injective
  apply ULift.down_injective
  simp only [ContinuousMulEquiv.trans_apply, primewisePadicChangeUniverse_apply_down]

/-- The map from the universe-zero primewise product determined by an arbitrary
element of a profinite group. It need not be surjective. -/
noncomputable def primewisePadicBaseMapOfGenerator (G : ProfiniteGrp.{u}) (g : G) :
    primewisePadic.{0} →ₜ* G :=
  (primewisePadicMapOfGenerator G g).comp
    (primewisePadicChangeUniverse.{0,u} : primewisePadic.{0} →ₜ* primewisePadic.{u})

/-- The common-source map takes the integer diagonal to powers of its element. -/
@[simp]
theorem primewisePadicBaseMapOfGenerator_diagonal
    (G : ProfiniteGrp.{u}) (g : G) (n : ℤ) :
    primewisePadicBaseMapOfGenerator G g (primewisePadicDiagonal.{0} n) = g ^ n := by
  simp [primewisePadicBaseMapOfGenerator]

/-- A topological generator yields a surjection from the common source. -/
theorem primewisePadicBaseMapOfGenerator_surjective
    (G : ProfiniteGrp.{u}) (g : G) (hg : IsTopologicalGenerator G g) :
    Surjective (primewisePadicBaseMapOfGenerator G g) := by
  exact (primewisePadicMapOfGenerator_surjective G g hg).comp
    primewisePadicChangeUniverse.{0,u}.surjective

/-- The common-source maps are natural under arbitrary continuous homomorphisms,
without generation, injectivity or surjectivity assumptions. -/
theorem primewisePadicBaseMapOfGenerator_naturality
    (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (f : G →ₜ* H) (g : G) :
    f.comp (primewisePadicBaseMapOfGenerator G g) =
      primewisePadicBaseMapOfGenerator H (f g) := by
  apply ContinuousMonoidHom.ext
  have equality := (denseRange_primewisePadicDiagonal.{0}).equalizer
    (f.continuous_toFun.comp (primewisePadicBaseMapOfGenerator G g).continuous_toFun)
    (primewisePadicBaseMapOfGenerator H (f g)).continuous_toFun
    (by
      funext n
      change f (primewisePadicBaseMapOfGenerator G g (primewisePadicDiagonal n)) =
        primewisePadicBaseMapOfGenerator H (f g) (primewisePadicDiagonal n)
      rw [primewisePadicBaseMapOfGenerator_diagonal,
        primewisePadicBaseMapOfGenerator_diagonal, map_zpow])
  exact congrFun equality

end ProfiniteGrp
