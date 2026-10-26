/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.LinearAlgebra.FiniteProjective.Charpoly
public import AlgebraicGroups.Scheme.AffineEquivalenceRelation

@[expose] public section

/-!
# Integrality for constant-rank affine equivalence relations

For an affine internal equivalence relation whose structural coordinate map is
finite projective of constant local rank, the canonical finite-projective
characteristic polynomial of multiplication has invariant coefficients.
Consequently the object ring is integral over the equalizer of the two
coordinate maps.

The cartesian composition square compares the two scalar extensions of
multiplication by `t x` through mixed scalar actions and `TargetCopy`;
intertwining and base-change naturality give invariant coefficients without a
global basis. The polynomial uses a split-presentation Fredholm construction.
The coefficient-invariance argument itself does not use the stated local-rank
hypothesis; local rank is needed for monicity and Cayley--Hamilton in the
integrality conclusion. Reflexivity supplies injectivity of the other leg.

## References

* The Stacks Project, Lemmas 39.23.2 and 39.23.4
  ([tags 03BH](https://stacks.math.columbia.edu/tag/03BH) and
  [03BJ](https://stacks.math.columbia.edu/tag/03BJ)), establish invariant
  norms and integrality for affine finite locally free groupoids.
* `AlgebraicGroups.Scheme.AffineEquivalenceRelation` supplies the cartesian
  composition coordinates and injectivity from reflexivity;
  `AlgebraicGroups.LinearAlgebra.FiniteProjective.Charpoly` supplies the
  finite-projective characteristic polynomial and its naturality, monicity
  and Cayley--Hamilton results.
* Mathlib, `Mathlib.LinearAlgebra.Matrix.SchurComplement`
  (`Matrix.det_one_sub_mul_comm`), underlies the independence of the
  split-presentation Fredholm polynomial used here.
-/

open CategoryTheory Limits
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry.AffineEquivalenceRelation

open Module.FiniteProjective

attribute [local instance] RingHomInvPair.of_ringEquiv

universe uC u

/-- The canonical fixed-rank finite-projective characteristic polynomial of
multiplication by `t x` has invariant coefficients.  The proof uses only the
cartesian composition square and no global basis. This is the coefficient
invariance argument of Stacks Project
[Lemma 39.23.2, tag 03BH](https://stacks.math.columbia.edu/tag/03BH),
expressed through scalar-extension naturality. The displayed local-rank
hypothesis is not used for coefficient invariance. -/
lemma finiteProjectiveCharpoly_coeff_invariant
    {C : Type uC} {A B : Type u}
    [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] [Algebra A B] [IsScalarTower C A B]
    [Module.Finite A B] [Module.Projective A B]
    (s t : A →ₐ[C] B) (hs : IsScalarTower.toAlgHom C A B = s)
    (hrel : EquivalenceRelation (specMap s) (specMap t))
    (n : ℕ)
    (_hrank : ∀ (J : Ideal A) [J.IsMaximal],
      Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl B) = n)
    (x : A) : ∀ k,
      s ((finiteProjectiveCharpoly A B n
        (Algebra.lmul A B (t x))).coeff k) =
      t ((finiteProjectiveCharpoly A B n
        (Algebra.lmul A B (t x))).coeff k) := by
  let E := TargetCopy B
  let _ : Algebra C E :=
    (targetCopyMap (algebraMap C B)).toAlgebra
  let _ : Algebra A E := (targetCopyMap t.toRingHom).toAlgebra
  let _ : IsScalarTower C A E := targetCopy_isScalarTower t
  let D := E ⊗[A] B
  let _ : Algebra C D := Algebra.TensorProduct.leftAlgebra
  let _ : Algebra E D := Algebra.TensorProduct.leftAlgebra
  let _ : IsScalarTower C E D := by infer_instance
  obtain ⟨p0, p1, c, hp0, hp1, hp0s, hcs, hct, hcart⟩ :=
    exists_composition_coordinates s t hs hrel
  have hsRing : s.toRingHom = algebraMap A B := by
    rw [← hs]
    rfl
  have hbase : c.toRingHom.comp (algebraMap A B) =
      p1.toRingHom.comp (algebraMap A B) := by
    rw [← hsRing]
    exact congr_arg AlgHom.toRingHom hcs
  have hcartRing : IsPullback
      (specMapRing c.toRingHom) (specMapRing p1.toRingHom)
      (specMapRing (algebraMap A B)) (specMapRing (algebraMap A B)) := by
    rw [← hsRing]
    exact hcart
  let _ : Algebra B D := p1.toRingHom.toAlgebra
  obtain ⟨qB, hqB⟩ := exists_tensorLinearEquiv_of_isPullback
    c.toRingHom p1.toRingHom hbase hcartRing
  let e : B ≃+* E := TargetCopy.ringEquiv.symm
  have hp1e (b : B) : p1 b = algebraMap E D (e b) := by
    rw [hp1 b]
    rfl
  let q : (B ⊗[A] B) ≃ₛₗ[RingHomClass.toRingHom e] D :=
    { qB with
      map_smul' := fun b z ↦ by
        change qB (b • z) = e b • qB z
        rw [qB.map_smul]
        rw [Algebra.smul_def, Algebra.smul_def]
        change p1 b * qB z = algebraMap E D (e b) * qB z
        rw [hp1e] }
  let f : Module.End A B := Algebra.lmul A B (t x)
  let fB : Module.End B (B ⊗[A] B) := f.baseChange B
  let fE : Module.End E D := f.baseChange E
  have hfE : fE = Algebra.lmul E D (p0 (t x)) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add y z hy hz => simp_all [fE, mul_add]
    | tmul y z =>
      change y ⊗ₜ[A] (t x * z) = p0 (t x) * (y ⊗ₜ[A] z)
      rw [hp0]
      simp
  have hq : ∀ z, q.toLinearMap (fB z) = fE (q.toLinearMap z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add y z hy hz => simp_all [fB, fE, mul_add]
    | tmul b₀ b₁ =>
      change qB (b₀ ⊗ₜ[A] (t x * b₁)) =
        fE (qB (b₀ ⊗ₜ[A] b₁))
      rw [hqB, hqB, hfE]
      change p1 b₀ * c (t x * b₁) =
        p0 (t x) * (p1 b₀ * c b₁)
      have hctx : c (t x) = p0 (t x) := DFunLike.congr_fun hct x
      rw [map_mul, hctx]
      ring
  have hchar := finiteProjectiveCharpoly_map_ringEquiv_of_intertwine
    (n := n) e q fB fE hq
  intro k
  apply e.injective
  have hcharCoeff := congr_arg (fun p : Polynomial E ↦ p.coeff k) hchar
  rw [Polynomial.coeff_map] at hcharCoeff
  have hsCoeff := finiteProjectiveCharpoly_coeff_baseChange
    (R := A) (S := B) n k f
  have htCoeff := finiteProjectiveCharpoly_coeff_baseChange
    (R := A) (S := E) n k f
  calc
    e (s ((finiteProjectiveCharpoly A B n f).coeff k)) =
        e (algebraMap A B ((finiteProjectiveCharpoly A B n f).coeff k)) := by
          exact congr_arg e (DFunLike.congr_fun hsRing _)
    _ = e ((finiteProjectiveCharpoly B (B ⊗[A] B) n fB).coeff k) := by
      rw [hsCoeff]
    _ = (finiteProjectiveCharpoly E D n fE).coeff k := hcharCoeff
    _ = algebraMap A E ((finiteProjectiveCharpoly A B n f).coeff k) := htCoeff.symm
    _ = e (t ((finiteProjectiveCharpoly A B n f).coeff k)) := rfl

/-- A finite projective affine internal equivalence relation of fixed local
rank makes its object ring integral over the equalizer of its two coordinate
maps. This follows the invariant-polynomial and Cayley--Hamilton argument of
Stacks Project
[Lemma 39.23.4, tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ),
using a basis-free finite-projective characteristic polynomial. -/
lemma isIntegral_equalizer_of_projective_constantRank
    {C : Type uC} {A B : Type u}
    [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] [Algebra A B] [IsScalarTower C A B]
    [Module.Finite A B] [Module.Projective A B]
    (s t : A →ₐ[C] B) (hs : IsScalarTower.toAlgHom C A B = s)
    (hrel : EquivalenceRelation (specMap s) (specMap t))
    (n : ℕ)
    (hrank : ∀ (J : Ideal A) [J.IsMaximal],
      Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl B) = n)
    (x : A) : _root_.IsIntegral (AlgHom.equalizer s t) x := by
  have hcoeff :=
    finiteProjectiveCharpoly_coeff_invariant
      s t hs hrel n hrank x
  have ht : Function.Injective t :=
    (maps_injective_of_equivalenceRelation s t hrel).2
  exact isIntegral_equalizer_of_finiteProjectiveCharpoly_coeff_invariant
    s t hs ht n hrank x hcoeff

end AlgebraicGeometry.AffineEquivalenceRelation
