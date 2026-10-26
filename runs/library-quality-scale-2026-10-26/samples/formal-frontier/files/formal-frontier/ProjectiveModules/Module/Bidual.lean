/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Finiteness.Projective

import Mathlib.LinearAlgebra.Pi

/-!
# Ordinary-coefficient bidual evaluation

For a left module `M` over a semiring `R`, the first Hom `M →ₗ[R] R` carries
pointwise right multiplication, expressed as an `Rᵐᵒᵖ`-module structure.
Its ordinary-coefficient second Hom carries pointwise left multiplication by `R`.
Evaluation is Mathlib's mixed-scalar `LinearMap.flip` applied to the identity.
No right action on `M` is required, and the scalar and source universes are
independent.

`LinearMap.bidualEvalEquiv` bundles this evaluation for finite projective modules.
For commutative semirings, restriction of the second Hom's inner scalars compares
it with Mathlib's `Module.evalEquiv` without changing the coefficient carrier.

## References

The evaluation construction and its mixed-scalar linearities use Mathlib's
bilinear-map and opposite-module APIs. The commutative finite-projective case
is Mathlib's `Module.IsReflexive` and `Module.evalEquiv`.
For the finite-projective duality context, see Charles A. Weibel,
*The K-book*, Chapter I, §2.
-/

@[expose] public section

universe uR uM uN uF

namespace LinearMap

universe uι

/-- The coordinate projections generate the right-regular module of forms on
finite Pi. The opposite coefficient acts on the right, so its underlying
coefficient is `f (Pi.single i 1)`, not a coefficient acting on the left. -/
private theorem pi_form_eq_sum
    (R : Type uR) (ι : Type uι) [Semiring R] [Fintype ι] [DecidableEq ι]
    (f : (ι → R) →ₗ[R] R) :
    f = ∑ i, MulOpposite.op (f (Pi.single i 1)) •
      (LinearMap.proj i : (ι → R) →ₗ[R] R) := by
  apply (LinearEquiv.piRing R R ι Rᵐᵒᵖ).injective
  funext j
  simp [LinearEquiv.piRing_apply, sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, Pi.single_apply]

/-- Raw mixed-scalar evaluation is bijective on a finite Pi module. Its
inverse sends a bidual form `Φ` to the coordinates `i ↦ Φ (LinearMap.proj i)`.
This uses the coordinate equivalence, independently of `bidualEvalEquiv`. -/
private theorem flip_id_bijective_pi
    (R : Type uR) (ι : Type uι) [Semiring R] [Finite ι] :
    Function.Bijective (LinearMap.flip (LinearMap.id :
      ((ι → R) →ₗ[R] R) →ₗ[Rᵐᵒᵖ] ((ι → R) →ₗ[R] R))) := by
  classical
  let _ := Fintype.ofFinite ι
  constructor
  · intro x y h
    funext i
    exact congrArg (fun Φ : ((ι → R) →ₗ[R] R) →ₗ[Rᵐᵒᵖ] R =>
      Φ (LinearMap.proj i)) h
  · intro Φ
    refine ⟨fun i => Φ (LinearMap.proj i), ?_⟩
    apply LinearMap.ext
    intro f
    have hf := pi_form_eq_sum R ι f
    calc
      (LinearMap.flip (LinearMap.id :
          ((ι → R) →ₗ[R] R) →ₗ[Rᵐᵒᵖ] ((ι → R) →ₗ[R] R)))
          (fun i => Φ (LinearMap.proj i)) f =
          ∑ i, Φ (LinearMap.proj i) * f (Pi.single i 1) := by
        simpa only [LinearMap.flip_apply, LinearMap.id_apply, sum_apply,
          LinearMap.smul_apply, LinearMap.proj_apply, op_smul_eq_mul] using
            congrArg (fun g : (ι → R) →ₗ[R] R =>
              g (fun i => Φ (LinearMap.proj i))) hf
      _ = Φ f := by
        simpa only [map_sum, map_smul, op_smul_eq_mul] using
          (congrArg Φ hf).symm

/-- Bijectivity of ordinary-coefficient mixed-scalar evaluation descends along
an arbitrary module retraction. -/
private theorem bijective_flip_id_of_retract
    (R : Type uR) (M : Type uM) (F : Type uF)
    [Semiring R] [AddCommMonoid M] [AddCommMonoid F]
    [Module R M] [Module R F]
    (i : M →ₗ[R] F) (p : F →ₗ[R] M) (hpi : p.comp i = LinearMap.id)
    (hF : Function.Bijective
      (LinearMap.flip (LinearMap.id :
        (F →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (F →ₗ[R] R)))) :
    Function.Bijective
      (LinearMap.flip (LinearMap.id :
        (M →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (M →ₗ[R] R))) := by
  have hp_i (m : M) : p (i m) = m := LinearMap.congr_fun hpi m
  constructor
  · intro m n h
    have hi : i m = i n := hF.1 <| by
      ext f
      exact LinearMap.congr_fun h (f.comp i)
    exact (hp_i m).symm.trans ((congrArg p hi).trans (hp_i n))
  · intro Φ
    obtain ⟨x, hx⟩ :=
      hF.2 ((LinearMap.lcomp R R (LinearMap.lcomp Rᵐᵒᵖ R i)) Φ)
    refine ⟨p x, ?_⟩
    ext f
    have hx_apply := LinearMap.congr_fun hx (f.comp p)
    have hform : (f.comp p).comp i = f := by
      ext m
      exact congrArg f (hp_i m)
    exact hx_apply.trans (congrArg Φ hform)

/-- Evaluation identifies a finite projective left module with its
ordinary-coefficient bidual. The first Hom has the right-regular coefficient
action and the second Hom has the left-regular coefficient action.
For the finite-projective duality context, see Weibel's *The K-book*, Chapter I, §2. -/
noncomputable def bidualEvalEquiv
    (R : Type uR) (M : Type uM)
    [Semiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    M ≃ₗ[R] ((M →ₗ[R] R) →ₗ[Rᵐᵒᵖ] R) :=
  LinearEquiv.ofBijective
    (LinearMap.flip (LinearMap.id :
      (M →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (M →ₗ[R] R))) (by
      obtain ⟨n, p, i, _, _, hpi⟩ :=
        Module.Finite.exists_comp_eq_id_of_projective R M
      exact bijective_flip_id_of_retract R M (Fin n → R) i p hpi
        (flip_id_bijective_pi R (Fin n)))

/-- The forward map is the mixed-scalar evaluation pairing. -/
@[simp]
theorem bidualEvalEquiv_toLinearMap
    (R : Type uR) (M : Type uM)
    [Semiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    (bidualEvalEquiv R M).toLinearMap =
      LinearMap.flip (LinearMap.id :
        (M →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (M →ₗ[R] R)) := rfl

/-- Evaluating the bidual image of an element applies the supplied form. -/
@[simp]
theorem bidualEvalEquiv_apply
    (R : Type uR) (M : Type uM)
    [Semiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (m : M) (f : M →ₗ[R] R) :
    bidualEvalEquiv R M m f = f m := rfl

/-- A form evaluated at the inverse bidual image has the prescribed value. -/
@[simp]
theorem apply_bidualEvalEquiv_symm
    (R : Type uR) (M : Type uM)
    [Semiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (Φ : (M →ₗ[R] R) →ₗ[Rᵐᵒᵖ] R) (f : M →ₗ[R] R) :
    f ((bidualEvalEquiv R M).symm Φ) = Φ f := by
  simpa only [bidualEvalEquiv_apply] using
    congrArg (fun Ψ : (M →ₗ[R] R) →ₗ[Rᵐᵒᵖ] R => Ψ f)
      ((bidualEvalEquiv R M).apply_symm_apply Φ)

/-- Evaluation commutes with two successive precompositions. -/
theorem flip_id_bidual_naturality
    (R : Type uR) (M : Type uM) (N : Type uN)
    [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (g : M →ₗ[R] N) :
    (LinearMap.lcomp R R (LinearMap.lcomp Rᵐᵒᵖ R g)).comp
        (LinearMap.flip (LinearMap.id :
          (M →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (M →ₗ[R] R))) =
      (LinearMap.flip (LinearMap.id :
        (N →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (N →ₗ[R] R))).comp g := by
  ext m f
  rfl

/-- The finite-projective evaluation equivalences commute with linear maps. -/
theorem bidualEvalEquiv_naturality
    (R : Type uR) (M : Type uM) (N : Type uN)
    [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (g : M →ₗ[R] N) :
    (LinearMap.lcomp R R (LinearMap.lcomp Rᵐᵒᵖ R g)).comp
        (bidualEvalEquiv R M).toLinearMap =
      (bidualEvalEquiv R N).toLinearMap.comp g := by
  simpa only [bidualEvalEquiv_toLinearMap] using flip_id_bidual_naturality R M N g

/-- Over a commutative semiring, restriction of the second Hom's inner scalars
turns mixed-scalar evaluation into the same-scalar dual evaluation. -/
theorem flip_id_restrictScalars_eq_dual_eval
    (R : Type uR) (M : Type uM)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    (LinearMap.restrictScalarsₗ
      (R := R) (S := Rᵐᵒᵖ) (M := M →ₗ[R] R) (N := R) (R₁ := R)).comp
        (LinearMap.flip (LinearMap.id :
          (M →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (M →ₗ[R] R))) = Module.Dual.eval R M := by
  apply LinearMap.ext₂
  intro m f
  simp only [LinearMap.comp_apply, LinearMap.restrictScalarsₗ_apply,
    LinearMap.restrictScalars_apply, LinearMap.flip_apply, LinearMap.id_apply,
    Module.Dual.eval_apply]

/-- The coefficient-preserving inner-scalar conversion agrees with the
commutative finite-projective evaluation equivalence. -/
theorem bidualEvalEquiv_restrictScalars
    (R : Type uR) (M : Type uM)
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    (LinearMap.restrictScalarsₗ
      (R := R) (S := Rᵐᵒᵖ) (M := M →ₗ[R] R) (N := R) (R₁ := R)).comp
        (bidualEvalEquiv R M).toLinearMap =
      (Module.evalEquiv R M).toLinearMap := by
  simpa only [bidualEvalEquiv_toLinearMap, Module.evalEquiv_toLinearMap] using
    flip_id_restrictScalars_eq_dual_eval R M

/-- The two inner-scalar restrictions on the ordinary-coefficient second Hom
are inverse conversions over a commutative semiring. -/
theorem bidual_restrictScalars_roundTrips
    (R : Type uR) (M : Type uM)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    (LinearMap.restrictScalarsₗ
      (R := Rᵐᵒᵖ) (S := R) (M := M →ₗ[R] R) (N := R) (R₁ := R)).comp
        (LinearMap.restrictScalarsₗ
          (R := R) (S := Rᵐᵒᵖ) (M := M →ₗ[R] R) (N := R) (R₁ := R)) = LinearMap.id ∧
      (LinearMap.restrictScalarsₗ
        (R := R) (S := Rᵐᵒᵖ) (M := M →ₗ[R] R) (N := R) (R₁ := R)).comp
        (LinearMap.restrictScalarsₗ
          (R := Rᵐᵒᵖ) (S := R) (M := M →ₗ[R] R) (N := R) (R₁ := R)) = LinearMap.id := by
  constructor
  · apply LinearMap.ext₂
    intro Φ f
    rfl
  · apply LinearMap.ext₂
    intro Ψ f
    rfl

end LinearMap
