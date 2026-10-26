/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.Rename
public import Mathlib.RingTheory.RingHom.Smooth
import MultivariatePolynomials.RenameComplement
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.TrivSqZeroExt.Ideal

@[expose] public section

/-!
# Formal smoothness of variable renaming

Formal smoothness of a variable-renaming homomorphism is relative to the full
source polynomial ring. The predicate `RingHom.FormallySmooth` uses the algebra
structure induced by the homomorphism: a source variable `X i` acts through the
target variable `X (f i)`. This differs from formal smoothness over the coefficient
ring, which holds for every polynomial algebra and cannot detect collisions.

Renaming is formally smooth exactly when its underlying map is injective, or
equivalently when the variable map is injective or the coefficient ring is
subsingleton. The subsingleton alternative includes the zero ring, where even a
noninjective variable map induces a bijection on polynomial rings. The coefficient
and both variable types have independent universes; empty and infinite variable
families are allowed.

An injective variable map identifies the source with polynomials on its range.
Splitting off the complementary variables then expresses renaming as a polynomial
extension, up to ring equivalences. Conversely, a collision is detected by the
square-zero extension of the target by itself: lift one source variable with
second component `1` and all other variables with second component `0`. Formal
smoothness would give a full-source algebra lift of the identity on the target,
forcing the two different lifts of colliding variables to agree.

## References

* Mathlib, `Mathlib.RingTheory.RingHom.Smooth`: formal smoothness with the algebra
  structure induced by a ring homomorphism.
* Mathlib, `Mathlib.RingTheory.Smooth.Basic`: formal smoothness of polynomial
  algebras and infinitesimal lifting.
* Mathlib, `Mathlib.Algebra.TrivSqZeroExt.Ideal`: the square-zero kernel of the
  projection from a trivial square-zero extension.
* `MultivariatePolynomials.Rename`: the injectivity criterion for variable renaming.
* `MultivariatePolynomials.RenameComplement`: splitting complementary variables
  and the retained-variable action equation.
-/

universe u v w

namespace MvPolynomial

private theorem rename_formallySmooth_of_injective
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]
    (f : σ → τ) (hf : Function.Injective f) :
    (rename (R := R) f).toRingHom.FormallySmooth := by
  classical
  let e₁ := renameEquiv R (Equiv.ofInjective f hf)
  let e₂ := splitComplAlgEquiv (R := R) (Set.range f)
  have hrename :
      (rename (R := R) (Subtype.val : Set.range f → τ)).comp e₁.toAlgHom =
        rename (R := R) f := by
    apply algHom_ext
    intro i
    simp [e₁, renameEquiv_apply]
  have hcomp : e₂.symm.toRingEquiv.toRingHom.comp
      ((C : MvPolynomial (Set.range f) R →+*
        MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)).comp
        e₁.toRingEquiv.toRingHom) = (rename (R := R) f).toRingHom := by
    apply RingHom.ext
    intro p
    apply e₂.injective
    change e₂ (e₂.symm (C (e₁ p))) = e₂ (rename f p)
    have hr : rename f p = rename (Subtype.val : Set.range f → τ) (e₁ p) :=
      (DFunLike.congr_fun hrename p).symm
    rw [AlgEquiv.apply_symm_apply, hr]
    exact (splitComplAlgEquiv_rename_subtypeVal (R := R) (Set.range f) (e₁ p)).symm
  have hC : (C : MvPolynomial (Set.range f) R →+*
      MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)).FormallySmooth := by
    change (algebraMap (MvPolynomial (Set.range f) R)
      (MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R))).FormallySmooth
    exact RingHom.formallySmooth_algebraMap.mpr inferInstance
  have h₁ : e₁.toRingEquiv.toRingHom.FormallySmooth :=
    RingHom.FormallySmooth.of_bijective e₁.bijective
  rw [← hcomp]
  exact (h₁.comp hC).comp (RingHom.FormallySmooth.of_bijective e₂.symm.bijective)

private theorem injective_of_rename_formallySmooth
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R] [Nontrivial R]
    (f : σ → τ) (h : (rename (R := R) f).toRingHom.FormallySmooth) :
    Function.Injective f := by
  classical
  intro i j heq
  by_contra hij
  let S := MvPolynomial τ R
  let E := TrivSqZeroExt S S
  let g : MvPolynomial σ R →+* S := (rename (R := R) f).toRingHom
  -- Give the square-zero extension a source action that distinguishes i from j.
  let φ : MvPolynomial σ R →+* E :=
    eval₂Hom ((TrivSqZeroExt.inlHom S S).comp (C : R →+* S))
      (fun k => (⟨X (f k), if k = i then 1 else 0⟩ : E))
  have hφC (r : R) : φ (C r) = TrivSqZeroExt.inl (C r) :=
    eval₂Hom_C ((TrivSqZeroExt.inlHom S S).comp (C : R →+* S))
      (fun k => (⟨X (f k), if k = i then 1 else 0⟩ : E)) r
  have hφX (k : σ) : φ (X k) = (⟨X (f k), if k = i then 1 else 0⟩ : E) :=
    eval₂Hom_X' ((TrivSqZeroExt.inlHom S S).comp (C : R →+* S))
      (fun k => (⟨X (f k), if k = i then 1 else 0⟩ : E)) k
  let π : E →+* S := (TrivSqZeroExt.fstHom S S S).toRingHom
  have hπ : π.comp φ = g := by
    apply ringHom_ext
    · intro r
      simp [π, g, hφC, TrivSqZeroExt.fstHom_apply]
      rfl
    · intro k
      simp [π, g, hφX, TrivSqZeroExt.fstHom_apply]
      rfl
  letI : Algebra (MvPolynomial σ R) S := g.toAlgebra
  letI : Algebra (MvPolynomial σ R) E := φ.toAlgebra
  letI : Algebra.FormallySmooth (MvPolynomial σ R) S := h
  let q : E →ₐ[MvPolynomial σ R] S :=
    { toRingHom := π
      commutes' p := RingHom.congr_fun hπ p }
  have hsurj : Function.Surjective q := by
    intro p
    exact ⟨TrivSqZeroExt.inl p, rfl⟩
  have hsq : RingHom.ker q.toRingHom ^ 2 = ⊥ := by
    change TrivSqZeroExt.kerIdeal S S ^ 2 = ⊥
    exact TrivSqZeroExt.kerIdeal_sq S S
  let l : S →ₐ[MvPolynomial σ R] E :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id (MvPolynomial σ R) S)
      q hsurj ⟨2, hsq⟩
  -- Source-linearity, not just coefficient-linearity, prescribes both images.
  have hl (k : σ) : l (X (f k)) = (⟨X (f k), if k = i then 1 else 0⟩ : E) := by
    have hk := l.commutes (X k)
    change l (g (X k)) = φ (X k) at hk
    simpa only [g, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_X,
      hφX] using hk
  have hε : (1 : S) = 0 := by
    have he := (hl i).symm.trans
      ((congrArg (fun t : τ => l (X t)) heq).trans (hl j))
    simpa [Ne.symm hij] using congrArg (TrivSqZeroExt.snd : E → S) he
  exact one_ne_zero hε

/-- Variable renaming is formally smooth over the full source polynomial ring
exactly when the variable map is injective or the coefficients are subsingleton.
The second alternative is necessary over the zero ring. -/
theorem rename_formallySmooth_iff
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R] (f : σ → τ) :
    (rename (R := R) f).toRingHom.FormallySmooth ↔
      Function.Injective f ∨ Subsingleton R := by
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · letI : Nontrivial R := hR
      exact Or.inl (injective_of_rename_formallySmooth f h)
  · rintro (hf | hR)
    · exact rename_formallySmooth_of_injective f hf
    · letI : Subsingleton R := hR
      letI : Subsingleton (MvPolynomial σ R) := Algebra.subsingleton R _
      letI : Subsingleton (MvPolynomial τ R) := Algebra.subsingleton R _
      exact RingHom.FormallySmooth.of_bijective
        ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- Variable renaming is formally smooth over the full source polynomial ring
exactly when its underlying map on polynomial rings is injective. -/
theorem rename_formallySmooth_iff_injective
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R] (f : σ → τ) :
    (rename (R := R) f).toRingHom.FormallySmooth ↔
      Function.Injective (rename (R := R) f) := by
  rw [rename_formallySmooth_iff, injective_rename_iff]

end MvPolynomial
