/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.RenameComplement
public import MultivariatePolynomials.Regularity
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

/-!
# Flatness and prime spectra of variable renaming

The original homomorphism on the full polynomial rings induced by a variable
map is flat exactly when the variable map is injective or the coefficient ring
is subsingleton. Coefficient and variable universes are independent.

An injective variable map identifies the source with polynomials on its range;
`splitComplAlgEquiv` then identifies the target with a free polynomial algebra
over that source. A collision kills a regular difference of variables, which
flatness can do only when the target, and hence its coefficient ring, is zero.

The prime-spectrum surjectivity criterion over commutative semirings and the
faithful-flatness criterion over commutative rings use the same
injectivity-or-subsingleton condition, for the original map on full polynomial
semirings or rings. An injective renaming has a retraction, while evaluation
at zero and one separates colliding source variables over nontrivial
coefficients. Faithful flatness follows from flatness and surjectivity on
prime spectra.

## References

* Mathlib's `Module.Free` instance for multivariate polynomials,
  `RingHom.Flat.comp`, and `IsSMulRegular.of_flat`.
* Mathlib's `MvPolynomial.killCompl_comp_rename` and
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`.
-/

universe u v w

namespace MvPolynomial

/-- Renaming along an injective variable map is flat on the full polynomial rings. -/
theorem rename_flat_of_injective {R : Type u} {σ : Type v} {τ : Type w}
    [CommRing R] (f : σ → τ) (hf : Function.Injective f) :
    RingHom.Flat (rename (R := R) f).toRingHom := by
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
  have hC : RingHom.Flat
      (C : MvPolynomial (Set.range f) R →+*
        MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)) := by
    change RingHom.Flat (algebraMap (MvPolynomial (Set.range f) R)
      (MvPolynomial ((Set.range f)ᶜ : Set τ) (MvPolynomial (Set.range f) R)))
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have h₁ : RingHom.Flat e₁.toRingEquiv.toRingHom :=
    RingHom.Flat.of_bijective e₁.bijective
  rw [← hcomp]
  exact (h₁.comp hC).comp (RingHom.Flat.of_bijective e₂.symm.bijective)

/-- If a noninjective renaming is flat, its coefficient ring is subsingleton. -/
theorem subsingleton_of_rename_flat_of_not_injective
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R]
    (f : σ → τ) (hf : ¬ Function.Injective f)
    (hflat : RingHom.Flat (rename (R := R) f).toRingHom) : Subsingleton R := by
  classical
  have hcollision : ∃ i j, f i = f j ∧ i ≠ j := by
    by_contra h
    apply hf
    intro i j heq
    by_contra hij
    exact h ⟨i, j, heq, hij⟩
  obtain ⟨i, j, heq, hij⟩ := hcollision
  let g : MvPolynomial σ R →+* MvPolynomial τ R := (rename (R := R) f).toRingHom
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) := g.toAlgebra
  let : Module.Flat (MvPolynomial σ R) (MvPolynomial τ R) := hflat
  have hsource : IsSMulRegular (MvPolynomial σ R) (X i - X j : MvPolynomial σ R) :=
    (isRegular_X_sub_X (R := R) hij).1
  have htarget : IsSMulRegular (MvPolynomial τ R)
      (algebraMap (MvPolynomial σ R) (MvPolynomial τ R)
        (X i - X j : MvPolynomial σ R)) := hsource.of_flat
  have hz : algebraMap (MvPolynomial σ R) (MvPolynomial τ R)
      (X i - X j : MvPolynomial σ R) = 0 := by
    change g (X i - X j) = 0
    simp [g, heq]
  rw [hz] at htarget
  have h10 : (1 : MvPolynomial τ R) = 0 :=
    htarget (show (0 : MvPolynomial τ R) • (1 : MvPolynomial τ R) =
      (0 : MvPolynomial τ R) • 0 by simp)
  have hcoeff : (1 : R) = 0 := by
    simpa using congrArg (fun p : MvPolynomial τ R => constantCoeff p) h10
  exact subsingleton_of_zero_eq_one hcoeff.symm

/-- Variable renaming on the full polynomial rings is flat exactly when the
variable map is injective or the coefficient ring is subsingleton. -/
theorem rename_flat_iff {R : Type u} {σ : Type v} {τ : Type w}
    [CommRing R] (f : σ → τ) :
    RingHom.Flat (MvPolynomial.rename (R := R) f).toRingHom ↔
      Function.Injective f ∨ Subsingleton R := by
  classical
  constructor
  · intro hflat
    by_cases hf : Function.Injective f
    · exact Or.inl hf
    · exact Or.inr (subsingleton_of_rename_flat_of_not_injective f hf hflat)
  · rintro (hf | hR)
    · exact rename_flat_of_injective f hf
    · let : Subsingleton R := hR
      unfold RingHom.Flat
      infer_instance

/-- The map on prime spectra induced by variable renaming on the full polynomial
semirings is surjective exactly when the variable map is injective or the
coefficient semiring is subsingleton. -/
theorem comap_rename_surjective_iff {R : Type u} {σ : Type v} {τ : Type w}
    [CommSemiring R] (f : σ → τ) :
    Function.Surjective (PrimeSpectrum.comap (MvPolynomial.rename (R := R) f).toRingHom) ↔
      Function.Injective f ∨ Subsingleton R := by
  classical
  constructor
  · intro hsurj
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inr hR
    · left
      intro i j hij
      by_contra hne
      obtain ⟨p⟩ := (PrimeSpectrum.nonempty_iff_nontrivial (R := R)).mpr hR
      -- Pulling back `p` along this evaluation separates the colliding variables.
      let e : MvPolynomial σ R →+* R := eval (fun k => if k = j then 1 else 0)
      obtain ⟨q, hq⟩ := hsurj (PrimeSpectrum.comap e p)
      have hi : (X i : MvPolynomial σ R) ∈ (PrimeSpectrum.comap e p).asIdeal := by
        change e (X i) ∈ p.asIdeal
        simpa only [e, eval_X, if_neg hne] using p.asIdeal.zero_mem
      have hj : (X j : MvPolynomial σ R) ∈ (PrimeSpectrum.comap e p).asIdeal := by
        rw [← hq] at hi ⊢
        change rename f (X i) ∈ q.asIdeal at hi
        change rename f (X j) ∈ q.asIdeal
        simpa only [rename_X, hij] using hi
      have hone : (1 : R) ∈ p.asIdeal := by
        change e (X j) ∈ p.asIdeal at hj
        simpa only [e, eval_X, if_pos rfl, ite_true] using hj
      exact p.isPrime.one_notMem hone
  · rintro (hf | hR)
    · intro p
      refine ⟨PrimeSpectrum.comap (killCompl (R := R) hf).toRingHom p, ?_⟩
      have hcomp : (killCompl (R := R) hf).toRingHom.comp (rename (R := R) f).toRingHom =
          RingHom.id (MvPolynomial σ R) := by
        apply RingHom.ext
        intro a
        exact killCompl_rename_app hf a
      rw [← PrimeSpectrum.comap_comp_apply, hcomp, PrimeSpectrum.comap_id]
    · letI : Subsingleton R := hR
      intro p
      exact isEmptyElim p

/-- Variable renaming on the full polynomial rings is faithfully flat exactly
when the variable map is injective or the coefficient ring is subsingleton.
The scalar action is induced by the displayed renaming homomorphism. -/
theorem rename_faithfullyFlat_iff {R : Type u} {σ : Type v} {τ : Type w}
    [CommRing R] (f : σ → τ) :
    RingHom.FaithfullyFlat (MvPolynomial.rename (R := R) f).toRingHom ↔
      Function.Injective f ∨ Subsingleton R := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective,
    rename_flat_iff, comap_rename_surjective_iff, and_self]

end MvPolynomial
