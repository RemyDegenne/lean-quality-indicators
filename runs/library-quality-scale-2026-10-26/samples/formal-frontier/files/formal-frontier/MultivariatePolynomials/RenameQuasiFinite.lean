/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.RingHom.QuasiFinite

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.QuasiFinite.Polynomial
import MultivariatePolynomials.RenameModuleFinite

@[expose] public section

/-!
# Quasi-finiteness of variable renaming

The quasi-finiteness criterion concerns the original homomorphism between the
full polynomial rings. Its induced action is `p • q = MvPolynomial.rename f p * q`,
with scalars in the source polynomial ring, not merely in the coefficient ring.
The coefficient and two variable types have independent universes.

Here quasi-finiteness is Mathlib's finiteness of every residue-field fiber as a
module over that residue field. Mathlib's predicate does not include a
`FiniteType` hypothesis; no finite-type convention is added here.

Module finiteness gives the positive direction. Over nontrivial coefficients,
an omitted target variable gives a split surjective evaluation onto `R[X]`
that kills every renamed variable. Composition and restriction of scalars
would then make the coefficient map `R →+* R[X]` quasi-finite, contradicting
Mathlib's polynomial obstruction at a maximal ideal.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename` and
  `Mathlib.Algebra.Polynomial.AlgebraMap`: variable renaming and evaluation.
* Andrew Yang's Mathlib quasi-finite algebra, polynomial and ring-homomorphism
  APIs in `Mathlib.RingTheory.QuasiFinite.Basic`,
  `Mathlib.RingTheory.QuasiFinite.Polynomial` and
  `Mathlib.RingTheory.RingHom.QuasiFinite`.
* Johan Commelin's Mathlib finiteness API in
  `Mathlib.RingTheory.Finiteness.Basic`.
* Formal Frontier Agents, the compositional polynomial obstruction.
  The evaluation section and factorization follow the proof patterns in this
  library's `RenameModuleFinite` and `RenameIntegral` modules.
-/

universe u v w

/-- The original renaming homomorphism between full polynomial rings over a
commutative ring is quasi-finite exactly when the variable map is surjective or
the coefficient ring is subsingleton. Quasi-finiteness uses the full
source-polynomial action induced by this homomorphism and Mathlib's
residue-field-fiber convention, which does not require `FiniteType`. -/
theorem MvPolynomial.rename_quasiFinite_iff
    {σ : Type u} {τ : Type v} {R : Type w} [CommRing R] (f : σ → τ) :
    RingHom.QuasiFinite (MvPolynomial.rename (R := R) f).toRingHom ↔
      Function.Surjective f ∨ Subsingleton R := by
  classical
  constructor
  · intro hφ
    by_cases hR : Subsingleton R
    · exact Or.inr hR
    · left
      let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
      by_contra hf
      simp only [Function.Surjective, not_forall, not_exists] at hf
      obtain ⟨j, hj⟩ := hf
      let φ : MvPolynomial σ R →+* MvPolynomial τ R :=
        (MvPolynomial.rename (R := R) f).toRingHom
      let ψa : MvPolynomial τ R →ₐ[R] Polynomial R :=
        MvPolynomial.aeval (fun k => if k = j then Polynomial.X else 0)
      let ψ := ψa.toRingHom
      let ε : MvPolynomial σ R →+* R := MvPolynomial.constantCoeff
      have hψ : Function.Surjective ψ := by
        intro p
        refine ⟨Polynomial.aeval (MvPolynomial.X j : MvPolynomial τ R) p, ?_⟩
        have hsec : ψa.comp (Polynomial.aeval (MvPolynomial.X j)) =
            AlgHom.id R (Polynomial R) := by
          apply Polynomial.algHom_ext
          simp [ψa]
        exact DFunLike.congr_fun hsec p
      -- All source variables vanish, so the composite factors through augmentation.
      have hcomp : ψ.comp φ = Polynomial.C.comp ε := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [ψ, ψa, φ, ε]
        · intro i
          simp [ψ, ψa, φ, ε, hj i]
      have hψq : ψ.QuasiFinite :=
        RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective ψ hψ)
      have hψφ : (ψ.comp φ).QuasiFinite := hψq.comp hφ
      rw [hcomp] at hψφ
      -- Restriction of scalars retains the outer map, with no assumption on ε.
      have hC : (Polynomial.C : R →+* Polynomial R).QuasiFinite :=
        RingHom.QuasiFinite.of_comp hψφ
      have hA : Algebra.QuasiFinite R (Polynomial R) :=
        RingHom.quasiFinite_algebraMap.mp
          (by simpa only [Polynomial.algebraMap_eq] using hC)
      let : Algebra.QuasiFinite R (Polynomial R) := hA
      obtain ⟨P, hP⟩ := Ideal.exists_maximal (Polynomial R)
      let : P.IsMaximal := hP
      exact Polynomial.not_quasiFiniteAt P
        (inferInstance : Algebra.QuasiFiniteAt R P)
  · intro h
    exact RingHom.QuasiFinite.of_finite
      ((MvPolynomial.moduleFinite_rename_iff (R := R) f).mpr h)
