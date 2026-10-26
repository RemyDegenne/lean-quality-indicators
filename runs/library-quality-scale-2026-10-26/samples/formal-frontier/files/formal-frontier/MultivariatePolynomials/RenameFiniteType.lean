/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.MvPolynomial.Supported

@[expose] public section

/-!
# Finite type of variable renaming

A map of variable types induces an algebra structure on the target polynomial
semiring over the source polynomial semiring. A source polynomial acts by
multiplication by its renamed image. This algebra is of finite type exactly when
the coefficient semiring is subsingleton or only finitely many target variables
lie outside the image of the variable map.

The variable types and coefficient type may have independent universes, and the
variable map need not be injective or surjective. The finite set concerns missed
target variables, not source variables that are identified by renaming.

Finite type means finite generation as an algebra over the source polynomial
semiring. It does not mean finite presentation or finiteness as a module over
the coefficient semiring.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Rename`: polynomial variable renaming.
* Mathlib, `Mathlib.RingTheory.FiniteType`: finite generation of semiring algebras.
* Mathlib, `Mathlib.RingTheory.Adjoin.Basic` and `Mathlib.RingTheory.Adjoin.FG`:
  algebra generation and change of base in a scalar tower.
* Mathlib, `Mathlib.Algebra.MvPolynomial.Supported`: supported subalgebras and
  detection of variables over nontrivial coefficients.
-/

universe u v w

namespace MvPolynomial

/-- Renaming variables gives a finite-type algebra over the source polynomial semiring
exactly when the coefficient semiring is subsingleton or finitely many target variables
are missed. The algebra structure is induced by the renaming homomorphism. -/
theorem finiteType_rename_iff {R : Type u} {σ : Type v} {τ : Type w}
    [CommSemiring R] (f : σ → τ) :
    @Algebra.FiniteType (MvPolynomial σ R) (MvPolynomial τ R) _ _
      (MvPolynomial.rename (R := R) f).toRingHom.toAlgebra ↔
      Subsingleton R ∨ Set.Finite ((Set.range f)ᶜ) := by
  classical
  let : Algebra (MvPolynomial σ R) (MvPolynomial τ R) :=
    (rename (R := R) f).toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial σ R) (MvPolynomial τ R) :=
    IsScalarTower.of_algHom (rename (R := R) f)
  -- Restriction of scalars retains all the renamed source variables.
  have hadjoin (s : Set (MvPolynomial τ R)) :
      (Algebra.adjoin (MvPolynomial σ R) s).restrictScalars R =
        Algebra.adjoin R
          (algebraMap (MvPolynomial σ R) (MvPolynomial τ R) ''
            Set.range (X : σ → MvPolynomial σ R) ∪ s) :=
    Algebra.adjoin_eq_adjoin_union R _ s adjoin_range_X
  constructor
  · intro h
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inl hR
    let : Nontrivial R := hR
    obtain ⟨s, hs⟩ := h.out
    let t : Finset τ := s.biUnion vars
    have hbound :
        Algebra.adjoin R
          (algebraMap (MvPolynomial σ R) (MvPolynomial τ R) ''
            Set.range (X : σ → MvPolynomial σ R) ∪ (s : Set (MvPolynomial τ R))) ≤
          supported R (Set.range f ∪ (t : Set τ)) := by
      apply Algebra.adjoin_le
      rintro p (hp | hp)
      · rcases hp with ⟨q, ⟨i, rfl⟩, rfl⟩
        change rename f (X i) ∈ supported R _
        rw [rename_X, X_mem_supported]
        exact Or.inl ⟨i, rfl⟩
      · apply mem_supported.mpr
        intro j hj
        exact Or.inr (Finset.subset_biUnion_of_mem vars hp hj)
    rw [← hadjoin, hs, Subalgebra.restrictScalars_top] at hbound
    refine Or.inr (t.finite_toSet.subset ?_)
    intro j hj
    have hj' : j ∈ Set.range f ∪ (t : Set τ) :=
      X_mem_supported.mp (hbound (show X j ∈ (⊤ : Subalgebra R (MvPolynomial τ R))
        from trivial))
    exact hj'.resolve_left hj
  · rintro (hR | hf)
    · let : Subsingleton R := hR
      let : Subsingleton (MvPolynomial τ R) :=
        Algebra.subsingleton R (MvPolynomial τ R)
      refine ⟨⟨∅, ?_⟩⟩
      apply top_unique
      intro p _
      rw [Subsingleton.elim p 0]
      exact Subalgebra.zero_mem _
    · refine ⟨Subalgebra.fg_def.mpr
        ⟨X '' (Set.range f)ᶜ, hf.image X, ?_⟩⟩
      apply Subalgebra.restrictScalars_injective R
      rw [hadjoin, Subalgebra.restrictScalars_top]
      have hcover :
          algebraMap (MvPolynomial σ R) (MvPolynomial τ R) ''
              Set.range (X : σ → MvPolynomial σ R) ∪ X '' (Set.range f)ᶜ =
            Set.range (X : τ → MvPolynomial τ R) := by
        ext p
        constructor
        · rintro (hp | hp)
          · rcases hp with ⟨q, ⟨i, rfl⟩, rfl⟩
            exact ⟨f i, (rename_X f i).symm⟩
          · rcases hp with ⟨j, _, rfl⟩
            exact ⟨j, rfl⟩
        · rintro ⟨j, rfl⟩
          by_cases hj : j ∈ Set.range f
          · obtain ⟨i, rfl⟩ := hj
            exact Or.inl ⟨X i, ⟨i, rfl⟩, rename_X f i⟩
          · exact Or.inr ⟨j, hj, rfl⟩
      rw [hcover, adjoin_range_X]

end MvPolynomial
