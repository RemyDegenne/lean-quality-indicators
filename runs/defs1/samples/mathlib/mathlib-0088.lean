@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomologicalComplex

open ShortComplex

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
  (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)

variable {c : ComplexShape ℕ} [DecidableRel c.Rel] (hc : ∀ i j, c.Rel i j → Odd (i + j))

open HomologicalComplex hiding mk

/-- The `i, j, k`th short complex associated to the alternating constant complex on `φ, ψ : A ⟶ A`
is `A --ψ--> A --φ--> A` when `i ~ j, j ~ k` and `j` is even. -/
noncomputable def alternatingConstScIsoEven
    {i j k : ℕ} (hij : c.Rel i j) (hjk : c.Rel j k) (h : Even j) :
    (alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk ψ φ hEven :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, right_eq_ite_iff]
      intro hi
      have := hc i j hij
      exact False.elim <| Nat.not_odd_iff_even.2 hi <| by simp_all [Nat.odd_add])
    (by simp_all [alternatingConst])

end HomologicalComplex
end
