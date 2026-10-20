@[expose] public section

noncomputable section

open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite

open scoped AlgebraicGeometry

universe u v w

variable {X : TopCat.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]

section

variable {C : Type v} [Category.{u} C] (A : C) [HasTerminal C]

theorem skyscraperPresheaf_isSheaf : (skyscraperPresheaf p₀ A).IsSheaf := by
  classical
  exact
    (Presheaf.isSheaf_iso_iff (eqToIso <| skyscraperPresheaf_eq_pushforward p₀ A)).mpr
      (Sheaf.pushforward_sheaf_of_sheaf _
        (Presheaf.isSheaf_on_punit_of_isTerminal _ (by
          dsimp [skyscraperPresheaf]
          rw [ite_eq_right]
          · exact terminalIsTerminal
          · #adaptation_note 
            exact Set.notMem_empty PUnit.unit.{u + 1})))

end
end
end
