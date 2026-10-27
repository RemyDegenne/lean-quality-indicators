public section

namespace CFSG.Sporadic.Bridge.Fi24

open CFSG.Sporadic.Fi24 TauCeti

theorem closure_le_range {x : ℕ → GL (Fin 781) (ZMod 3)}
    (hrel : ∀ v ∈ Sporadic.fi24PrimePresentation.relatorLetters, wordProd x v = 1) :
    Subgroup.closure (x '' Set.Iio 11) ≤ (presHom _ x hrel).range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨presGen _ k, presHom_presGen _ _ _ (by rw [generatorCount_eq]; exact hk)⟩

end CFSG.Sporadic.Bridge.Fi24
end
