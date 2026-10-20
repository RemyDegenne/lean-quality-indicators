@[expose] public section

universe u v

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R}

theorem nonempty_iso_iff_finrank_eq [StrongRankCondition R]
    [Module.Finite R X] [Module.Finite R Y] [Module.Free R X] [Module.Free R Y] :
    Nonempty (X ≅ Y) ↔ Module.finrank R X = Module.finrank R Y := by
  constructor
  · rintro ⟨e⟩
    exact e.toLinearEquiv.finrank_eq
  · intro h
    obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq h
    exact ⟨e.toModuleIso⟩

end ModuleCat
end
