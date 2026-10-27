public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix

open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear
  blockSpecialLinear_mono)

open CFSG.Quasithin (perfectCore)

open scoped MatrixGroups commutatorElement

section Generic

variable {F : Type} [Field F] {n : ℕ}

theorem offDiag_of_mem_map_diagTorusSL {ω : (Fin 3 → Fˣ) →* (Fin n → Fˣ)}
    {hω : ∀ t, ∏ i, ω t i = 1} {P : Type*} [Group P] {H : Subgroup P}
    {π : P →* (Fin 3 → Fˣ)} {d : SpecialLinearGroup (Fin n) F}
    (hd : d ∈ H.map ((diagTorusSL ω hω).comp π)) :
    ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0 := by
  obtain ⟨p, -, rfl⟩ := hd
  exact fun i j hij => diagTorusSL_apply_ne ω hω (π p) hij

end Generic
end CFSG.SeitzReduction.F4Pilot
end
