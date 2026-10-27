public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem pairVec_mem_splitSub {n : ℕ} {D D₂ : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {a b : Fin n → ZMod 2} : pairVec a b ∈ splitSub n D D₂ ↔ a ∈ D ∧ b ∈ D₂ := by
  constructor
  · rintro ⟨a', ha', b', hb', h⟩
    obtain ⟨rfl, rfl⟩ := pairVec_inj.mp h
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl⟩

end CFSG.ASVolI.ChH
end
