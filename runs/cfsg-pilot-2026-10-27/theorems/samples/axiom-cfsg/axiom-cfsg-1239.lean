public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.RankTwo

open scoped MatrixGroups commutatorElement

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

local notation "F2" => rootOperatorFamily Tag.G2

theorem mem_RA2_iff {γ : Fin 2 → ℤ} : γ ∈ RA2 ↔ (γ 0, γ 1) ∈ A2l := by
  rw [mem_rootsA2]
  have key : ∀ a b : ℤ, γ = ![a, b] ↔ (γ 0, γ 1) = (a, b) := fun a b => by
    constructor
    · rintro rfl
      simp
    · intro h
      obtain ⟨h0, h1⟩ := Prod.mk.inj h
      funext i
      fin_cases i <;> simp [h0, h1]
  simp only [A2l, List.mem_cons, List.not_mem_nil, or_false, key]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
end
