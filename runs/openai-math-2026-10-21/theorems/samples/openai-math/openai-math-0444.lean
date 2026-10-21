namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Topology

open Set Function MeasureTheory

theorem affineRectangle_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (c : Plane) :
    Injective (affineRectangle c a b) := by
  intro x y he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  exact Prod.ext (mul_left_cancel₀ ha (add_left_cancel h1))
    (mul_left_cancel₀ hb (add_left_cancel h2))

end
end PackingSufficiencySupport.Hamiltonian
end
end OAI
