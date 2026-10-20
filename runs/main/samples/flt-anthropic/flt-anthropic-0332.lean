namespace P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat

set_option autoImplicit false

noncomputable section

namespace M4aP1R

namespace LevelCoveringArch

open Matrix NumberField NumberField.InfinitePlace NumberField.AdelicLevel AutomorphicForm IsDedekindDomain

theorem globalPoints_eps_mem_levelOne (N : Ideal (𝓞 ℚ)) :
    globalPoints (𝓞 ℚ) ℚ eps ∈ levelOne (𝓞 ℚ) ℚ N := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
  refine ⟨isLevelOneMatrix_eps N, ?_⟩
  rw [← map_inv, ← map_inv, eps_inv]
  exact isLevelOneMatrix_eps N

end LevelCoveringArch
end M4aP1R
end
end P2MW.S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
