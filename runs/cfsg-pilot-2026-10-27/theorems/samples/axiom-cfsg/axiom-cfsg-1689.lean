public section

namespace CFSG.Quasithin.F7Two

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.TwoF4
  CFSG.LieType.Ree.LargeReeCover

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {m : ℕ}

local notation "X[" k "]" => largeReeBlockGroup K m (octBlock k)

local notation "Γ" => F4.reeGamma K m

local notation "wT" => weylTwo K * weylOne K * weylTwo K

theorem sylowVec_mem_tKernel (hK : Nat.card K = 2 ^ (2 * m + 1)) {x : Fin 12 → K} (h0 : x 0 = 0)
    (h1 : x 1 = 0) (h3 : x 3 = 0) : sylowVec m K x ∈ tKernel K m := by
  rw [← SetLike.mem_coe, coe_tKernel hK]
  exact ⟨x, ⟨h0, h1, h3⟩, rfl⟩

end CFSG.Quasithin.F7Two
end
