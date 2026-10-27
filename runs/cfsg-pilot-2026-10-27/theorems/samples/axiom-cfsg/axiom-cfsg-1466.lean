public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt

open scoped Pointwise

section SEData

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {q e : ℕ}

theorem holtStructure_of_isBenderNormal_top (h : IsBenderNormal Ω (⊤ : Subgroup G) q e) :
    HoltStructure G Ω :=
  let ⟨_, ht⟩ := longInv_nonempty_of_isBenderNormal_top h
  ⟨.ofIsBenderNormalTop h ht⟩

end SEData
end CFSG.Holt.H78
end
