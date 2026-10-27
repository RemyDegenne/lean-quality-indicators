public section

namespace CFSG.GH74.Generic.BProg.B3.FalseCtxS45

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification Subgroup

open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS4

open scoped commutatorElement

section JBar

variable {G : Type} [Group G] [Finite G] {x a : G} {J H : Subgroup G}

theorem orderOf_yAut (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hxY : x ∈ centralizer ({a} : Set G)) (hxJ : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1)
    (hnc : x ∉ centralizerSection J (pPrimeCoreOf 2 J)) : orderOf (yAut hJ.1 hxY hxJ) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact yAut_mul_self hJ.1 hxY hxJ hx2) (yAut_ne_one hJ hxY hxJ hnc)

end JBar
end CFSG.GH74.Generic.BProg.B3.FalseCtxS45
end
