public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

theorem isElemAbelian_omegaOneCenterOf {G : Type*} [Group G] (X : Subgroup G) :
    IsElemAbelian 2 (omegaOneCenterOf X) := by
  have hle : omegaOneCenterOf X ≤ centerOf X := (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hcomm : ∀ a ∈ omegaOneCenterOf X, ∀ b ∈ omegaOneCenterOf X, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hle hb).2 a (hle ha).1
  refine ⟨isMulCommutative_subgroup_iff.mpr hcomm, fun x hx => ?_⟩
  change x ∈ Subgroup.closure _ at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact one_pow 2
  | mul a b ha hb iha ihb => rw [Commute.mul_pow (hcomm a ha b hb) 2, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

end CFSG.AGLEmbedding
end
