public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20

section B

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ U : Subgroup G} {g : G}

theorem A_inf_Bsub {k : Kind} {M : Subgroup G} (h11 : Lemma20_11) (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hT : TypeCl z k S) (h : FusedSetup z S ε q L₁ L₂ K₁ K₂ U g) :
    ∀ x ∈ OddCore z, x ∈ Bsub z g → x = 1 := by
  intro x hxA hxB
  have hxF : x ∈ F20 z := oddCore_centralizer_le_F z hxA (fun f hf => F_comm_Bsub h11 hF hMC hT h f hf x hxB)
  exact F_inf_Bsub h11 hF hMC hT h x hxF hxB

end B
end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
end
