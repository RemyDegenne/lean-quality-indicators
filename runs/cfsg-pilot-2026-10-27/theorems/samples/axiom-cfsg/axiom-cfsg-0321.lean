public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit root_diagonal_conjugation)

open CFSG.LieType.Steinberg.Adjoint

section Corner

variable {K : Type} [Field K] [Finite K]

theorem twE6Corner_decomp (σ : K ≃+* K) (ι : MulAut (twistedE6RootGroup K σ))
    (hι : ι ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    ∃ (g : twistedE6RootGroup K σ) (a : Fin TwistTag.E6.tag.rank → Kˣ),
      ∀ x : twistedE6RootGroup K σ,
        (ι x : ModGL TwistTag.E6.tag K) =
          ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a) *
            (x : ModGL TwistTag.E6.tag K) *
            ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a)⁻¹ := by
  obtain ⟨_, ⟨g, rfl⟩, _, ⟨u, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hι
  refine ⟨g, compatDiag TwistTag.E6 σ.toRingHom u, fun x => ?_⟩
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_compatDiagAutHom, Subgroup.coe_inv]
  simp only [mul_assoc, mul_inv_rev]

end Corner
end CFSG.LieType.SeitzGeneration.ExcWideThree
end
