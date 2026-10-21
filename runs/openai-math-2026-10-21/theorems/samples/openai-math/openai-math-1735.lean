namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {p : A} (hp : IsStarProjection p)

lemma projection_factor_trace (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e) :
    t.functional (e:A)=((‖TracialGNS.algebraVector (factorTrace t f hf) e0‖^2:ℝ):ℂ) := by
  have hn := (factorTrace t f hf).preGNS_norm_sq ((factorTrace t f hf).toPreGNS e0)
  have he := corner_projection_coe hp (e:=e) heproj
  symm
  simpa only [TracialGNS.algebraVector_apply,Completion.norm_coe,
    Complex.ofReal_pow,PositiveLinearMap.ofPreGNS_toPreGNS,pullbackState_apply,
    map_mul,map_star,heq,he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq] using hn

end Kadison.FreeBlocks
end
end
end
end OAI
