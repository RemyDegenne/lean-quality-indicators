public section

namespace CFSG.GH74.GLS.SP.Local

open CFSG.ShultStronglyClosedTI.InvolutionCounting

namespace OrdCnt

section Involutions

variable {I : Type} [Group I]

theorem orderOf_conj_eq (g a : I) : orderOf (g * a * g⁻¹) = orderOf a := by
  simpa using (MulAut.conj g).orderOf_eq a

end Involutions
end OrdCnt
end CFSG.GH74.GLS.SP.Local
end
