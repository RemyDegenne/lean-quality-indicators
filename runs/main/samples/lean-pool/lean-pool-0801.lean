@[expose] public section

open Set

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

namespace FreeBeam

namespace Abstract

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

namespace FourthOrderTraceModel

omit [CompleteSpace H] [CompleteSpace V] in
@[simp] theorem embed_maximalAmbientInverse
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.maximalAmbientDomain) :
    D.embed (D.maximalAmbientInverse x) = (x : H) := by
  have h := D.maximalRangeEquiv.apply_symm_apply x
  exact congrArg Subtype.val h

end FourthOrderTraceModel
end
end Abstract
end FreeBeam
end DavisKahan
end TauCeti
end
