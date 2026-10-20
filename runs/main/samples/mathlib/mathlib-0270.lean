@[expose] public section

open Set Function

open Module hiding reflection

open Submodule (span span_image)

open AddSubgroup (zmultiples)

noncomputable section

variable (ι R M N : Type*)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

attribute [instance] RootPairing.isPerfPair_toLinearMap

namespace RootPairing

variable {ι R M N}

variable (P : RootPairing ι R M N) (i j : ι)

lemma reflectionPerm_involutive : Involutive (P.reflectionPerm i) :=
  involutive_iff_iter_2_eq_id.mpr (by ext; simp)

end RootPairing
end
end
