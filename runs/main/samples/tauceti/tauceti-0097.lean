public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField

variable (K : Type) [Field K] [NumberField K]

variable [DecidableEq (HeightOneSpectrum (𝓞 K))]

@[simp]
theorem sumLocalInvSection_apply (v : HeightOneSpectrum (𝓞 K)) (r : AddCircle (1 : ℚ)) :
    sumLocalInvSection K v r = (DFinsupp.single v ((invMap (v.adicCompletion K)).symm r), 0) :=
  (rfl)

end TauCeti.ClassFieldTheory
end
end
