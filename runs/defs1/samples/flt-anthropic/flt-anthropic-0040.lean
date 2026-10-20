namespace P2MW.S_M4aHerbrand_adeleBaseChange_local_rigidity

set_option autoImplicit false

section Fold_AdeleCorners

namespace M4aHerbrand

namespace Rigidity

p2m_open

open NumberField IsDedekindDomain

section Corners

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

variable [DecidableEq (InfinitePlace F)] [DecidableEq (HeightOneSpectrum R)]

noncomputable def singleFinStratum (w : HeightOneSpectrum R) (t : w.adicCompletion F) :
    RestrictedProduct (fun u : HeightOneSpectrum R => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (Filter.principal ({w}ᶜ)) :=
  ⟨Pi.single w t, by
    rw [Filter.eventually_principal]
    intro u hu
    rw [Pi.single_eq_of_ne (by simpa using hu)]
    exact zero_mem _⟩

end Corners
end Rigidity
end M4aHerbrand
end Fold_AdeleCorners
end P2MW.S_M4aHerbrand_adeleBaseChange_local_rigidity
