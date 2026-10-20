namespace P2MW.S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion

set_option autoImplicit false

p2m_open

open scoped Topology

namespace NumberField

namespace WeakApprox

p2m_open

variable (K : Type*) [Field K] [NumberField K]

noncomputable def absFamily (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ ↥S → AbsoluteValue K ℝ :=
  Sum.elim (fun w => w.1) (fun v => NumberField.HeightOneSpectrum.adicAbv K v.1)

end WeakApprox
end NumberField
end P2MW.S_NumberField_denseRange_algebraMap_infiniteAdeleRing_prod_adicCompletion
