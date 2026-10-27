public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory

open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u

noncomputable section

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}
  {I : HopfIdeal k H}

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- The quotient from the scheme-theoretic kernel of the coinvariant projection to the proposed
normal subgroup. It is induced by the always-valid inclusion
`kernelHopfIdeal (coinvariantsι hI) ≤ I`. -/
noncomputable abbrev coinvariantsKernelQuotientMap (hI : I.IsNormal) :
    quotient H (kernelHopfIdeal (coinvariantsι hI)) ⟶ quotient H I :=
  quotientMapOfLe H (kernelHopfIdeal_coinvariantsι_le hI)

end
end TauCeti.CommHopfAlgCat
end
