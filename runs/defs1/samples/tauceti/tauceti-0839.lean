public section

noncomputable section

open Filter Metric Set Topology

namespace TauCeti

local notation "𝔻" => Set.Elem (ball (0 : ℂ) 1)

local notation "𝔻*" => Set.Elem (ball (0 : ℂ) 1 \ {0})

variable {E ι : Type*}

/-- The **puncture filling** of `E` along the punctured discs `φ i : 𝔻* → E`: the space `E` with
one point `PunctureFilling.center φ i` added for every `i`, which fills the puncture of `φ i`. Its
topology is the final topology of the inclusion `PunctureFilling.incl` of `E` and of the filled
discs `PunctureFilling.disc φ i : 𝔻 → PunctureFilling φ`.

Its points are those of the sum `E ⊕ ι`; the constructor is private, and points are built with
`PunctureFilling.incl` and `PunctureFilling.center` and taken apart with
`PunctureFilling.induction`. -/
structure PunctureFilling (φ : ι → 𝔻* → E) : Type _ where
  private mk ::
  /-- A point of the puncture filling as a point of `E ⊕ ι`: a point of `E`, or the index of the
  puncture it fills. -/
  toSum : E ⊕ ι

end TauCeti
end
end
