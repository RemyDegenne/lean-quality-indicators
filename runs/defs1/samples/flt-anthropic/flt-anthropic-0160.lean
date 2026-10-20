set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 800000

namespace ModularCurve

open AlgebraicCurve

noncomputable def qExpGens (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {ι : Type*}
    (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i) : Option ι → Module.End K (LaurentSeries K)
  | none => LaurentSeries.heckeU K p (Fact.out : p.Prime).pos
  | some i => LaurentSeries.heckeT K (ℓ i) (hℓ i) 2

end ModularCurve
