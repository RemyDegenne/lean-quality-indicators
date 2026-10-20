@[expose] public section

namespace NRR

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismStableRelativeBoundary

namespace StableFullCollarOriginMarginAffinePullback

open EquivariantCoordinateHomotopy

open RefinedAffineMap

open StableFullCollarOriginMargin

open StableFullCollarConstructionAffinePullback

variable {p : Nat}

theorem affinePullback_margin_pos
    (hp : Nat.Prime p)
    (F₀ F₁ : ZeroFreeMap hp)
    (H : ZeroFreeHomotopy hp F₀ F₁)
    (A₀ : StableRegularApproximation hp F₀.map)
    (A₁ : StableRegularApproximation hp F₁.map) :
    0 < (fullCollarOriginMarginDataAffinePullback hp F₀ F₁ H A₀ A₁).margin :=
  (fullCollarOriginMarginDataAffinePullback hp F₀ F₁ H A₀ A₁).margin_pos

end StableFullCollarOriginMarginAffinePullback
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
end
