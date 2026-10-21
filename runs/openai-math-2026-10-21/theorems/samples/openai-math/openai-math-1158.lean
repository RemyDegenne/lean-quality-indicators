namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit

open scoped ContDiff Topology

open Set Function Filter

open scoped Manifold

open Manifold

variable (m : ℕ)

theorem minus_coordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    minus (annulusCoordinate m x)=x.2 1 := by
  rw [minus,inverse_coordinate m hx,annulusCoordinate_apply]
  ring

end PackingSufficiencySupport.DiagonalQuadrics.Explicit
end
end OAI
