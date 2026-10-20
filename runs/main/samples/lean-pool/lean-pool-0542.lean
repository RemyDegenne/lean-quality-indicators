@[expose] public section

namespace NRR

theorem avvakumov_akopyan_karasev_affinePullback :
    ∀ (K : Geometry.ConvexBody Geometry.Plane) (n : Nat), 0 < n →
      ∃ P : ConvexPartition K n, P.IsFair :=
  avvakumov_akopyan_karasev

end NRR
end
