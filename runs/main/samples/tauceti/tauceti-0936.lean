public section

noncomputable section

open Set Topology

open scoped Topology.Homotopy

universe u

namespace TauCeti

theorem subsingleton_homotopyGroup_universalGSpace (G : Type u) [Nonempty G]
    (n : ℕ) (x : universalGSpace G) :
    Subsingleton (π_ (n + 1) (universalGSpace G) x) :=
  subsingleton_homotopyGroup_realization_indexedJoin
    (Set.infinite_univ.mono fun _ _ => ‹Nonempty G›) (Fin (n + 1)) x

end TauCeti
end
end
