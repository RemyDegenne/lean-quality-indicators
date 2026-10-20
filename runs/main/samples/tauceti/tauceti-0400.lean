public section

namespace TauCeti

open CategoryTheory ContRepresentation TopRep _root_.ContinuousCohomology ContinuousMap

universe u v w

namespace TopPairing

section degreeZero

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

theorem resolutionCupPairing_zero_eq_flip (n : ℕ) (x : X.V)
    (b : (TopRep.resolution'X Y n).V) :
    P.resolutionCupPairing 0 n ((TopRep.d X 0).hom x) b =
      ((TopRep.resolution Z).XIsoOfEq (by omega : n + 0 + 1 = 0 + n + 1)).hom.hom
        (P.flip.resolutionCupPairing n 0 b ((TopRep.d X 0).hom x)) := by
  rw [resolutionCupPairing_apply, resolutionCupPairing_apply]
  calc
    _ = P.flip.resolutionCup n 0 (0 + n) (by omega)
        (b, (TopRep.d X 0).hom x) :=
      P.resolutionCup_zero_eq_flip n (0 + n) (by omega) x b
    _ = ((TopRep.resolution Z).XIsoOfEq
          (by omega : n + 0 + 1 = 0 + n + 1)).hom.hom
        (P.flip.resolutionCup n 0 (n + 0) (Nat.add_comm n 0)
          (b, (TopRep.d X 0).hom x)) :=
      (P.flip.resolutionCup_cast (Nat.add_comm n 0) (by omega)
        (by omega : n + 0 + 1 = 0 + n + 1) (b, (TopRep.d X 0).hom x)).symm

end degreeZero
end TopPairing
end TauCeti
end
