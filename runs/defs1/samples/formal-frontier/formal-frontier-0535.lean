@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

/-- The corresponding diagram of profinite groups, with finite coordinates. -/
def powerQuotientDiagram (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (S : Set Nat.Primes) : Nat.PowerIndex S ⥤ ProfiniteGrp.{u} :=
  powerIndexFunctor G hG S ⋙ G.diagram

end ProfiniteGrp
end
