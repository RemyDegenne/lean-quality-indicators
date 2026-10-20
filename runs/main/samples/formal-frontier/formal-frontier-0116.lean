@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

@[simp] theorem powerQuotientDiagram_map_mk (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes) {n d : Nat.PowerIndex S}
    (f : n ⟶ d) (g : G) :
    (powerQuotientDiagram G hG S).map f
      (QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g) =
      QuotientGroup.mk' (powerImage G hG d.val : Subgroup G) g := by
  have h := congrArg (fun m : G ⟶ (powerQuotientDiagram G hG S).obj d => m g)
    ((powerQuotientCone G hG S).w f)
  change (powerQuotientDiagram G hG S).map f
      ((powerQuotientCone G hG S).π.app n g) =
      (powerQuotientCone G hG S).π.app d g at h
  simpa only [powerQuotientCone_π_apply] using h

end ProfiniteGrp
end
