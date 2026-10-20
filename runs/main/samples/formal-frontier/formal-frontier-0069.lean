@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

@[simp] theorem powerOpenNormalSubgroup_toSubgroup (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) {S : Set Nat.Primes} (n : Nat.PowerIndex S) :
    (powerOpenNormalSubgroup G hG n).toSubgroup =
      (powerImage G hG n.val : Subgroup G) := rfl

end ProfiniteGrp
end
