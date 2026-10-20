@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

@[simp] theorem toPowerQuotientLimit_apply (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes) (n : Nat.PowerIndex S) (g : G) :
    (toPowerQuotientLimit G hG S g).val n =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g := by
  have h := congrArg (fun f : G ⟶ (powerQuotientDiagram G hG S).obj n => f g)
    ((ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S)).fac
      (powerQuotientCone G hG S) n)
  change ((ProfiniteGrp.limitCone (powerQuotientDiagram G hG S)).π.app n)
      (toPowerQuotientLimit G hG S g) =
      (powerQuotientCone G hG S).π.app n g at h
  change (ProfiniteGrp.limitCone (powerQuotientDiagram G hG S)).π.app n
      (toPowerQuotientLimit G hG S g) =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g
  exact h.trans (powerQuotientCone_π_apply G hG S n g)

end ProfiniteGrp
end
