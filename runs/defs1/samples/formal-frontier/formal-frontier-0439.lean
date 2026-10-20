@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

/-- The chosen generator identifies residues at one exact-index power level
with the corresponding power quotient. -/
noncomputable def residuePowerQuotientComponent (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    {S : Set Nat.Primes} (n : Nat.PowerIndex S)
    (hindex : (powerImage G hG n.val : Subgroup G).index = n.val) :
    (residueDiagram.{u} S).obj n ≅ (powerQuotientDiagram G hG S).obj n := by
  letI : DiscreteTopology ((residueDiagram.{u} S).obj n) := ⟨rfl⟩
  letI : DiscreteTopology ((powerQuotientDiagram G hG S).obj n) := ⟨rfl⟩
  let e : (residueDiagram.{u} S).obj n ≃ₜ*
      (powerQuotientDiagram G hG S).obj n :=
    ContinuousMulEquiv.mk
      ((MulEquiv.ulift :
        ULift.{u} (Multiplicative (ZMod n.val)) ≃* Multiplicative (ZMod n.val)).trans
        (powerImage_zmodContinuousMulEquiv G hG g hg n.val n.pos hindex).toMulEquiv)
      continuous_of_discreteTopology continuous_of_discreteTopology
  exact ContinuousMulEquiv.toProfiniteGrpIso e

end ProfiniteGrp
end
