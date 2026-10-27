@[expose] public section

namespace Stafford38.CharacteristicFilteredQuotientTwoJet

open Stafford38.CharacteristicAssociatedGradedModule

open Stafford38.CharacteristicFilteredQuotientRees

open Stafford38.CharacteristicFilteredQuotientReesAction

open Stafford38.CharacteristicFilteredQuotientReesExact

open Stafford38.CharacteristicFilteredQuotientSpecialFibre

open Stafford38.CharacteristicOrderReesTwoJet

open Stafford38.EulerSurjectivity

open Stafford38.WeylIteratedEquivalence

open Stafford38.WeylOrderRees

noncomputable section

universe u

variable (k : Type u) [Field k]

variable {n : ℕ}

local instance quotientOrderAssociatedGradedSymbolModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (Stafford38.Characteristic.SymbolRing k n)
      (Stafford38.CharacteristicFilteredQuotientGraded.QuotientOrderAssociatedGraded k I) :=
  inferInstanceAs (Module (Stafford38.Characteristic.SymbolRing k n)
    (OrderAssociatedGradedModule k I))

local instance filteredRightQuotientSMul
    (I : RightIdeal (PresentedWeyl k n)) :
    SMul (PresentedWeyl k n)ᵐᵒᵖ
      (Stafford38.CharacteristicFilteredQuotient.FilteredRightQuotient k I) :=
  filteredRightQuotientOpSMul k I

local instance filteredRightQuotientModule
    (I : RightIdeal (PresentedWeyl k n)) :
    Module (PresentedWeyl k n)ᵐᵒᵖ
      (Stafford38.CharacteristicFilteredQuotient.FilteredRightQuotient k I) :=
  filteredRightQuotientOpModule k I

local instance orderPieceOpGradedMonoid :
    SetLike.GradedMonoid
      (CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k) where
  one_mem := by
    rw [mem_orderPieceOp_iff]
    exact (Stafford38.CharacteristicAssociatedGradedModule.orderPieceOne
      (n := n) k).property
  mul_mem := by
    intro N M y z hy hz
    rw [mem_orderPieceOp_iff] at hy hz ⊢
    rw [MulOpposite.unop_mul]
    simpa [Nat.add_comm] using
      Stafford38.WeylFiltration.mul_mem_orderPiece k hz hy

local instance orderPieceOpGradedSMul
    (I : RightIdeal (PresentedWeyl k n)) :
    SetLike.GradedSMul
      (CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k)
      (Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I) where
  smul_mem := by
    intro M N y q hy hq
    obtain ⟨z, hz, rfl⟩ := hq
    rw [mem_orderPieceOp_iff] at hy
    refine ⟨z * y.unop, ?_, ?_⟩
    · simpa [Nat.add_comm] using
        Stafford38.WeylFiltration.mul_mem_orderPiece k hz hy
    rfl

local instance orderPieceOpGMulAction
    (I : RightIdeal (PresentedWeyl k n)) :
    GradedMonoid.GMulAction
      (fun N => CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k N)
      (fun N => Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I N) :=
  { SetLike.toGSMul
      (CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k)
      (Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I) with
    one_smul := fun ⟨_i, _m⟩ =>
      Sigma.subtype_ext (zero_vadd _ _) (one_smul _ _)
    mul_smul := fun ⟨_i, _a⟩ ⟨_j, _a'⟩ ⟨_l, _b⟩ =>
      Sigma.subtype_ext (add_vadd _ _ _) (mul_smul _ _ _) }

local instance orderPieceOpGdistribMulAction
    (I : RightIdeal (PresentedWeyl k n)) :
    DirectSum.GdistribMulAction
      (fun N => CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k N)
      (fun N => Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I N) :=
  { orderPieceOpGMulAction (n := n) k I with
    smul_add := fun _a _b _c => Subtype.ext <| smul_add _ _ _
    smul_zero := fun _a => Subtype.ext <| smul_zero _ }

local instance orderPieceOpGmodule
    (I : RightIdeal (PresentedWeyl k n)) :
    DirectSum.Gmodule
      (fun N => CharacteristicFilteredQuotientReesAction.orderPieceOp (n := n) k N)
      (fun N => Stafford38.CharacteristicFilteredQuotient.quotientOrderPiece k I N) :=
  { orderPieceOpGdistribMulAction (n := n) k I with
    add_smul := fun _a _a' _b => Subtype.ext <| add_smul _ _ _
    zero_smul := fun _b => Subtype.ext <| zero_smul _ _ }

local instance quotientOrderReesModule_smulCommClass
    (I : RightIdeal (PresentedWeyl k n)) :
    SMulCommClass (OrderReesRing (n := n) k)ᵐᵒᵖ k
      (QuotientOrderReesModule k I) where
  smul_comm r a x := by
    change
      (orderPieceOpDirectSumEquivReesOp (n := n) k).symm r • (a • x) =
        a • ((orderPieceOpDirectSumEquivReesOp (n := n) k).symm r • x)
    exact oppositeOrderPieceSum_smul_comm k I _ _ _

/-- The source opposite-Rees action descends to the additive two-jet
quotient. -/
def quotientOrderReesSourceAction
    (I : RightIdeal (PresentedWeyl k n))
    (r : (OrderReesRing (n := n) k)ᵐᵒᵖ) :
    FilteredQuotientTwoJet k I →ₗ[k] FilteredQuotientTwoJet k I :=
  (quotientOrderReesTwoJetSubmodule k I).mapQ
    (quotientOrderReesTwoJetSubmodule k I)
    (DistribSMul.toLinearMap k (QuotientOrderReesModule k I) r)
    (by
      intro x hx
      exact op_smul_mem_quotientOrderReesTwoJetSubmodule k I r hx)

end
end Stafford38.CharacteristicFilteredQuotientTwoJet
end
