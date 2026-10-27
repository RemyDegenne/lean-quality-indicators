public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits

open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.RadicalLabels

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank

open LinearMap (BilinForm)

open scoped Pointwise

namespace AltEight

open scoped IsMulCommutative

theorem card_mulAut_eq_card_GL {p : ℕ} [Fact p.Prime] {E : Type} [Group E] [Finite E]
    [CFSG.IsElementaryAbelian p E] {n : ℕ} (hE : Nat.card E = p ^ n) :
    Nat.card (MulAut E) = Nat.card (GL (Fin n) (ZMod p)) := by
  classical
  have hfin : Module.finrank (ZMod p) (Additive E) = n := by
    have h := FiniteField.pow_finrank_eq_natCard p (Additive E)
    have h' : Nat.card (Additive E) = p ^ n := hE
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h.trans h')
  let bas := Module.finBasisOfFinrankEq (ZMod p) (Additive E) hfin
  let e1 : MulAut E ≃ (Additive E ≃+ Additive E) := MulEquiv.toAdditive
  let e2 : (Additive E ≃+ Additive E) ≃ (Additive E ≃ₗ[ZMod p] Additive E) :=
    { toFun := fun σ => σ.toLinearEquiv (ZMod.map_smul σ)
      invFun := fun σ => σ.toAddEquiv
      left_inv := fun σ => by ext; rfl
      right_inv := fun σ => by ext; rfl }
  let e3 : (Additive E ≃ₗ[ZMod p] Additive E) ≃*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive E) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm
  let e4 : LinearMap.GeneralLinearGroup (ZMod p) (Additive E) ≃* GL (Fin n) (ZMod p) :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv bas).toMulEquiv
  exact Nat.card_congr (e1.trans (e2.trans (e3.trans e4).toEquiv))

end AltEight
end CFSG.EvenSmallLie.Child3
end
