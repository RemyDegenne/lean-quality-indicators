import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import P2M.Util
namespace P2MW.S_Module_Flat_of_flat_of_faithfullyFlat_right

set_option autoImplicit false

open TensorProduct

namespace Module p2m_export "Module" "Flat Flat.iff_lTensor_preserves_injective_linearMap Injective FaithfullyFlat FaithfullyFlat.lTensor_injective_iff_injective Flat.lTensor_preserves_injective_linearMap" namespace Flat p2m_export "Module.Flat" "iff_lTensor_preserves_injective_linearMap baseChange lTensor_preserves_injective_linearMap" end Module.Flat
p2m_open_scoped "Module Module.Flat" in

theorem Module.Flat.of_flat_of_faithfullyFlat_right_aux (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  rw [← LinearMap.baseChange_eq_ltensor,
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective S T]
  have key : ∀ x, TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P
      (((f.baseChange S).lTensor T) x) =
      f.lTensor T (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul t y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul s n => simp [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul]
  have hT : Function.Injective (f.lTensor T) := Module.Flat.lTensor_preserves_injective_linearMap f hf
  have : Function.Injective (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P ∘
      ((f.baseChange S).lTensor T)) := by
    rw [show (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P ∘
        ((f.baseChange S).lTensor T) : _ → _) =
        f.lTensor T ∘ TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N from funext key]
    exact hT.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N).injective
  exact this.of_comp

theorem solution (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S :=
  Module.Flat.of_flat_of_faithfullyFlat_right_aux R S T
