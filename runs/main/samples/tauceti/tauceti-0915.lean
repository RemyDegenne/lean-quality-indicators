public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

open LaurentPolynomial hiding C

universe v v' u u' w w'

namespace LaurentK0

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]

variable {E : GradedExactStructure C} {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]

theorem forgetGradingMap_injective_iff
    (hF : E.toExactStructure.IsConflationExact E' F) (comm : E.shift.functor ⋙ F ≅ F) :
    Function.Injective (forgetGradingMap hF comm) ↔
      LinearMap.ker (forgetGradingUnderlyingMap hF) =
        ((RingHom.ker (laurentEval (R := ℤ) (1 : ℤˣ)) • ⊤ :
          Submodule (LaurentPolynomial ℤ) (LaurentK0 E)).restrictScalars ℤ) := by
  let p := ((RingHom.ker (laurentEval (R := ℤ) (1 : ℤˣ)) • ⊤ :
    Submodule (LaurentPolynomial ℤ) (LaurentK0 E)).restrictScalars ℤ)
  have hp : p ≤ LinearMap.ker (forgetGradingUnderlyingMap hF) := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hzero : (LaurentSpecialization.mk (R := ℤ) 1 x :
        LaurentSpecialization (1 : ℤˣ) (LaurentK0 E)) = 0 := by
      rw [LaurentSpecialization.mk_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    have := congrArg (forgetGradingMap hF comm) hzero
    simpa using this
  let g := p.liftQ (forgetGradingUnderlyingMap hF)
    (fun x hx ↦ LinearMap.mem_ker.mp (hp hx))
  let e := Submodule.Quotient.restrictScalarsEquiv ℤ
    (RingHom.ker (laurentEval (R := ℤ) (1 : ℤˣ)) • ⊤ :
      Submodule (LaurentPolynomial ℤ) (LaurentK0 E))
  have hmap : forgetGradingMap hF comm = g.comp e.symm.toLinearMap := by
    apply LaurentSpecialization.hom_ext
    intro x
    rw [forgetGradingMap_mk, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LaurentSpecialization.mk_apply, Submodule.Quotient.restrictScalarsEquiv_symm_mk]
    exact (Submodule.liftQ_apply p (forgetGradingUnderlyingMap hF) x).symm
  have hinjective : Function.Injective (g.comp e.symm.toLinearMap) ↔
      Function.Injective g := by
    rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap]
    exact Function.Injective.of_comp_iff' g e.symm.bijective
  rw [hmap]
  rw [hinjective, ← LinearMap.ker_eq_bot]
  constructor
  · intro hbot
    apply le_antisymm
    · intro x hx
      have hmk : Submodule.mkQ p x ∈
          (LinearMap.ker (forgetGradingUnderlyingMap hF)).map (Submodule.mkQ p) :=
        ⟨x, hx, rfl⟩
      rw [← Submodule.ker_liftQ p (forgetGradingUnderlyingMap hF)
          (fun y hy ↦ LinearMap.mem_ker.mp (hp hy)),
        hbot, Submodule.mem_bot] at hmk
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk
    · exact hp
  · intro hker
    exact Submodule.ker_liftQ_eq_bot' p (forgetGradingUnderlyingMap hF) hker.symm

end LaurentK0
end TauCeti
end
