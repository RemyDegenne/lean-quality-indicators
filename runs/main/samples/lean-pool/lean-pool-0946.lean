@[expose] public section

noncomputable section

open CategoryTheory Finset

open CategoryTheory.Localization.Construction

universe v u v' pu pv u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]

variable (Z : Center C)

variable {D : Type u} [Category.{v'} D]

variable (F : C ⥤ D)

namespace NaiveCenterCounterexample

open Family Polynomial Multicenter

lemma psiPreDil_respects {x y : CEx.PreDil} (h : CEx.r x y) : psiPreDil x = psiPreDil y := by
  obtain ⟨β, hβ⟩ := h
  have hβ' := congrArg (Polynomial.eval 0) hβ
  simp only [eval_mul] at hβ'
  change x.num.eval 0 * (CEx.elem ^ (β + y.pow)).eval 0 =
    y.num.eval 0 * (CEx.elem ^ (β + x.pow)).eval 0 at hβ'
  rw [CEx_elem_pow_eval, CEx_elem_pow_eval] at hβ'
  simp only [Finsupp.add_apply] at hβ'
  refine IsLocalization.eq.mpr ⟨⟨2 ^ (β ()), β (), rfl⟩, ?_⟩
  change (2 : ℤ) ^ (β ()) * (2 ^ (y.pow ()) * x.num.eval 0) =
    2 ^ (β ()) * (2 ^ (x.pow ()) * y.num.eval 0)
  calc (2 : ℤ) ^ (β ()) * (2 ^ (y.pow ()) * x.num.eval 0)
      = (2 ^ (β ()) * 2 ^ (y.pow ())) * x.num.eval 0 := by ring
    _ = 2 ^ (β () + y.pow ()) * x.num.eval 0 := by rw [pow_add]
    _ = x.num.eval 0 * 2 ^ (β () + y.pow ()) := by ring
    _ = y.num.eval 0 * 2 ^ (β () + x.pow ()) := hβ'
    _ = 2 ^ (β () + x.pow ()) * y.num.eval 0 := by ring
    _ = (2 ^ (β ()) * 2 ^ (x.pow ())) * y.num.eval 0 := by rw [pow_add]
    _ = 2 ^ (β ()) * (2 ^ (x.pow ()) * y.num.eval 0) := by ring

end NaiveCenterCounterexample
end CategoryTheory.Dilatations
end
end
