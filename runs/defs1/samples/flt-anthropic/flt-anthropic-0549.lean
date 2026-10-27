namespace P2MW.S_CerednikDrinfeld_exists_injective_mem_rationalHomSet_kernelIdealSet_eq_nrd_dvd

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option linter.unusedSectionVars false

open Polynomial

namespace FrobeniusKernelIdeal

open WeierstrassCurve WeierstrassCurve.Affine Polynomial FrobeniusKernelIdeal.Poly

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

scoped instance instIsEllipticFrobTwist (W : WeierstrassCurve k) [W.IsElliptic] : (frobTwist p W).IsElliptic := by
  unfold frobTwist; infer_instance

omit [IsAlgClosed k] [DecidableEq k] [Fact p.Prime] [CharP k p] in

scoped instance instIsEllipticBaseChangeSelf (W : WeierstrassCurve k) [W.IsElliptic] : (W.baseChange k).IsElliptic := by
  unfold WeierstrassCurve.baseChange; infer_instance

noncomputable def frobPt (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (frobTwist p W).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (x ^ p) (y ^ p) (frob_nonsingular p W h)
  map_zero' := rfl
  map_add' := by
    have hf : ∀ z : k, frobenius k p z = z ^ p := frobenius_def p
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.left hxy.right]
      have h2 : y₁ ^ p = (frobTwist p W).toAffine.negY (x₂ ^ p) (y₂ ^ p) := by
        rw [hxy.right, ← hf, ← hf, ← hf, Affine.map_negY]
      rw [Affine.Point.add_of_Y_eq (congr_arg (· ^ p) hxy.left) h2]
    · have hxy' : ¬ (x₁ ^ p = x₂ ^ p ∧
          y₁ ^ p = (frobTwist p W).toAffine.negY (x₂ ^ p) (y₂ ^ p)) := by
        rintro ⟨e1, e2⟩
        apply hxy
        refine ⟨frobenius_inj k p (by rw [hf, hf]; exact e1), frobenius_inj k p ?_⟩
        rw [hf, hf, e2, ← hf, ← hf, Affine.map_negY, hf]
      rw [Affine.Point.add_some hxy, Affine.Point.add_some hxy']
      simp only [Affine.Point.some.injEq]
      refine ⟨?_, ?_⟩
      · rw [← hf, ← hf, ← hf, ← hf, ← hf, Affine.map_slope, Affine.map_addX]
      · rw [← hf, ← hf, ← hf, ← hf, ← hf, Affine.map_slope, Affine.map_addY]

end Frobenius
end FrobeniusKernelIdeal
end P2MW.S_CerednikDrinfeld_exists_injective_mem_rationalHomSet_kernelIdealSet_eq_nrd_dvd
