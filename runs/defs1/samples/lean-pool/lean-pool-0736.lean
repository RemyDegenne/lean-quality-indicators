@[expose] public section

namespace OneMfld

open Set

noncomputable section

/-- The affine map `x ↦ k·x + d` as a chart from `Ioo 0 1 ⊆ ℝ≥0` onto
`Ioo d (d + k) ⊆ ℝ`. -/
def affineNNRealOPH (k d : ℝ) (hk : 0 < k) :
    { e : OpenPartialHomeomorph NNReal ℝ //
      e.source = Ioo 0 1 ∧ e.target = Ioo d (d + k) ∧
      ∀ x : NNReal, e.toFun x = k * (x : ℝ) + d } := by
  refine ⟨{ toFun := fun x => k * (x : ℝ) + d
            invFun := fun y => Real.toNNReal ((y - d) / k)
            source := Ioo 0 1
            target := Ioo d (d + k)
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := isOpen_Ioo
            open_target := isOpen_Ioo
            continuousOn_toFun :=
              ((continuous_const.mul NNReal.continuous_coe).add continuous_const).continuousOn
            continuousOn_invFun :=
              (continuous_real_toNNReal.comp
                ((continuous_id.sub continuous_const).div_const k)).continuousOn },
    rfl, rfl, fun x => rfl⟩
  · intro x hx
    have hx0 : (0:ℝ) < x := hx.1
    have hx1 : (x:ℝ) < 1 := hx.2
    constructor
    · nlinarith
    · nlinarith
  · intro y hy
    exact ⟨Real.toNNReal_pos.mpr (div_pos (sub_pos.mpr hy.1) hk),
      Real.toNNReal_lt_one.mpr ((div_lt_one hk).mpr (by linarith [hy.2]))⟩
  · intro x _
    show Real.toNNReal ((k * (x:ℝ) + d - d) / k) = x
    have h : (k * (x:ℝ) + d - d) / k = (x:ℝ) := by
      field_simp
      ring
    rw [h, Real.toNNReal_coe]
  · intro y hy
    show k * ((Real.toNNReal ((y - d) / k) : NNReal) : ℝ) + d = y
    rw [Real.coe_toNNReal _ (div_nonneg (sub_nonneg.mpr hy.1.le) hk.le)]
    field_simp
    ring

end
end OneMfld
end
