@[expose] public noncomputable section

open Filter

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

theorem isClosed_subjet_hessian_slice (C : Set (Point n)) (u : Point n -> Real)
    (x : Point n) (p : Point n) :
    IsClosed {X : Hessian n | ({ gradient := p, hessian := X } : Jet n) ∈ Subjet C u x} := by
  rw [← closure_subset_iff_isClosed]
  intro X hX
  refine subjet_of_subjetExcess_secondOrderNonposWithin ?_
  intro ε hε
  let denom : Real := (n : Real) * (n : Real) + 1
  have hdenom_pos : 0 < denom := by
    have hn2 : 0 <= (n : Real) * (n : Real) :=
      mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n)
    dsimp [denom]
    linarith
  let η : Real := ε / denom
  have hηpos : 0 < η := div_pos hε hdenom_pos
  have hηnonneg : 0 <= η := hηpos.le
  have hnbhd : {Y : Hessian n | ∀ i j : Fin n, |(Y - X) i j| < η} ∈ nhds X :=
    hessian_eventually_entrywise_abs_sub_lt X hηpos
  rcases (mem_closure_iff_nhds.mp hX _ hnbhd) with ⟨Y, hYclose, hYjet⟩
  have hbase := subjetExcess_secondOrderNonposWithin hYjet (ε / 2) (by linarith)
  have hcoef : (1 / 2 : Real) * η * (n : Real) * (n : Real) <= ε / 2 := by
    have hn2_nonneg : 0 <= (n : Real) * (n : Real) :=
      mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n)
    have hfrac : ((n : Real) * (n : Real)) / denom <= 1 := by
      rw [div_le_one hdenom_pos]
      dsimp [denom]
      linarith
    calc
      (1 / 2 : Real) * η * (n : Real) * (n : Real) =
          (ε / 2) * (((n : Real) * (n : Real)) / denom) := by
        dsimp [η]
        field_simp [hdenom_pos.ne']
      _ <= (ε / 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hfrac (by linarith)
      _ = ε / 2 := by ring
  filter_upwards [hbase] with y hy
  let JX : Jet n := { gradient := p, hessian := X }
  let JY : Jet n := { gradient := p, hessian := Y }
  have hA : ∀ i j : Fin n, |(X - Y) i j| <= η := by
    intro i j
    have hclose := (hYclose i j).le
    simpa [Pi.sub_apply, abs_sub_comm] using hclose
  have hquad_abs : |quadraticModel x 0 0 (X - Y) y| <=
      ((1 / 2 : Real) * η * (n : Real) * (n : Real)) * ‖y - x‖ ^ 2 :=
    abs_quadraticModel_zero_zero_le_of_entrywise_abs_le x y hηnonneg hA
  have hquad : quadraticModel x 0 (JX - JY).gradient (JX - JY).hessian y <=
      (ε / 2) * ‖y - x‖ ^ 2 := by
    have hq1 : quadraticModel x 0 (JX - JY).gradient (JX - JY).hessian y =
        quadraticModel x 0 0 (X - Y) y := by
      simp [JY, JX]
    rw [hq1]
    have hle_abs :
        quadraticModel x 0 0 (X - Y) y <= |quadraticModel x 0 0 (X - Y) y| :=
      le_abs_self _
    exact hle_abs.trans (hquad_abs.trans (by gcongr))
  have hformula := subjetExcess_eq_add_quadraticModel_sub u x JX JY y
  change SubjetExcess u x JX y <= ε * ‖y - x‖ ^ 2
  rw [hformula]
  nlinarith [sq_nonneg ‖y - x‖]

end ViscositySolns
end
