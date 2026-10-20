@[expose] public section

universe uι uR uS uM uN

namespace ModuleCat

namespace RightExtension

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

/-- An arbitrary right module over a finite coefficient product is reconstructed
from its right scalar extensions along all coordinate projections. -/
noncomputable def piLinearEquiv [Finite ι]
    (M : ModuleCat.{uM} (∀ i, Ri i)ᵐᵒᵖ) :
    M ≃ₗ[(∀ i, Ri i)ᵐᵒᵖ] ModuleCat.piRight Ri
      (fun i => ModuleCat.of (Ri i)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri i) M)) := by
  classical
  letI := Fintype.ofFinite ι
  let Ei := fun i => ModuleCat.of (Ri i)ᵐᵒᵖ (Obj (Pi.evalRingHom Ri i) M)
  let q : ∀ i, Obj (Pi.evalRingHom Ri i) M →+ M := fun i => by
    letI : Module (∀ j, Ri j) (Ri i) := (Pi.evalRingHom Ri i).toModule
    exact BalancedTensorProduct.lift (R := ∀ j, Ri j) (M := M) (N := Ri i)
      { toFun := fun m r => MulOpposite.op (Pi.single i r) • m
        map_zero_left := fun r => smul_zero _
        map_add_left := fun m n r => smul_add _ m n
        map_zero_right := fun m => by simp
        map_add_right := fun m r s => by
          rw [Pi.single_add, MulOpposite.op_add, add_smul]
        balance := fun a m r => by
          change MulOpposite.op (Pi.single i r) • (MulOpposite.op a • m) =
            MulOpposite.op (Pi.single i (a i * r)) • m
          rw [← mul_smul]
          change MulOpposite.op (a * Pi.single i r) • m =
            MulOpposite.op (Pi.single i (a i * r)) • m
          rw [Pi.single_mul_right r] }
  have q_tmul : ∀ i (m : M) (r : Ri i),
      q i (tmul (Pi.evalRingHom Ri i) m r) = MulOpposite.op (Pi.single i r) • m := by
    intro i m r
    let _ : Module (∀ j, Ri j) (Ri i) := (Pi.evalRingHom Ri i).toModule
    exact BalancedTensorProduct.lift_tmul (R := ∀ j, Ri j) (M := M) (N := Ri i) _ m r
  have q_smul : ∀ i (a : ∀ j, Ri j) (z : Obj (Pi.evalRingHom Ri i) M),
      q i (MulOpposite.op (a i) • z) = MulOpposite.op a • q i z := by
    intro i a z
    let _ : Module (∀ j, Ri j) (Ri i) := (Pi.evalRingHom Ri i).toModule
    induction z using BalancedTensorProduct.induction_on with
    | zero => simp
    | pure m r =>
        change q i (MulOpposite.op (a i) • tmul (Pi.evalRingHom Ri i) m r) =
          MulOpposite.op a • q i (tmul (Pi.evalRingHom Ri i) m r)
        rw [tmul_smul, q_tmul, q_tmul]
        change MulOpposite.op (Pi.single i (r * a i)) • m =
          MulOpposite.op a • (MulOpposite.op (Pi.single i r) • m)
        rw [← mul_smul]
        change MulOpposite.op (Pi.single i (r * a i)) • m =
          MulOpposite.op (Pi.single i r * a) • m
        rw [Pi.single_mul_left r]
    | neg z hz =>
        rw [smul_neg, (q i).map_neg, hz, (q i).map_neg, smul_neg]
    | add z w hz hw =>
        rw [smul_add, (q i).map_add, hz, hw, (q i).map_add, smul_add]
  let T : M →ₗ[(∀ i, Ri i)ᵐᵒᵖ] ModuleCat.piRight Ri Ei :=
    { toFun := fun m i => tmul (Pi.evalRingHom Ri i) m 1
      map_add' := fun m n => by
        apply funext
        intro i
        exact (tmulOne (Pi.evalRingHom Ri i)).map_add m n
      map_smul' := fun a m => by
        apply (ModuleCat.piRight_ext_iff Ri Ei _ _).2
        intro i
        change tmul (Pi.evalRingHom Ri i) (a • m) 1 =
          MulOpposite.op ((MulOpposite.unop a) i) • tmul (Pi.evalRingHom Ri i) m 1
        exact (tmulOne (Pi.evalRingHom Ri i)).map_smulₛₗ a m }
  let Q : ModuleCat.piRight Ri Ei →ₗ[(∀ i, Ri i)ᵐᵒᵖ] M :=
    { toFun := fun x => ∑ i, q i (x i)
      map_add' := fun x y => by
        calc
          (∑ i, q i ((x + y) i)) = ∑ i, q i (x i + y i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact congrArg (q i) (ModuleCat.piRight_add_apply Ri Ei x y i)
          _ = ∑ i, (q i (x i) + q i (y i)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact (q i).map_add (x i) (y i)
          _ = _ := Finset.sum_add_distrib
      map_smul' := fun a x => by
        change (∑ i, q i ((a • x) i)) = a • ∑ i, q i (x i)
        calc
          (∑ i, q i ((a • x) i)) = ∑ i, a • q i (x i) := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              q i ((a • x) i) =
                  q i (MulOpposite.op ((MulOpposite.unop a) i) • x i) :=
                congrArg (q i)
                  (ModuleCat.piRight_smul_apply Ri Ei (MulOpposite.unop a) x i)
              _ = MulOpposite.op (MulOpposite.unop a) • q i (x i) :=
                q_smul i (MulOpposite.unop a) (x i)
              _ = a • q i (x i) :=
                congrArg (fun b : (∀ j, Ri j)ᵐᵒᵖ => b • q i (x i))
                  (MulOpposite.op_unop a)
          _ = _ := (Finset.smul_sum (r := a) (f := fun i => q i (x i))
            (s := Finset.univ)).symm }
  have hcoord : ∀ i (z : Obj (Pi.evalRingHom Ri i) M),
      T (q i z) = ModuleCat.piRightSingle Ri Ei i z := by
    intro i z
    let si : Obj (Pi.evalRingHom Ri i) M →+ ModuleCat.piRight Ri Ei :=
      { toFun := ModuleCat.piRightSingle Ri Ei i
        map_zero' := ModuleCat.piRightSingle_zero Ri Ei i
        map_add' := fun x y => ModuleCat.piRightSingle_add Ri Ei i x y }
    let _ : Module (∀ j, Ri j) (Ri i) := (Pi.evalRingHom Ri i).toModule
    exact DFunLike.congr_fun
      (BalancedTensorProduct.hom_ext (R := ∀ j, Ri j) (M := M) (N := Ri i)
        (g := T.toAddMonoidHom.comp (q i)) (h := si) fun m r => by
          change T (q i (tmul (Pi.evalRingHom Ri i) m r)) =
            ModuleCat.piRightSingle Ri Ei i (tmul (Pi.evalRingHom Ri i) m r)
          rw [q_tmul]
          apply funext
          intro j
          change tmul (Pi.evalRingHom Ri j) (MulOpposite.op (Pi.single i r) • m) 1 =
            ModuleCat.piRightSingle Ri Ei i (tmul (Pi.evalRingHom Ri i) m r) j
          rw [smul_tmul]
          by_cases h : j = i
          · subst j
            rw [ModuleCat.piRightSingle_apply_same]
            change tmul (Pi.evalRingHom Ri i) m ((Pi.single i r) i * 1) =
              tmul (Pi.evalRingHom Ri i) m r
            rw [Pi.single_eq_same, mul_one]
          · rw [ModuleCat.piRightSingle_apply_ne Ri Ei i j h]
            change tmul (Pi.evalRingHom Ri j) m ((Pi.single i r) j * 1) = 0
            rw [Pi.single_eq_of_ne h, zero_mul]
            simp [tmul]) z
  have hid : (∑ i, Pi.single i (1 : Ri i)) = (1 : ∀ i, Ri i) := by
    apply funext
    intro j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · exact Pi.single_eq_same j 1
    · intro i _ h
      exact Pi.single_eq_of_ne h.symm 1
    · simp
  refine
    { __ := T
      invFun := Q
      left_inv := ?_
      right_inv := ?_ }
  · intro m
    change (∑ i, q i (tmul (Pi.evalRingHom Ri i) m 1)) = m
    simp_rw [q_tmul]
    rw [← Finset.sum_smul]
    calc
      (∑ i, MulOpposite.op (Pi.single i (1 : Ri i))) • m =
          MulOpposite.op (∑ i, Pi.single i (1 : Ri i)) • m :=
        congrArg (fun a : (∀ i, Ri i)ᵐᵒᵖ => a • m)
          (map_sum (MulOpposite.opAddEquiv : (∀ i, Ri i) ≃+ (∀ i, Ri i)ᵐᵒᵖ)
            (fun i => Pi.single i (1 : Ri i)) Finset.univ).symm
      _ = m := by rw [hid]; simp
  · intro x
    change T (∑ i, q i (x i)) = x
    rw [map_sum]
    simp_rw [hcoord]
    have hx := ModuleCat.piRight_eq_finsum_single Ri Ei x
    rw [finsum_eq_sum_of_fintype] at hx
    exact hx.symm

end Pi
end RightExtension
end ModuleCat
end
