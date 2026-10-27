@[expose] public section

universe uι uR uM uN uP

namespace Module

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) (Mi : ι → Type uM)

variable [∀ i, Semiring (Ri i)] [∀ i, AddCommMonoid (Mi i)]

variable [∀ i, Module (Ri i)ᵐᵒᵖ (Mi i)]

variable (Ni : ι → Type uN) [∀ i, AddCommMonoid (Ni i)]

variable [∀ i, Module (Ri i)ᵐᵒᵖ (Ni i)]

/-- Maps linear for the canonical right coefficient-product action correspond
additively to families of factor-linear maps. -/
noncomputable def piRightHomAddEquiv :
    (@LinearMap (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ri i)ᵐᵒᵖ _ _ (RingHom.id _)
      (∀ i, Mi i) (∀ i, Ni i) _ _ (piRightModule Ri Mi) (piRightModule Ri Ni)) ≃+
        (∀ i, Mi i →ₗ[(Ri i)ᵐᵒᵖ] Ni i) := by
  classical
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Mi i) := piRightModule Ri Mi
  letI : Module (∀ i, Ri i)ᵐᵒᵖ (∀ i, Ni i) := piRightModule Ri Ni
  exact
    { toFun := fun f i =>
        { toFun := fun m => f (Pi.single i m) i
          map_add' := by
            intro m n
            rw [Pi.single_add]
            exact congrArg (fun y : ∀ i, Ni i => y i)
              (f.map_add (Pi.single i m) (Pi.single i n))
          map_smul' := by
            intro r m
            have hs : Pi.single i (r • m) =
                @SMul.smul _ _ (piRightModule Ri Mi).toSMul
                  (MulOpposite.op (Pi.single i r.unop)) (Pi.single i m) := by
              simpa only [Pi.single_eq_same, MulOpposite.op_unop] using
                piRightModule_single_smul Ri Mi (Pi.single i r.unop) i m
            calc
              f (Pi.single i (r • m)) i =
                  f (@SMul.smul _ _ (piRightModule Ri Mi).toSMul
                    (MulOpposite.op (Pi.single i r.unop)) (Pi.single i m)) i :=
                congrArg (fun y : ∀ i, Mi i => f y i) hs
              _ = (@SMul.smul _ _ (piRightModule Ri Ni).toSMul
                  (MulOpposite.op (Pi.single i r.unop)) (f (Pi.single i m))) i :=
                congrArg (fun y : ∀ i, Ni i => y i)
                  (f.map_smul (MulOpposite.op (Pi.single i r.unop)) (Pi.single i m))
              _ = r • f (Pi.single i m) i := by
                rw [piRightModule_smul_apply, Pi.single_eq_same, MulOpposite.op_unop] }
      invFun := fun φ =>
        { toFun := fun x i => φ i (x i)
          map_add' := by
            intro x y
            funext i
            exact (φ i).map_add (x i) (y i)
          map_smul' := by
            intro a x
            funext i
            calc
              φ i ((@SMul.smul _ _ (piRightModule Ri Mi).toSMul a x) i) =
                  φ i (MulOpposite.op (a.unop i) • x i) :=
                congrArg (φ i) (piRightModule_smul_apply_unop Ri Mi a x i)
              _ = MulOpposite.op (a.unop i) • φ i (x i) := (φ i).map_smul _ _
              _ = (@SMul.smul _ _ (piRightModule Ri Ni).toSMul a
                  (fun j => φ j (x j))) i :=
                (piRightModule_smul_apply_unop Ri Ni a (fun j => φ j (x j)) i).symm }
      left_inv := by
        intro f
        apply LinearMap.ext
        intro x
        funext i
        change f (Pi.single i (x i)) i = f x i
        calc
          f (Pi.single i (x i)) i =
              f (@SMul.smul _ _ (piRightModule Ri Mi).toSMul
                (MulOpposite.op (Pi.single i (1 : Ri i))) x) i :=
            congrArg (fun y : ∀ i, Mi i => f y i)
              (piRightModule_single_one_smul Ri Mi i x).symm
          _ = (@SMul.smul _ _ (piRightModule Ri Ni).toSMul
              (MulOpposite.op (Pi.single i (1 : Ri i))) (f x)) i :=
            congrArg (fun y : ∀ i, Ni i => y i)
              (f.map_smul (MulOpposite.op (Pi.single i (1 : Ri i))) x)
          _ = f x i := by
            rw [piRightModule_smul_apply, Pi.single_eq_same, MulOpposite.op_one, one_smul]
      right_inv := by
        intro φ
        funext i
        apply LinearMap.ext
        intro m
        change φ i ((Pi.single i m) i) = φ i m
        rw [Pi.single_eq_same]
      map_add' := by
        intro f g
        funext i
        apply LinearMap.ext
        intro m
        rfl }

end Pi
end Module
end
