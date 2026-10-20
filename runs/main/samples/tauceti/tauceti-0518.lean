public section

open CategoryTheory MulOpposite

open scoped TensorProduct

namespace TauCeti.GradedModuleCat

universe v vM vN uk uA uB uC

variable {k : Type uk} {A : Type uA} {B : Type uB}
  [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B)

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) : Module A M :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := A) (B := Bᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) : Module Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := A) (B := Bᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) : IsScalarTower k A M :=
  TauCeti.Algebra.TensorProduct.moduleLeftIsScalarTower (k := k) (A := A) (B := Bᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    IsScalarTower k Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRightIsScalarTower (k := k) (A := A) (B := Bᵐᵒᵖ) M

local instance (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    SMulCommClass A Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleSMulCommClass (k := k) (A := A) (B := Bᵐᵒᵖ) M

local instance leftGradedSMul [SetLike.GradedOne Δ.piece]
    (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    SetLike.GradedSMul Γ.piece M.grading.piece where
  smul_mem {p q} {a m} ha hm := by
    -- Express the restricted action through its defining inclusion into the envelope.
    change (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m ∈ M.grading.piece (p + q)
    have h1 : (1 : Bᵐᵒᵖ) ∈ Δ.opposite.piece 0 :=
      (Δ.mem_opposite_piece_iff 0 1).2 (SetLike.one_mem_graded Δ.piece)
    have h := Γ.tmul_mem_tensorProduct Δ.opposite ha h1
    rw [add_zero] at h
    exact SetLike.GradedSMul.smul_mem h hm

local instance rightGradedSMul [DirectSum.Decomposition Δ.piece]
    [SetLike.GradedOne Γ.piece] (M : GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) :
    SetLike.GradedSMul (InternalGrading.ofDecomposition Δ.piece).opposite.piece
      M.grading.piece where
  smul_mem {p q} {a m} ha hm := by
    -- Express the restricted right action through the other envelope inclusion.
    change ((1 : A) ⊗ₜ[k] a) • m ∈ M.grading.piece (p + q)
    rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at ha
    have ha' : a ∈ Δ.opposite.piece p := (Δ.mem_opposite_piece_iff p a).2 ha
    have h := Γ.tmul_mem_tensorProduct Δ.opposite (SetLike.one_mem_graded Γ.piece) ha'
    rw [zero_add] at h
    exact SetLike.GradedSMul.smul_mem h hm

section ModuleTensor

variable [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece]
  (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
  (N : GradedModuleCat.{vN} Δ.piece)

local notation "T" => BalancedTensorProduct k B M N

local instance : Module A T := BalancedTensorProduct.leftModule A

local instance : IsScalarTower k A T := BalancedTensorProduct.leftIsScalarTower A

local instance : SetLike.GradedSMul Γ.piece
    (BalancedTensorProduct.grading (𝒜 := Δ.piece) M.grading N.grading).piece :=
  BalancedTensorProduct.gradedSMul_left (𝒜 := Δ.piece) M.grading N.grading A Γ.piece

variable {M N}
  {M' M'' : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece}
  {N' N'' : GradedModuleCat.{vN} Δ.piece}

section Lift

variable {P : GradedModuleCat.{max vM vN} Γ.piece}
  (f : M →ₗ[k] N →ₗ[k] P)
  (hbalance : ∀ (b : B) (m : M) (n : N),
    f (((1 : A) ⊗ₜ[k] op b) • m) n = f m (b • n))
  (hleft : ∀ (a : A) (m : M) (n : N),
    f ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m) n = a • f m n)

variable (hdegree : ∀ {p q : ℤ} {m : M} {n : N},
  m ∈ M.grading.piece p → n ∈ N.grading.piece q → f m n ∈ P.grading.piece (p + q))

@[simp]
theorem bimoduleModuleTensorLift_tmul (m : M) (n : N) :
    (bimoduleModuleTensorLift Γ Δ f hbalance hleft hdegree).hom
      (bimoduleModuleTensorTmul Γ Δ M N m n) = f m n := by
  simp only [bimoduleModuleTensorLift, hom_ofHom, moduleTensorLiftLinear_tmul]

end Lift
end ModuleTensor
end TauCeti.GradedModuleCat
end
