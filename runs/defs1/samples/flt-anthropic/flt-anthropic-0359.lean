namespace P2MW.S_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow

set_option autoImplicit false

open scoped NNReal

namespace K2Tate

noncomputable section

attribute [-instance] Ideal.Quotient.semiNormedCommRing Ideal.Quotient.normedCommRing
  Ideal.Quotient.normedAlgebra Subalgebra.seminormedRing Subalgebra.normedRing
  Subalgebra.seminormedCommRing Subalgebra.normedCommRing SubalgebraClass.seminormedRing
  SubalgebraClass.normedRing

attribute [-instance] Submodule.Quotient.instSMul' Submodule.Quotient.mulAction'
  Submodule.Quotient.smulZeroClass' Submodule.Quotient.distribSMul'
  Submodule.Quotient.distribMulAction' Submodule.Quotient.module'

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] instCommRingO instCommRingT instCommSemiringT instRingT instSemiringT
  instAddCommGroupT instModuleT instAlgebraT

attribute [local instance] instZeroT instAddMonoidT instAddCommMonoidT

attribute [local instance] instDistribMulActionT instSMulZeroClassT instSMulT instSMulFinsuppT
  instCommRingV

scoped instance subsingleton_T_zero : Subsingleton (T p 0) :=
  Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.span_singleton_one])

namespace Tower

attribute [scoped instance] Tower.ring Tower.alg Tower.fin Tower.free

variable {p}

variable (D : Tower p)

scoped instance instModuleB (i : ℕ) : Module (T p i) (D.B i) := Algebra.toModule

scoped instance instAddCommGroupB (i : ℕ) : AddCommGroup (D.B i) := inferInstance

scoped instance instDistribMulActionB (i : ℕ) : DistribMulAction (T p i) (D.B i) := inferInstance

scoped instance instSMulB (i : ℕ) : SMul (T p i) (D.B i) := inferInstance

scoped instance instIsScalarTowerB (i : ℕ) : IsScalarTower (T p i) (T p i) (D.B i) := inferInstance

variable {ι : Type} [Fintype ι]

scoped instance : Fintype D.idx := Module.Free.ChooseBasisIndex.fintype _ _

scoped instance algLB : Algebra (L p) D.Bhat := D.toBhat.toAlgebra

scoped instance : Module.Free (L p) D.Bhat := Module.Free.of_basis D.basisE

scoped instance : Module.Finite (L p) D.Bhat := Module.Finite.of_basis D.basisE

scoped instance : Module.Flat (L p) D.Bhat := Module.Flat.of_projective

def pr (i : ℕ) : D.Bhat →+* D.B i := (Pi.evalRingHom (fun i => D.B i) i).comp D.Bhat.subtype

end Tower
end
end K2Tate
end P2MW.S_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow
