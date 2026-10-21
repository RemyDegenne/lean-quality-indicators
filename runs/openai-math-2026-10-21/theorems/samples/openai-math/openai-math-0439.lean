namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Abelian

open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.ModuleBar

universe u

variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]

variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]

variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)

omit [HasDerivedCategory (ModuleCat R)] in
theorem tensorSecond_action (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N (n+3) ((tensorSecond k R S M N r hr).comp x (by omega)) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) (extClass3 k S N r hr) n
          (tensorKunneth k R S M N n x) := by
  unfold tensorKunneth
  simp only [LinearEquiv.trans_apply, ExternalTensor.selfExtScalarEquiv_comp,
    tensorSecond, LinearEquiv.apply_symm_apply]
  exact nativeTensorSecond_action k R S M N r hr n _

end ArExplicit.ModuleBar
end
end OAI
