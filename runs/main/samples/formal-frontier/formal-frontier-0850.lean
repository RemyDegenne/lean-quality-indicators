@[expose] public section

open scoped TensorProduct

universe uR uM uN

namespace TensorProduct

theorem forall_dualDistrib_apply_eq_zero_iff_submodule
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    [Module.Projective R M]
    (I : Submodule R R) (t : M ⊗[R] I) :
    (∀ f : Module.Dual R M, ∀ g : Module.Dual R I,
      TensorProduct.dualDistrib R M I (f ⊗ₜ[R] g) t = 0) ↔ t = 0 := by
  exact forall_dualDistrib_apply_eq_zero_iff_of_eval_separatingLeft R M I
    (fun x hx => Subtype.ext (hx I.subtype)) t

end TensorProduct
end
