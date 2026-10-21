namespace OAI

noncomputable section

namespace Tachikawa.OuterTensor

open CategoryTheory

open scoped TensorProduct ModuleCat.Algebra

variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma freeEquivLinear_action (m n : ℕ) (r : A ⊗[k] B) :
    (freeEquivLinear k A B m n).toLinearMap.comp
      (action k A B (freeObj A m) (freeObj B n) r) =
      (Algebra.lsmul k k (Fin m → Fin n → A ⊗[k] B) r).comp
      (freeEquivLinear k A B m n).toLinearMap := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    ext i j
    change (a * x i) ⊗ₜ[k] (b * y j) = (a ⊗ₜ[k] b) * (x i ⊗ₜ[k] y j)
    exact (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm
  | add r s hr hs =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hr, hs]

end Tachikawa.OuterTensor
end
end OAI
