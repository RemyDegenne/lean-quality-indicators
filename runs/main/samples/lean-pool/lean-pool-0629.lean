@[expose] public section

open scoped TensorProduct

namespace CK

variable (k : Type*) [CommRing k]

variable [Algebra ℚ k]

omit [Algebra ℚ k] in
theorem _root_.CK.adamsAbHom_toLinearMap (n : ℕ) :
    (adamsAbHom k n).toLinearMap = adamsAb k n := by
  induction n with
  | zero =>
    apply LinearMap.ext; intro x
    change (Algebra.ofId k (Hab k)).comp (εab k) x = adamsAb k 0 x
    rw [AlgHom.comp_apply]
    change algebraMap k (Hab k) (εab k x) = adamsAb k 0 x
    rw [show adamsAb k 0
          = ((WithConv.toConv (LinearMap.id (R := k) (M := Hab k))) ^ 0).ofConv from rfl, pow_zero]
    change algebraMap k (Hab k) (εab k x) = (1 : WithConv (Hab k →ₗ[k] Hab k)) x
    rw [LinearMap.convOne_apply]
    rfl
  | succ m ih =>
    apply LinearMap.ext; intro x
    rw [adamsAb_succ_apply]
    have e1 : (Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)).toLinearMap
        = TensorProduct.map LinearMap.id (adamsAb k m) := by
      apply TensorProduct.ext'
      simp_all
    change Algebra.TensorProduct.lmul' k
        ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)) ((Δab k) x))
      = LinearMap.mul' k (Hab k)
          (TensorProduct.map LinearMap.id (adamsAb k m) ((Δab k).toLinearMap x))
    rw [show (Algebra.TensorProduct.lmul' k)
            ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)) ((Δab k) x))
          = LinearMap.mul' k (Hab k)
              ((Algebra.TensorProduct.map (AlgHom.id k (Hab k)) (adamsAbHom k m)).toLinearMap
                ((Δab k).toLinearMap x)) from rfl,
        e1]

end CK
end
