public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite

universe u

namespace PresheafOfModulesOfCommRing

variable {X : TopCat.{u}} (A : X.Presheaf CommRingCat.{u})
  (P Q : PresheafOfModulesOfCommRing.{u} A) (x : X)

private noncomputable local instance openNhdsInitiallySmall : InitiallySmall.{u} (OpenNhds x) :=
  initiallySmall_of_essentiallySmall _

private noncomputable local instance colimitCommRing : CommRing ((cA A x).pt) :=
  inferInstanceAs (CommRing (A.stalk x))

theorem stalkTensorEquiv_germ_tmul (V : Opens X) (hx : x ∈ V)
    (p : P.obj (op V)) (q : Q.obj (op V)) :
    stalkTensorEquiv A P Q x
        (TopCat.Presheaf.germ (P ⊗ Q).presheaf V x hx
          (show (P ⊗ Q).obj (op V) from p ⊗ₜ q)) =
      TopCat.Presheaf.germ P.presheaf V x hx p ⊗ₜ[A.stalk x]
        TopCat.Presheaf.germ Q.presheaf V x hx q := by
  let U : OpenNhds x := ⟨V, hx⟩
  change forwardNativeAdd A P Q x
      (nativeTensorGerm A P Q x (op U)
        (show (PDiag A (P ⊗ Q) x).obj (op U) from p ⊗ₜ q)) =
    nativeModuleGerm A x P (op U) p ⊗ₜ[A.stalk x]
      nativeModuleGerm A x Q (op U) q
  exact forwardNativeAdd_tmul A P Q x (op U) p q

end PresheafOfModulesOfCommRing
end
