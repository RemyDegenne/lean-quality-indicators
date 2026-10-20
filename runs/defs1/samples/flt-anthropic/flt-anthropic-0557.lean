namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace C5Body

p2m_open

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}

noncomputable def AffSES.transferLeft {A A' B C : OModulePresheaf π} (S : AffSES A B C)
    (u : AffHom A' A) (v : AffHom A A') (huv : ∀ U x, u.app U (v.app U x) = x) (hvu : ∀ U x, v.app U (u.app U x) = x) :
    AffSES A' B C where
  inc := S.inc.comp u
  proj := S.proj
  injective U := by
    intro x y hxy
    have := S.injective U (by simpa [AffHom.comp_app] using hxy)
    simpa [hvu] using congrArg (v.app U) this
  surjective := S.surjective
  exact U := by
    rw [← S.exact U]
    ext z
    simp only [LinearMap.mem_range, AffHom.comp_app]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨u.app U x, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨v.app U x, by rw [huv]⟩

end C5Body
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_filtration_affSES_of_forall_affineOpens_bijective_sum
