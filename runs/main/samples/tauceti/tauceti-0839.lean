public section

noncomputable section

open CategoryTheory

universe u v w v₁ v₂ v₃

namespace TauCeti

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R]

variable {X : TopCat.{v}}

@[simp]
theorem transport_refl (L : LocalCoefficientSystem.{u, v, w} R X) (x : X) :
    transport L (Path.Homotopic.Quotient.refl x) = LinearEquiv.refl R _ := by
  ext a
  rw [transport_apply, LinearEquiv.refl_apply]
  have h : Path.Homotopic.Quotient.refl x = 𝟙 (FundamentalGroupoid.mk x) :=
    (FundamentalGroupoid.id_eq_path_refl _).symm
  rw [h]
  exact L.map_id_apply _ a

end LocalCoefficientSystem
end TauCeti
end
end
