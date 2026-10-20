public section

open scoped TensorProduct

namespace TauCeti

universe u v

theorem isReduced_of_smooth
    (R : Type u) (A : Type v) [CommRing R] [IsReduced R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] : IsReduced A := by
  obtain ⟨R₀, A₀, _, _, _, _, _, _, _, _, ⟨e⟩⟩ :=
    Algebra.Smooth.exists_finiteType ℤ R A
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ _
  have : IsReduced (A₀ ⊗[R₀] R) := by
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro B hB
    have : Algebra.FiniteType R₀ B := ⟨B.fg_top.mpr hB⟩
    have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R₀ _
    have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
    have : IsReduced (B ⊗[R₀] A₀) := isReduced_of_smooth_of_isNoetherianRing B _
    exact isReduced_of_injective (Algebra.TensorProduct.comm R₀ A₀ B)
      (Algebra.TensorProduct.comm R₀ A₀ B).injective
  have : IsReduced (R ⊗[R₀] A₀) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R₀ R A₀)
      (Algebra.TensorProduct.comm R₀ R A₀).injective
  exact isReduced_of_injective e e.injective

end TauCeti
end
