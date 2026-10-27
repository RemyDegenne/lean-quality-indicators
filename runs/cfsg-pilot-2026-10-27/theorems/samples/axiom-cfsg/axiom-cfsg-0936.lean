public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN28

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G101Hyp B Γ v₁ W X X₀)

theorem phi_eq_of {y : ↥X} {g : Module.Dual (ZMod 2) ↥W}
    (hg : ∀ w : ↥W, (y : V ≃ₗ[ZMod 2] V) (w : V) = (w : V) + g w • v₁) : phi h y = g := by
  ext w
  have h1 := phi_spec h y w
  rw [hg w] at h1
  exact eq_of_smul_v1 h (add_left_cancel h1).symm

end CFSG.Quasithin.SzN28
end
