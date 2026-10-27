public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap

open CFSG.Blueprint.Fischer (K)

namespace AS35ZS

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem center_eq_bot_of_endo {L : Subgroup (V ≃ₗ[ZMod 2] V)} [Nontrivial V]
    (hcon : ∀ f : V →ₗ[ZMod 2] V, (∀ g ∈ L, ∀ v, g (f v) = f (g v)) → f ≠ 0 → f = 1) :
    Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hf := hcon _ (commute_of_mem_center hz) (fun h0 => by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have := LinearMap.congr_fun h0 v
    simp only [LinearEquiv.coe_coe, LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at this
    exact hv this)
  apply Subtype.ext
  ext v
  exact LinearMap.congr_fun hf v

end AS35ZS
end CFSG.LargeExtraspecial
end
