public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1

open scoped commutatorElement

theorem exists_pComponent_of_quotient_component {X : Type} [Group X] [Finite X]
    {Kh : Subgroup (X ⧸ pPrimeCore 2 X)} (hK : IsComponent Kh) :
    ∃ L : Subgroup X, IsPComponent 2 L ∧ L.map (QuotientGroup.mk' (pPrimeCore 2 X)) = Kh := by
  let π : X →* X ⧸ pPrimeCore 2 X := QuotientGroup.mk' (pPrimeCore 2 X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let S : Set (Subgroup X) := {J | J.IsSubnormal ∧ J.map π = Kh}
  have hS : S.Nonempty :=
    ⟨Kh.comap π, isSubnormal_comap π hK.2, by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective _ hπ, top_inf_eq]⟩
  obtain ⟨L, hLS, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup X)) S hS
  exact ⟨L, ⟨Kh, hK, hLS.1, hLS.2, fun J hJ hJs hJm => hmin J ⟨hJs, hJm⟩ hJ⟩, hLS.2⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1
end
