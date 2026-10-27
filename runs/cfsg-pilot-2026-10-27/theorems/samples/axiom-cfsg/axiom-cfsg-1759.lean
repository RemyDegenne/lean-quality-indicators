public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open CFSG.RankThree.OrthogonalInvolutions Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem commSpace_eq_sup_span_pair {ω : V ≃ₗ[ZMod 2] V} (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace ω) = 4)
    {c : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0)
    {u₀ : V} (hu₀ : u₀ ∈ commSpace ω)
    (hu₀not : u₀ ∉ Submodule.span (ZMod 2) {c, ω c}) :
    commSpace ω = Submodule.span (ZMod 2) {c, ω c} ⊔
      Submodule.span (ZMod 2) {u₀, ω u₀} := by
  let ℓ := Submodule.span (ZMod 2) {c, ω c}
  let W := Submodule.span (ZMod 2) {u₀, ω u₀}
  have hℓU : ℓ ≤ commSpace ω := by
    rw [show ℓ = Submodule.span (ZMod 2) {c, ω c} from rfl, Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hc
    · exact AS35QCo.apply_mem_commSpace rfl hc
  have hWU : W ≤ commSpace ω := by
    rw [show W = Submodule.span (ZMod 2) {u₀, ω u₀} from rfl, Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hu₀
    · exact AS35QCo.apply_mem_commSpace rfl hu₀
  have hℓdim : finrank (ZMod 2) ℓ = 2 := finrank_span_apply_eq_two hω3 hc hc0
  have hu₀0 : u₀ ≠ 0 := by
    intro h
    exact hu₀not (by rw [h]; exact ℓ.zero_mem)
  have hWdim : finrank (ZMod 2) W = 2 := finrank_span_apply_eq_two hω3 hu₀ hu₀0
  have hℓWbot : ℓ ⊓ W = ⊥ := span_pair_inf_span_pair_eq_bot hω3 hc hc0 hu₀ hu₀not
  have hdimsup : finrank (ZMod 2) ↥(ℓ ⊔ W) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq ℓ W
    rw [hℓWbot, finrank_bot, add_zero, hℓdim, hWdim] at h
    exact h
  exact (Submodule.eq_of_le_of_finrank_eq (sup_le hℓU hWU) (by rw [hdimsup, h4])).symm

end CFSG.LargeExtraspecial
end
