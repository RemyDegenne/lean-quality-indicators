public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise SemidirectProduct

variable {A V : Type*} [Group A] [Group V] {ρ : A →* MulAut V} {N : Subgroup V}

section Main

variable [Finite A] [Finite V] [Group.IsSolvable A]

variable [N.Normal]

theorem exists_mem_fixedPoints_range_mk_eq [Group.IsSolvable V] (hN : IsInvariantSubgroup ρ N)
    (hcop : (Nat.card A).Coprime (Nat.card V)) {x : V ⧸ N}
    (hx : ∀ b : A, hN.quotientAut b x = x) :
    ∃ v ∈ FixedPoints.subgroup ρ.range V, (v : V ⧸ N) = x := by
  have h : x ∈ (FixedPoints.subgroup ρ.range V).map (QuotientGroup.mk' N) := by
    rw [← fixedPoints_quotientAut_range hN hcop, mem_fixedPoints_range_iff]
    exact hx
  obtain ⟨v, hv, hvx⟩ := h
  exact ⟨v, hv, hvx⟩

end Main
end CFSG.FeitThompson
end
