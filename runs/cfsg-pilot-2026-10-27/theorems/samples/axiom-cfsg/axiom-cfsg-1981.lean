public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

open CFSG.FeitThompson.Prep03

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

namespace OrientedCoreFamily

section CoherentBaseline

variable {G : Type u} [Group G] [Fintype G]

theorem commutator_sdiff_one_conj (M : Subgroup G) (t : ↥M) :
    (fun a => t⁻¹ * a * t) '' (((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1})
      = ((commutator ↥M : Subgroup ↥M) : Set ↥M) \ {1} := by
  have hN : (commutator ↥M).Normal := inferInstance
  have key : ∀ (x t : ↥M), t⁻¹ * x * t = 1 → x = 1 := by
    intro x t h
    have : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [this, h]; group
  refine Set.Subset.antisymm ?_ ?_
  · rintro a ⟨x, ⟨hxK, hx1⟩, rfl⟩
    refine ⟨by simpa using hN.conj_mem x hxK t⁻¹, fun hc => hx1 ?_⟩
    exact Set.mem_singleton_iff.2 (key x t (Set.mem_singleton_iff.1 hc))
  · intro a ⟨haK, ha1⟩
    refine ⟨t * a * t⁻¹, ⟨by simpa using hN.conj_mem a haK t, fun hc => ha1 ?_⟩, by group⟩
    refine Set.mem_singleton_iff.2 (key a t⁻¹ ?_)
    have h : t * a * t⁻¹ = 1 := Set.mem_singleton_iff.1 hc
    rw [show t⁻¹⁻¹ * a * t⁻¹ = t * a * t⁻¹ from by group, h]

end CoherentBaseline
end OrientedCoreFamily
end CFSG.FeitThompson
end
