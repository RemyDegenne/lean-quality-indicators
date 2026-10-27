public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem w172_exists_acting_prime {L : Subgroup Γ} (hsolv : Group.IsSolvable ↥L)
    (hO2 : pCoreOf 2 L = ⊥) {d : Γ} (hdL : d ∈ L) (hd : d * d = 1) (hd1 : d ≠ 1) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ x ∈ pCoreOf q L,
      d * x * d⁻¹ * x⁻¹ ∉ (⁅pCoreOf q L, pCoreOf q L⁆ : Subgroup Γ) := by
  classical
  have hO2' : CFSG.pCore 2 ↥L = ⊥ := by
    have h := hO2
    rw [CFSG.Open.pCoreOf] at h
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥L) (f := L.subtype)
      (Subgroup.subtype_injective L)).mp h
  let d' : ↥L := ⟨d, hdL⟩
  have hd' : d' * d' = 1 := Subtype.ext (by simpa [d'] using hd)
  have hd1' : d' ≠ 1 := fun h => hd1 (by simpa [d'] using congrArg Subtype.val h)
  obtain ⟨q, hqprime, hq2, x, hxP, hxnot⟩ :=
    w172_exists_acting_prime_group hsolv hO2' hd' hd1'
  refine ⟨q, hqprime, hq2, (x : Γ), ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem L.subtype hxP
  · intro hmem
    have hmem' : d * (x : Γ) * d⁻¹ * (x : Γ)⁻¹ ∈
        (⁅CFSG.pCore q ↥L, CFSG.pCore q ↥L⁆ : Subgroup ↥L).map L.subtype := by
      rw [Subgroup.map_commutator]
      simpa only [CFSG.Open.pCoreOf] using hmem
    have hmem'' : L.subtype (d' * x * d'⁻¹ * x⁻¹) ∈
        (⁅CFSG.pCore q ↥L, CFSG.pCore q ↥L⁆ : Subgroup ↥L).map L.subtype := hmem'
    exact hxnot ((Subgroup.mem_map_iff_mem (Subgroup.subtype_injective L)).mp hmem'')

end CFSG.LocalAnalysis.WeakClosure81
end
