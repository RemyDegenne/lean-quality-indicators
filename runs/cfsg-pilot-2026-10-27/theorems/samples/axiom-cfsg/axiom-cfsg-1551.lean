public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

open CFSG.Quasithin.JonesParshall

open scoped commutatorElement

variable {m : ℕ} {K : Type} [Field K]

theorem _root_.CFSG.Quasithin.F112R.isShort2_perfectCore_parP2 {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) :
    IsShort2 (perfectCore (parP2 h)) := by
  haveI := h.charP
  haveI := finite_hypSU h
  set L := perfectCore (parP2 h) with hLdef
  have hQ : blockQ L = radQ2 h := pCoreOf_perfectCore_parP2_eq' h
  have hU : blockU L = radQ2 h := blockU_perfectCore_parP2 h
  have hZ : blockZ L = ⊥ := blockZ_perfectCore_parP2 h
  have hQne : radQ2 h ≠ ⊥ :=
    fun e => zRad_ne_bot h (le_bot_iff.mp ((zRad_le_radQ2 h).trans (le_of_eq e)))
  have hperf : ⁅L, L⁆ = L := perfectCore_perfect (parP2 h)
  have hperfTop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf)
  refine ⟨?_, ?_, ⟨?_, ?_⟩, Or.inl (isQuasisimple_quot h), ?_, ?_⟩
  · intro N hN hN2
    haveI : N.Normal := hN
    by_contra hNtop
    haveI : Nontrivial (↥L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
    haveI : Group.IsNilpotent (↥L ⧸ N) := hN2.isNilpotent
    haveI : Group.IsSolvable (↥L ⧸ N) := inferInstance
    have hle : (⊤ : Subgroup ↥L) ≤ N :=
      Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M := N) (H := ⊤) hperfTop
    exact hNtop (top_le_iff.mp hle)
  · change L ⊓ Subgroup.centralizer (blockQ L : Set (hypSU h 2 0)) ≤ blockQ L
    rw [hQ]
    exact inf_centralizer_radQ2_le h
  · rw [hU, hQ]
    refine le_inf le_rfl fun x hx => ?_
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => radQ2_comm h hy hx
  · intro x hx
    rw [hU] at hx
    exact sq_eq_one_of_mem_radQ2 h hx
  · rw [hZ, hU]
    exact bot_lt_iff_ne_bot.mpr hQne
  · rw [hZ, hU]
    intro W _ hWU hWN
    rcases radQ2_irreducible h W hWU ((lev2Hom_range_le_perfectCore h).trans hWN) with h | h
    · exact Or.inl h
    · exact Or.inr h

end CFSG.Quasithin.H13.U4Par
end
