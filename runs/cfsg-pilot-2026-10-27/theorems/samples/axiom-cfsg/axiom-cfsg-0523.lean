public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

namespace Lemma129

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)

section Weak

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

theorem barX_le_centralizer_of_le_centBar {p : ℕ} (hp : p.Prime) {N K S : Subgroup G}
    (hK : GLAPComponent p N K) (hSN : S ≤ N) (hS : S ≤ centBar p ⊤ K) :
    barX p N S ≤ Subgroup.centralizer (barX p N K : Set (↥N ⧸ GLAPPrimeCore p ↥N)) := by
  refine barX_le_centralizer fun s hs t ht _ _ => ?_
  have hsn := mem_normalizer_of_mem_centBar (hS hs)
  have h1 := (mem_centBar_top_iff hsn).1 (hS hs)
  have hmk : barAut p K ⟨s, hsn⟩ (QuotientGroup.mk ⟨t, ht⟩) = QuotientGroup.mk ⟨t, ht⟩ := by
    rw [h1]; rfl
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at hmk
  have hker := QuotientGroup.eq.1 hmk
  have hu : (s * t * s⁻¹)⁻¹ * t ∈ GLAPPrimeCoreOf p K := by
    refine ⟨_, hker, ?_⟩
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hconj := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p K ht) _).1
    ((GLAPPrimeCoreOf p K).inv_mem hu)
  have e : s * t * s⁻¹ * t⁻¹ = t * ((s * t * s⁻¹)⁻¹ * t)⁻¹ * t⁻¹ := by group
  rw [e]
  exact glaPPrimeCoreOf_le_of_isSubnormal hp hK.2.1 hconj

end Weak
end Lemma129
end CFSG.LocalAnalysis.GLTheoremB.MovingAround
end
