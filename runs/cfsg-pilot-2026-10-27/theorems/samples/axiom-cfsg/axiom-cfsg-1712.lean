public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE

open CFSG.HardMathSupport.Curtis.UnitaryLevi (SM wordW wordW_append laF lbF wa wb QF4 QF4_comm
  QF4_cube QF4_pGroup nine_dvd_QF4 wa_mem_QF4 wb_mem_QF4 exists_conj_mem_QF4 mem_QF4 wa_cube
  wb_cube wa_wb_comm inv_eq_sq_of_cube inv_wa_wb inv_wa_wb_wb pair_nine card_centralizer_conj
  wordW_cube_of wordW_comm_of pair_comm_of_closure solve_int_fpf)

section Main

variable {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L] [IsAlgClosure F L]
  (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
  {w0 : WeylGroup Tag.F4} (hw0 : ∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u)

include hFr hw0 in
theorem boundTwA_core (h3 : 3 ∣ Nat.card F + 1) (lx ly : List (Fin Tag.F4.rank))
    (hx : wordW Tag.F4 lx ∈ QF4) (hy : wordW Tag.F4 ly ∈ QF4) (Φ Ψ : Matrix (Fin 4) (Fin 4) ℤ)
    (hid : 1 - ATw ly = (1 - ATw lx) * Φ + Ψ * (1 + ATw lx + ATw lx * ATw lx))
    (c₁ c₂ : Fin 4 → ℤ) (p₁ p₂ : Fin 4)
    (hf₁ : ∀ i : Fin 4, (3 : ℤ) ∣ ((ATw lx).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i : Fin 4, (3 : ℤ) ∣ ((ATw lx).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({wordW Tag.F4 lx, wordW Tag.F4 ly} :
      Set (WeylGroup Tag.F4))))
    (s : NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)
    (hs : NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s = wordW Tag.F4 lx)
    (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer
      ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr))) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  obtain ⟨ω, hω⟩ := exists_orderOf_three_μC (F := F) (L := L) h3
  obtain ⟨C, hCinj, hCsurj, hCmem⟩ := exists_nfix_lift Fr hFr w0 QF4 QF4_pGroup
    (fun q _ => Subgroup.mem_centralizer_singleton_iff.2 (weylGroup_mul_comm_of_neg hw0 q).symm)
  obtain ⟨gx, hgxC, hgx⟩ := hCsurj _ hx
  obtain ⟨gy, hgyC, hgy⟩ := hCsurj _ hy
  have hcomm : gy * gx = gx * gy := hCinj _ (mul_mem hgyC hgxC) _ (mul_mem hgxC hgyC) (by
    rw [map_mul, map_mul, hgx, hgy]; exact QF4_comm _ hy _ hx)
  have hgx3 : gx ^ 3 = 1 := hCinj _ (pow_mem hgxC 3) _ (one_mem C) (by
    rw [map_pow, map_one, hgx]; exact QF4_cube _ hx)
  refine caseA_ab (ιT Fr hFr w0 hw0) (NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)
    Atw (ιT_injective Fr hFr w0 hw0) (NFixToWeyl_eq_one_mem_range Fr hFr w0 hw0)
    (NFixToWeyl_ιT Fr hFr w0 hw0) (NFix_conj_ιT Fr hFr w0 hw0) _ _ s gx gy hs hgx hgy hcomm hgx3
    hs3 Φ Ψ ?_ ω hω c₁ c₂ p₁ p₂ ?_ ?_ h11 h12 h21 h22 hQ
  · rw [Atw_wordW, Atw_wordW]; exact hid
  · rw [Atw_wordW]; exact hf₁
  · rw [Atw_wordW]; exact hf₂

end Main
end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
end
