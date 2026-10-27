public section

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit Matrix Subgroup

namespace CFSG.RankThree.S4Free.SzNatural

variable (n : ℕ)

theorem inf_centralizer_conj {T T' : Subgroup (Sz n)} (g : Sz n)
    (hT : ∀ h, h ∈ T' ↔ g⁻¹ * h * g ∈ T) (h : Sz n) :
    h ∈ T' ⊓ centralizer (T' : Set (Sz n)) ↔
      g⁻¹ * h * g ∈ T ⊓ centralizer (T : Set (Sz n)) := by
  rw [mem_inf, mem_inf, ← hT, mem_centralizer_iff, mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun hc t ht => ?_, fun hc t' ht' => ?_⟩
  · have h1 := hc (g * t * g⁻¹) ((hT _).mpr (by simpa [mul_assoc] using ht))
    have := congrArg (fun x => g⁻¹ * x * g) h1
    simpa [mul_assoc] using this
  · have h1 := hc _ ((hT t').mp ht')
    have := congrArg (fun x => g * x * g⁻¹) h1
    simpa [mul_assoc] using this

end CFSG.RankThree.S4Free.SzNatural
end
