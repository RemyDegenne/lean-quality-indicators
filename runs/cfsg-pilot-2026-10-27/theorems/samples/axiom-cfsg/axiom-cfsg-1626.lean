public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small

open scoped symmDiff

variable {N : ℕ}

theorem bil_not_natWt_add_spin {σ c b₀ : ZMod N} {e : ℕ} (hb₀ : b₀ ≠ 0) {a b : Fin 4 → ZMod N}
    (ha : IsNatWt σ a) (hb : IsSpinWt b₀ e b) : ¬ IsNatWt c (a + b) := by
  intro h
  obtain ⟨k, u, hu, rfl⟩ := bil_natWt_eq ha
  obtain ⟨i, v, hv, hsum⟩ := bil_natWt_eq h
  obtain ⟨j, hji, hjk⟩ := bil_exists_ne_ne i k
  have h1 := congrFun hsum j
  simp only [Pi.add_apply, Pi.single_apply, if_neg hji, if_neg hjk, zero_add] at h1
  rcases hb.1 j with h2 | h2
  · exact hb₀ (h2 ▸ h1)
  · exact hb₀ (neg_eq_zero.mp (h2 ▸ h1))

end CFSG.RankThree.GF2n.Stroth80.Tri
end
