@[expose] public section

open MeasureTheory Homogenization

open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem twistie5ND_split (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) {t : ℝ} (hTt : ContDiff ℝ (⊤ : ℕ∞) (T t)) (x : Vec 2) :
    twistie5ND I hΦ m κm T t x =
      twistie5Nd I hΦ m κm T t x - vecDiv (twistie5Flux I hΦ m κm T t) x := by
  rw [twistie5ND_eq_defect]
  exact sd_split_odd (fun k => I.xiMK m k.1 t) (Infra.Section3.xiMK_odd_support_finite I hm t)
    (fun k => sdDefect5 I hΦ m κm k.1 t) (fun k => G I hΦ m T (lIdx β I.Λ m k.1) t)
    (fun k i j => sd_defect5_contDiff I hΦ m κm k.1 t i j)
    (fun k j => contDiff_pi.1 (tf_G_slice_contDiff I hΦ m T t (lIdx β I.Λ m k.1) hTt) j) x

end AVenhance.Infra.Section5.Contracts
end
end
