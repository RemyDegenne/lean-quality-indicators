namespace OAI

namespace CriticalStrip

noncomputable section

open scoped BigOperators

open Set MeasureTheory Filter

theorem ordered_density_covariance_Ioo {N : ℕ} {R : ℝ} (hR : 0 < R)
    (w : Fin N → ℝ → ℝ) (hwc : ∀ i, ContinuousOn (w i) (Ioo 0 R))
    (hw : ∀ i x, x ∈ Ioo 0 R → 0 ≤ w i x) (f g : (Fin N → ℝ) → ℝ)
    (hfc : ContinuousOn f (coordinateBox (Fin N) (Ioo 0 R)))
    (hgc : ContinuousOn g (coordinateBox (Fin N) (Ioo 0 R)))
    (hfm : MonotoneOn f (coordinateBox (Fin N) (Ioo 0 R)))
    (hgm : MonotoneOn g (coordinateBox (Fin N) (Ioo 0 R)))
    (hh : IntegrableOn (rawProductDensity N w) (orderedChamber N (Ioo 0 R)))
    (hf : IntegrableOn (fun x => rawProductDensity N w x * f x) (orderedChamber N (Ioo 0 R)))
    (hg : IntegrableOn (fun x => rawProductDensity N w x * g x) (orderedChamber N (Ioo 0 R)))
    (hfg : IntegrableOn (fun x => rawProductDensity N w x * (f x * g x)) (orderedChamber N (Ioo 0 R))) :
    (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x * f x) *
      (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x * g x) ≤
    (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x) *
      (∫ x in orderedChamber N (Ioo 0 R), rawProductDensity N w x * (f x * g x)) := by
  apply ordered_density_covariance_exhaustion (fun n => R / (n + 3 : ℝ))
      (fun n => R - R / (n + 3 : ℝ)) (fun _ => by positivity) (fun n => ?_)
      (boundedWindow_mono hR.le) (boundedWindow_cover hR)
      w hwc hw f g hfc hgc hfm hgm hh hf hg hfg
  have hd : R / (n + 3 : ℝ) ≤ R / 2 :=
    div_le_div_of_nonneg_left hR.le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  linarith

end
end CriticalStrip
end OAI
