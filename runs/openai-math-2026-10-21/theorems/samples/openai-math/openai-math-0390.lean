namespace OAI

noncomputable section

open Set

namespace CylinderCovering.AngularTableCover

open AngularTable

lemma table_admissible {cap : Cap} {p : Parameters}
    (hm : 0 < p.sectors) (hmesh : mesh p ≤ 32*p.tilt^2)
    (hτ : p.tilt ∈ Icc (0:ℝ) (1/4)) (hη : p.margin ∈ Ioc (0:ℝ) (1/480)) :
    AngularGeneral.Admissible p.tilt p.margin 32 (data cap p) := by
  obtain ⟨h0,h1,hinc,hbound,hwidth⟩ := AngularPartitionIdentities.partition_properties hm hmesh
  have ho : ∀ c : AngularOrdinaryCaps.CapChoice, AngularGeneral.Admissible p.tilt p.margin 32
      (AngularOrdinaryCaps.ordinaryData c p.sectors (node p.sectors) p.tilt p.margin) :=
    fun c => AngularOrdinaryCaps.ordinaryData_admissible c hm
      h0 h1 hinc hη.1.le (by norm_num : (0:ℝ) ≤ 32) hwidth
  cases cap with
  | midpoint => exact ho .midpoint
  | maximum => exact ho .maximum
  | radial => exact ho .radial
  | squared =>
    have hmax : max (32:ℝ) ((1/8+p.margin)^2) = 32 := by
      apply max_eq_left
      have hx : (1/8+p.margin)^2 ≤ 1 := by nlinarith [hη.1,hη.2]
      linarith
    dsimp only [data]
    simpa only [hmax] using AngularCaps.withSquaredCaps_admissible hη.1.le (ho .radial)
  | cartesian b =>
    have hc := CartesianCaps.cartesianData_admissible hm h0 h1 hinc hτ
      (show p.margin ∈ Ioc (0:ℝ) 1 from ⟨hη.1,by linarith [hη.2]⟩)
      (by norm_num : (0:ℝ) ≤ 32) hwidth
    norm_num only [max_eq_left (by norm_num : (12:ℝ) ≤ 32)] at hc
    exact hc

end CylinderCovering.AngularTableCover
end
end OAI
