public section

namespace CFSG.ComponentClassification.HarrisLit.T1.L413

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap

open scoped MatrixGroups

variable {K : Type*} [Field K]

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_eq_La_of_commute (h2 : (2 : K) ≠ 0) (fr fr' : Frame Q)
    (hperp : fr.perp ≤ fr'.span) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1)
    (hs : ∀ B, g * fr.swap.La B = fr.swap.La B * g) (hl' : ∀ A, g * fr'.La A = fr'.La A * g)
    (hs' : ∀ B, g * fr'.swap.La B = fr'.swap.La B * g) :
    ∃ M : SL(2, K), g = fr.La M := by
  have hi : g * fr.La (-1) = fr.La (-1) * g := by rw [← fr.La_swap_neg_one]; exact hs (-1)
  have hi' : g * fr'.La (-1) = fr'.La (-1) * g := hl' (-1)
  have hM := eq_mulLeft_of_commute_right (transport_mul_right h2 fr hs)
  have hdet : (fr.transport g 1).det = 1 := by
    have h := map_of_mem hgO (fr.incl 1)
    rwa [← Frame.incl_transport h2 hi, Frame.Q_incl, Frame.Q_incl, Matrix.det_one] at h
  have hc1 := eq_mulRight_of_commute_left (transport_mul_left h2 fr' hl')
  have hc2 := eq_mulLeft_of_commute_right (transport_mul_right h2 fr' hs')
  set c := fr'.transport g 1
  have hcc : c = c 0 0 • 1 := eq_smul_one_of_commute fun X => (hc1 X).symm.trans (hc2 X)
  have hdet' : c.det = 1 := by
    have h := map_of_mem hgO (fr'.incl 1)
    rwa [← Frame.incl_transport h2 hi', Frame.Q_incl, Frame.Q_incl, Matrix.det_one] at h
  have hcube : c * c * c = 1 := by
    have hg3' : g * g * g = 1 := by rw [← pow_three']; exact hg3
    have h := Frame.transport_mul (F := fr') (g := g * g) (h := g) h2 hi'
    rw [Frame.transport_mul (F := fr') (g := g) (h := g) h2 hi', hg3', Frame.transport_one] at h
    have h1 := LinearMap.congr_fun h 1
    rw [Module.End.one_apply, Module.End.mul_apply, Module.End.mul_apply, hc1 1, hc1 (1 * c),
      hc1 (1 * c * c), one_mul] at h1
    exact h1.symm
  have hc0 : c 0 0 = 1 := by
    have hsq : c 0 0 * c 0 0 = 1 := by
      rw [hcc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, pow_two] at hdet'
      exact hdet'
    have hcu : c 0 0 * c 0 0 * c 0 0 = 1 := by
      have h := congrFun (congrFun hcube 0) 0
      rw [hcc] at h
      simpa [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using h
    rw [hsq, one_mul] at hcu
    exact hcu
  have hfix : ∀ Y, g (fr'.incl Y) = fr'.incl Y := fun Y => by
    rw [← Frame.incl_transport h2 hi', hc1 Y, hcc, hc0, one_smul, Matrix.mul_one]
  refine ⟨⟨fr.transport g 1, hdet⟩, LinearEquiv.ext fun v => ?_⟩
  have hr : v - fr.incl (fr.coords v) ∈ fr.perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
  obtain ⟨Y, hY⟩ := hperp hr
  have hgr : g (v - fr.incl (fr.coords v)) = v - fr.incl (fr.coords v) := by
    rw [← hY]
    exact hfix Y
  have hv : v = fr.incl (fr.coords v) + (v - fr.incl (fr.coords v)) := by abel
  calc g v = g (fr.incl (fr.coords v)) + g (v - fr.incl (fr.coords v)) := by
        rw [← map_add, ← hv]
    _ = fr.incl (fr.transport g 1 * fr.coords v) + (v - fr.incl (fr.coords v)) := by
        rw [← Frame.incl_transport h2 hi, ← hM, hgr]
    _ = v + fr.incl (fr.transport g 1 * fr.coords v - fr.coords v) := by
        rw [map_sub]
        abel
    _ = fr.La ⟨fr.transport g 1, hdet⟩ v := (Frame.La_apply fr ⟨fr.transport g 1, hdet⟩ v).symm

end CFSG.ComponentClassification.HarrisLit.T1.L413
end
