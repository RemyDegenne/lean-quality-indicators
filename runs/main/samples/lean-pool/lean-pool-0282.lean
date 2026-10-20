@[expose] public section

noncomputable section

open MeasureTheory

open Homogenization

open scoped ContDiff

namespace AVenhance.Infra.Section3

open AVenhance

theorem ChiMKCorrector.chiMK_spaceLap_three_active {β : ℝ} (I : Ingredients β)
    {m : ℕ} (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (hk : k % 4 = 3) :
    spaceLap (fun y => I.chiMK κ m k t y 0) x =
      -(4 * Real.pi ^ 2 / epsilon β I.Λ m ^ 2) *
        I.chiMK κ m k t x 0 := by
  let ε := epsilon β I.Λ m
  let freq := 2 * Real.pi / ε
  let A := -(4 * Real.pi ^ 2 * a β I.Λ m * I.corrTime κ m k t)
  have hε : ε ≠ 0 := ne_of_gt
    (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le)
  have hfreq (y : ℝ) : 2 * Real.pi * y / ε = freq * y := by
    dsimp [freq]
    field_simp [hε]
  have hgrad0 : (fun y => spaceGrad (fun z => I.chiMK κ m k t z 0) y 0) =
      fun _ => 0 := by
    funext y
    have h := chiMK_spaceGrad_three_all I κ k t y 0 hk hε
    simpa using h
  have hgrad1 : (fun y => spaceGrad (fun z => I.chiMK κ m k t z 0) y 1) =
      fun y => A * Real.sin (freq * y 1) := by
    funext y
    rw [chiMK_spaceGrad_three I κ k t y hk hε]
    rw [hfreq]
  have hchi : I.chiMK κ m k t x 0 =
      I.corrTime κ m k t *
        (2 * Real.pi * a β I.Λ m * ε * Real.cos (freq * x 1)) := by
    calc
      I.chiMK κ m k t x 0 =
          -(I.corrTime κ m k t * uShear β I.Λ m k x 0) := by
        simp [Ingredients.chiMK, Pi.smul_apply, smul_eq_mul]
      _ = I.corrTime κ m k t *
          (2 * Real.pi * a β I.Λ m * ε * Real.cos (freq * x 1)) := by
        have hu : uShear β I.Λ m k x 0 =
            -(2 * Real.pi * a β I.Λ m * ε *
              Real.cos (2 * Real.pi * x 1 / ε)) := by
          simp [uShear, hk, ε]
        rw [hu, hfreq]
        ring
  unfold spaceLap
  simp only [Fin.sum_univ_two]
  rw [hgrad0, hgrad1]
  rw [spaceGrad_sineCoordinate A freq 1 1 x]
  have hzeroGrad : spaceGrad (fun _ : Vec 2 => (0 : ℝ)) x 0 = 0 := by
    simp [AVenhance.spaceGrad]
  rw [hzeroGrad]
  simp only [ite_true]
  rw [hchi]
  dsimp [A, freq, ε]
  field_simp [hε]
  ring

end AVenhance.Infra.Section3
end
end
