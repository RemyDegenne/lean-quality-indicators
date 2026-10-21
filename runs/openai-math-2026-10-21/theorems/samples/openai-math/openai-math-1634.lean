namespace OAI

namespace Erdos3

open MvPolynomial

open scoped BigOperators Classical

theorem primePower_polynomial_character_decay
    {V : Type*} [Fintype V] {s : ℕ} (hs : 0 < s)
    {J : Fin s → Type*} [∀ j, Fintype (J j)]
    (p A a b e : ℕ) [NeZero p] (hp : p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (F : ∀ j, J j → MvPolynomial V (ZMod (p ^ A)))
    (hF : ∀ j i, (F j i).totalDegree ≤ j.val + 1)
    (hrank : ∀ (B : ℕ) (_ : b < B) (hBA : B ≤ A) (j : Fin s)
      (row : J j → ZMod (p ^ B)), (∃ i, IsUnit (row i)) →
      primePowerHomogeneousRankProbability p A B j.val hBA (F j) row ≤
        (p : ℝ) ^ (-C * B))
    (χ : AddChar (∀ j, J j → ZMod (p ^ A)) ℂ) (horder : orderOf χ = p ^ a)
    (r : V → ZMod (p ^ A)) :
    ‖𝔼 x : V → ZMod (p ^ A),
      χ (fun j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ ≤
      (p : ℝ) ^ (modularRankDecayExponent s C * modularRankChargeFactor s * (b + e)) *
        (p : ℝ) ^ (-modularRankDecayExponent s C * a) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hP : 0 ≤ modularRankDecayExponent s C := by
    dsimp [modularRankDecayExponent]
    positivity
  have hnorm : ‖𝔼 x : V → ZMod (p ^ A),
      χ (fun j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ ≤ 1 := by
    calc
      _ ≤ 𝔼 x : V → ZMod (p ^ A),
          ‖χ (fun j i => eval (fun v => r v + (p : ZMod (p ^ A)) ^ e * x v) (F j i))‖ :=
        RCLike.norm_expect_le (K := ℂ)
      _ = 1 := by simp only [χ.norm_apply, Fintype.expect_const]
  apply modular_local_decay_budget hpR hP (by positivity) (by positivity) hnorm
  intro hlargeR
  have hlarge : modularRankChargeFactor s * (b + e) < a := by
    exact_mod_cast hlargeR
  let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  obtain ⟨depth, hdepth, coeff, hcoord, hunit, hphase⟩ :=
    exists_primePower_tagged_ambient_rows hp χ
  obtain ⟨hmax, hattained⟩ := primePower_character_tag_depth_max hp χ depth hcoord horder
  have h := primePower_row_phase_decay_large hs p A a b e hp C hC F hF hrank
    depth hdepth hmax hattained coeff hunit hlarge r
  simpa only [hphase, Nat.cast_pow] using h

end Erdos3
end OAI
