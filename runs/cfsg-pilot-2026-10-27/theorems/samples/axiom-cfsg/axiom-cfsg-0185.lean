public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv Classical

namespace ThreeOne

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem odd_card_of_apply_eq {σ : Perm Ω} (hσ : ∀ x, σ (σ x) = x) {α : Ω} (hα : σ α = α)
    (hfix : ∀ x, x ≠ α → σ x ≠ x) : Odd (Fintype.card Ω) := by
  classical
  let f : Function.End Ω := ⇑σ
  have hf : f = ⇑σ := rfl
  have h2 : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext x
    change f (f x) = x
    rw [hf]
    exact hσ x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) h2
  have hset : Function.fixedPoints f = {α} := by
    ext x
    rw [Function.mem_fixedPoints_iff, Set.mem_singleton_iff]
    exact ⟨fun hx => by by_contra hne; exact hfix x hne (by simpa [f] using hx),
      fun hx => by rw [hx]; simpa [f] using hα⟩
  have hcard : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨α, by rw [Function.mem_fixedPoints_iff]; simpa [f] using hα⟩, fun y => ?_⟩
    apply Subtype.ext
    by_contra hne
    exact hfix y.1 hne (by
      have := Function.mem_fixedPoints_iff.mp y.2
      simpa [f] using this)
  rw [hcard] at hmod
  exact Nat.odd_iff.mpr (by simpa [Nat.ModEq] using hmod)

end ThreeOne
end CFSG.LocalAnalysis.WeakClosure81
end
