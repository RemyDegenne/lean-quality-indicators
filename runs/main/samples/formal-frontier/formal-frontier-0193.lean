set_option warningAsError true

namespace MvPolynomial

universe u v w z

variable {ι : Type u} {κ : Type v} {σ : Type w} {R : Type z} [CommSemiring R]

public section

theorem eval_aeval_pad_eq_zero_iff (j : ι ↪ κ) (f : ι → MvPolynomial σ R)
    (p : MvPolynomial κ R) (h : ∀ y : κ → R, eval y p = 0 ↔ y = 0)
    (x : σ → R) :
    eval x (aeval (Function.extend j f (fun _ => 0)) p) = 0 ↔
      ∀ i, eval x (f i) = 0 := by
  constructor
  · exact eval_aeval_pad_eq_zero_imp j f p (fun y => (h y).mp) x
  · intro hz
    rw [eval_aeval_pad]
    apply (h _).mpr
    funext k
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      simpa only [Pi.zero_apply, j.injective.extend_apply] using hz i
    · simp [Function.extend_apply' _ _ _ hk]

end
end MvPolynomial
