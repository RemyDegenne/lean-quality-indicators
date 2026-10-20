@[expose] public section

namespace RS

/-- The permutation fragment of `σ`: strand `k` joins incoming
label `k` to outgoing label `t + σ k`. -/
def permFragment {t : ℕ} (σ : Equiv.Perm (Fin t)) :
    Fragment (Fin (t + t)) where
  Flag := Fin t × Bool
  Vertex := Empty
  attach := fun f =>
    Sum.inr (if f.2 then
        ⟨t + (σ f.1).val, by have := (σ f.1).isLt; omega⟩
      else ⟨f.1.val, by have := f.1.isLt; omega⟩)
  pairing := fun f => (f.1, !f.2)
  pairing_invol := fun f => by simp
  pairing_ne := fun f h => by
    have hsnd := congrArg Prod.snd h
    simp at hsnd
  boundaryFlag := fun ℓ =>
    if h : ℓ.val < t then (⟨ℓ.val, h⟩, false)
    else (σ.symm ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩, true)
  attach_boundaryFlag := fun ℓ => by
    by_cases h : ℓ.val < t
    · rw [dite_eq_left h]
      exact congrArg Sum.inr (Fin.ext rfl)
    · rw [dite_eq_right h]
      refine congrArg Sum.inr (Fin.ext ?_)
      change t + (σ (σ.symm ⟨ℓ.val - t, by have := ℓ.isLt; omega⟩)).val =
        ℓ.val
      rw [Equiv.apply_symm_apply]
      change t + (ℓ.val - t) = ℓ.val
      have := ℓ.isLt
      omega
  eq_boundaryFlag := fun ℓ f h => by
    obtain ⟨a, b⟩ := f
    have hℓ := (Sum.inr.inj h).symm
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hℓ
      subst hℓ
      rw [dite_eq_left a.isLt]
    · simp only [ite_true] at hℓ
      subst hℓ
      rw [dite_eq_right (show ¬ t + (σ a).val < t by omega)]
      refine Prod.ext_iff.mpr ⟨?_, rfl⟩
      change a = σ.symm ⟨t + (σ a).val - t,
        by have := (σ a).isLt; omega⟩
      rw [show (⟨t + (σ a).val - t,
          by have := (σ a).isLt; omega⟩ : Fin t) = σ a from
        Fin.ext (by change t + (σ a).val - t = (σ a).val; omega)]
      exact (σ.symm_apply_apply a).symm
  circles := 0

end RS
end
