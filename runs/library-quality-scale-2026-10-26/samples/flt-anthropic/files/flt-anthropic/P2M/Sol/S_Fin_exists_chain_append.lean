import Mathlib
import P2M.Util
namespace P2MW.S_Fin_exists_chain_append

set_option autoImplicit false

namespace P2mWs11Concat

theorem aux {α : Type*} (S : α → α → Prop) {b c : α}
    (h₂ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = b ∧ f (Fin.last n) = c ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ)) :
    ∀ (n : ℕ) (a : α) (f : Fin (n + 1) → α), f 0 = a → f (Fin.last n) = b →
      (∀ i : Fin n, S (f i.castSucc) (f i.succ)) →
      ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = c ∧
        ∀ i : Fin n, S (f i.castSucc) (f i.succ) := by
  intro n
  induction n with
  | zero =>
    intro a f hf0 hfn _
    have hab : a = b := by rw [← hf0, ← hfn]; rfl
    subst hab
    exact h₂
  | succ n ih =>
    intro a f hf0 hfn hfS
    obtain ⟨m, g, hg0, hgm, hgS⟩ := ih (f 1) (fun i => f i.succ) rfl
      (by show f (Fin.last n).succ = b; rw [Fin.succ_last]; exact hfn)
      (fun i => by have := hfS i.succ; rwa [← Fin.succ_castSucc] at this)
    refine ⟨m + 1, Matrix.vecCons a g, rfl, ?_, ?_⟩
    · rw [← Fin.succ_last, Matrix.cons_val_succ]; exact hgm
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · have h01 := hfS 0
        rw [Fin.castSucc_zero, hf0] at h01
        show S (Matrix.vecCons a g (0 : Fin (m + 1)).castSucc) (Matrix.vecCons a g (0 : Fin (m + 1)).succ)
        rw [Fin.castSucc_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, hg0]
        exact h01
      · show S (Matrix.vecCons a g j.succ.castSucc) (Matrix.vecCons a g j.succ.succ)
        rw [← Fin.succ_castSucc, Matrix.cons_val_succ, Matrix.cons_val_succ]
        exact hgS j

end P2mWs11Concat

theorem solution {α : Type*} (S : α → α → Prop) {a b c : α}
    (h₁ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = b ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ))
    (h₂ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = b ∧ f (Fin.last n) = c ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ)) :
    ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = c ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ) := by
  obtain ⟨n, f, hf0, hfn, hfS⟩ := h₁
  exact P2mWs11Concat.aux S h₂ n a f hf0 hfn hfS
