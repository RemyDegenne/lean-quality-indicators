public section

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] {n : ℕ}

section Blocks

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}
  [hK : ∀ f : ↥(Fset s b F), Fact (∀ x ∈ Vf s b F f.1, aeval s f.1 *ᵥ x = 0)]

theorem fullW_act (H : PrimaryHyp τ s m F a b) (w : (f : Activ H) → ↥(Bl H f.1))
    {f : ↥(Fset s b F)} (h : IsAct H f) : fullW H w f = (w ⟨f, h⟩).1 := by
  unfold fullW
  rw [dif_pos h]

end Blocks
end CFSG.LieType.SemisimpleCentralizers.HeldUCD
end
