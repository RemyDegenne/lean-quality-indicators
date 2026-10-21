namespace OAI

section

noncomputable section

namespace ExactFourier.Packing

theorem Word.continuous_weight {τ : Type} {D : τ→Type}
 [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α]
 (f : τ→GMatrix) (W : Word D A α) : Continuous (fun p : GMatrix→ℝ=>W.weight (p∘f)) := by
 induction W with
 | nil => exact continuous_const
 | cons s W ih =>
  cases s with
  | mono M h => exact ih
  | call t e => exact (continuous_apply (f t)).add ih

end ExactFourier.Packing
end
end
end OAI
