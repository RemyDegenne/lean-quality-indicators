@[expose] public section

noncomputable section

open Set Filter TopologicalSpace Topology

open scoped ENNReal

variable {α : Type*} [TopologicalSpace α]

namespace EReal

variable {α : Type*} {u v : α → EReal}

variable {a b : EReal}

protected theorem Tendsto.mul {f : Filter α} {ma : α → EReal} {mb : α → EReal} {a b : EReal}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h₁ : a ≠ 0 ∨ b ≠ ⊥)
    (h₂ : a ≠ 0 ∨ b ≠ ⊤) (h₃ : a ≠ ⊥ ∨ b ≠ 0) (h₄ : a ≠ ⊤ ∨ b ≠ 0) :
    Tendsto (fun x ↦ ma x * mb x) f (𝓝 (a * b)) :=
  (EReal.tendsto_mul h₁ h₂ h₃ h₄).comp (hma.prodMk_nhds hmb)

end EReal
end
end
