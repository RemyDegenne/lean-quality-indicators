@[expose] public section

namespace LeanPool.DemazureProduct

namespace SlipFace

variable (sf : SlipFace)

infixl:70 " ⋆ " => star

infixl:70 " ◃ " => lres

infixr:70 " ▹ " => rres

/-- The set of boxes where the mixed difference `Δ` is equal to `1`,
as defined in the proof of *Proposition 4.3* (`prop:imageASP`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def Γ : Set (ℤ × ℤ) := {(a, b) | sf.Δ a b = 1}

end SlipFace
end LeanPool.DemazureProduct
end
