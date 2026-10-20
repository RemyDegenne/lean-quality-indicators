@[expose] public section

open Module

variable (K : Type*) [Field K]

namespace NumberField.canonicalEmbedding

/-- The canonical embedding of a number field `K` of degree `n` into `ℂ^n`. -/
def _root_.NumberField.canonicalEmbedding : K →+* ((K →+* ℂ) → ℂ) := RingHom.pi fun φ => φ

end NumberField.canonicalEmbedding
end
