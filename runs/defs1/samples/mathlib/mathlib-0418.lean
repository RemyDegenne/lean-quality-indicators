namespace BirdDet

open Function

variable {R : Type*} [CommRing R] {m n : ℕ}

variable (A : Matrix (Fin n) (Fin n) R) {p : ℕ}

/-- Bird's principal minor `f[α, α]`. -/
abbrev pminor (α : Fin p → Fin n) : R :=
  (A.submatrix α α).det

end BirdDet
