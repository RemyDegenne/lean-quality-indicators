@[expose] public section

open scoped BigOperators Matrix

variable {n R 𝕜 : Type _} [Field 𝕜] [Fintype n]

local notation "M" n => Matrix n n 𝕜

local notation "Mₙ" n => Matrix n n R

lemma PiMat.center {R ι : Type*} [CommSemiring R] {n : ι → Type*}
    [∀ i, Fintype (n i)] :
    Set.center (PiMat R ι n) =
      { x | ∀ i, x i ∈ Set.center (Matrix (n i) (n i) R) } :=
  Matrix.pi_center

end
