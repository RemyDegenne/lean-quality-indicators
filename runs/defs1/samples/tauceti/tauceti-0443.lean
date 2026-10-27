public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe uM

section Family

variable {B : Type*} [TopologicalSpace B] (β : PathComponentBasepoints B) (R : Type*) [CommRing R]

/-- The category of **DG local systems on a space with chosen basepoints**: families `(𝓕_c)`
indexed by the path components `c`, with `𝓕_c` a DG local system on `(B, b_c)`. -/
abbrev DGLocalSystemFamily : Type _ :=
  ∀ c : ZerothHomotopy B, DGLocalSystem.{uM} B (β.point c) R

end Family
end TauCeti
end
end
