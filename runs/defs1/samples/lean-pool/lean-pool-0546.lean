@[expose] public section

namespace TMB

universe u v

open Multiset Finset

/-- Construct a banana from positive strand lengths, every strand oriented
from `0` to `1`. -/
def bananaOfLengths (g : ℕ) (length : Fin (g + 1) → ℕ)
    (hpos : ∀ α, 0 < length α) : Banana g where
  tail := fun _ => 0
  head := fun _ => 1
  length := length
  core_loopless := fun _ => by decide
  length_pos := hpos

end TMB
end
