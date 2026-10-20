@[expose] public section

universe u

namespace Function

open Matrix (vecCons vecHead vecTail vecEmpty)

namespace FromTypes

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Constant `n`-ary function with value `t`. -/
def const : {n : ℕ} → (p : Fin n → Type u) → {τ : Type u} → (t : τ) → FromTypes p τ
  | 0,     _, _, t => t
  | n + 1, p, τ, t => fun _ => @const n (vecTail p) τ t

end FromTypes
end Function
end
