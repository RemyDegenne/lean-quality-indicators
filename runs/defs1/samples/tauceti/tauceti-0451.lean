public section

namespace TauCeti

open Matrix

/-- The **split octonions** over `R`, as Zorn vector matrices: the element `⟨a, b, v, w⟩` is the
formal matrix `[[a, v], [w, b]]` with scalar diagonal and vector off-diagonal entries. -/
@[ext]
structure Octonion (R : Type*) where
  /-- The top-left, scalar entry of the vector matrix. -/
  a : R
  /-- The bottom-right, scalar entry of the vector matrix. -/
  b : R
  /-- The top-right, vector entry of the vector matrix. -/
  v : Fin 3 → R
  /-- The bottom-left, vector entry of the vector matrix. -/
  w : Fin 3 → R

end TauCeti
end
