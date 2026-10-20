@[expose] public section

namespace QuadraticAlgebra

variable {K R : Type*} {a b : R}

section changeGenerator

variable [CommRing R]

theorem changeGenerator_injective (a b u k : R) {a' b' : R}
    (ha : a' = u ^ 2 * a - u * b * k - k ^ 2)
    (hb : b' = u * b + 2 * k) (hu : IsRegular u) :
    Function.Injective (changeGenerator a b u k ha hb) := by
  intro z w h
  have hy : z.im = w.im := hu.right <| by simpa using congr(im $h)
  exact QuadraticAlgebra.ext (by simpa [hy] using congr(re $h)) hy

end changeGenerator
end QuadraticAlgebra
end
