public section

namespace Matrix

variable {k Q : Type*} [Field k] [CommRing Q] [Algebra k Q]

/-- The `k`-subspace of rational vectors which the matrix `M` over `Q` scales by `s`. -/
def rationalEigenspace {n : Type*} [Fintype n] (M : Matrix n n Q) (s : Q) :
    Submodule k (n → k) :=
  LinearMap.ker (((M.mulVecLin - s • LinearMap.id).restrictScalars k) ∘ₗ
    LinearMap.compLeft (Algebra.linearMap k Q) n)

end Matrix
end
