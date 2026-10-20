public section

namespace TauCeti

namespace GridTwoStepDecomposition

variable {n : ℕ} {A B : GridState n → GridState n → Type*} {x z : GridState n}

theorem sum_decompositionsOf {M : Type*} [AddCommMonoid M]
    (first : ∀ u v : GridState n, Finset (A u v))
    (second : ∀ u v : GridState n, Finset (B u v))
    (w : ∀ y, A x y → B y z → M) :
    ∑ D ∈ decompositionsOf first second x z, w D.middle D.first D.second =
      ∑ y, ∑ P ∈ first x y, ∑ Q ∈ second y z, w y P Q := by
  classical
  simp [decompositionsOf, sigmaEquiv, Finset.sum_sigma']

end GridTwoStepDecomposition
end TauCeti
end
