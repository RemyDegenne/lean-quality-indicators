public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0) (n : ℕ)

/-- The iterated relative Frobenius as a natural transformation from the identity of `Over S` to
the `n`-th Frobenius twist, that is, the base change functor `Over.pullback F_S^n` along the
`n`-fold absolute Frobenius of `S`. -/
noncomputable def iterateRelativeFrobeniusNatTrans :
    𝟭 (Over S) ⟶ Over.pullback (S.iterateFrobenius p hS n) where
  app X := Over.homMk (X.hom.iterateRelativeFrobenius p hS n)
    (Hom.iterateRelativeFrobenius_snd _ _ _ _)
  naturality X Y g := by
    ext
    exact (Hom.iterateRelativeFrobenius_naturality hS Y.hom g.left (Over.w g) n).symm

end AlgebraicGeometry.Scheme
end
