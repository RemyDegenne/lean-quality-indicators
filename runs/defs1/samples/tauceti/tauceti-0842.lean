public section

open CategoryTheory

open scoped Pointwise

universe u v w

namespace TauCeti

variable {k : Type u} {G : Type v} [Group G]

section Normal

variable {N : Subgroup G} [hN : N.Normal]

section NormalFDRep

variable [Ring k]

/-- Conjugation by `g` is an autoequivalence of `FDRep k N`, with inverse conjugation by `g⁻¹`:
Mathlib's `Action.resEquiv` for the automorphism `MulAut.conjNormal g⁻¹` of `N`.

The body is sealed, as for `conjNormalRepEquiv`; `conjNormalFDRepEquiv_functor` and
`conjNormalFDRepEquiv_inverse` are the interface identifying it with conjugation. -/
def conjNormalFDRepEquiv (g : G) : FDRep k N ≌ FDRep k N :=
  Action.resEquiv (FGModuleCat k) (MulAut.conjNormal g⁻¹ : MulAut N)

end NormalFDRep
end Normal
end TauCeti
end
