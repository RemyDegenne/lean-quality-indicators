public section

namespace LinearMap

variable {k A P₀ P₁ N N' N'' : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [AddCommGroup N'] [Module A N'] [Module k N'] [IsScalarTower k A N']
  [AddCommGroup N''] [Module A N''] [Module k N''] [IsScalarTower k A N'']

/-- Maps vanishing on the kernel of `f`, modulo maps extending across `f`. -/
abbrev HomCocycleQuotient (f : P₁ →ₗ[A] P₀) (N : Type*)
    [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N] :=
  ker ((ker f).subtype.lcomp k N) ⧸
    (range (f.lcomp k N)).comap (ker ((ker f).subtype.lcomp k N)).subtype

end LinearMap
end
