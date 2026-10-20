@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

variable (R : Type u) [Ring R]

namespace FiniteProjective

section Representatives

variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

variable (Q : Type w) [AddCommGroup Q] [Module R Q]
  [Module.Finite R Q] [Module.Projective R Q]

/-- Representation is compatible with binary direct sum, modeled by the
product of the two module carriers. -/
noncomputable def reprProdIso :
    repr R (P × Q) ≅ of R (repr R P × repr R Q) :=
  isoOfLinearEquiv ((reprEquiv R (P × Q)).trans
    ((reprEquiv R P).symm.prodCongr (reprEquiv R Q).symm))

end Representatives
end FiniteProjective
end ModuleCat
end
