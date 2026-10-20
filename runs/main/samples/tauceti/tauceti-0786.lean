public section

namespace TauCeti.Module

@[simp]
theorem rankAtStalk_dual (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Module.rankAtStalk (R := R) (Module.Dual R M) = Module.rankAtStalk M := by
  ext p
  rw [Module.rankAtStalk_eq, Module.rankAtStalk_eq]
  exact (Dual.baseChangeEvaluationEquiv
    (R := R) (A := p.asIdeal.ResidueField) (M := M)).finrank_eq.trans
      Subspace.dual_finrank_eq

end TauCeti.Module
end
