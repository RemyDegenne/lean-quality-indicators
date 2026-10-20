namespace P2MW.S_HeckeEis_exists_basis_coeffH1par_int_complex

set_option autoImplicit false

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable section

namespace HeckeEis

namespace C2Aux

p2m_open

open MvPolynomial HeckeEis.RatAux HeckeEis.GenAux CongruenceSubgroup

open scoped MatrixGroups

variable (n N : ℕ) [NeZero N]

theorem moduleFinite_coeffParabolicCocycles :
    Module.Finite ℤ ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)) := by
  classical
  haveI := moduleFinite_binaryForm n
  obtain ⟨S, hS⟩ := Group.fg_def.mp (HeckeEis.ZQAux.instGroupFG_Gamma0 N)

  let ev : ↥(coeffParabolicCocycles ((binaryFormRepSL ℤ n).comp (Gamma0 N).subtype)) →ₗ[ℤ] (↥S → ↥(BinaryForm ℤ n)) :=
    { toFun := fun z g => z.1 g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : IsNoetherian ℤ (↥S → ↥(BinaryForm ℤ n)) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  refine Module.Finite.of_injective ev fun z z' h => Subtype.ext ?_
  exact coeffCocycles_eq_of_eqOn z.2.1 z'.2.1 hS fun g hg => congrFun h ⟨g, hg⟩

end C2Aux
end HeckeEis
end
end P2MW.S_HeckeEis_exists_basis_coeffH1par_int_complex
