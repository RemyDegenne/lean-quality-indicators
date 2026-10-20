namespace P2MW.S_AutomorphicForm_exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open IsDedekindDomain

open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

noncomputable section

namespace VInvAsm

open AutomorphicForm NumberField.AdelicLevel

variable {K : Type} [Field K] [NumberField K]

def rε (ε : InfinitePlace K → Bool) : (adelicMaximalCompact K) :=
  ⟨diagOne (signIdele ε), diagOne_mem_of_sign _ (signIdele_snd ε) (fun w => by
    rw [signIdele_fst]; split_ifs <;> simp)⟩

end VInvAsm
end
end P2MW.S_AutomorphicForm_exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule
