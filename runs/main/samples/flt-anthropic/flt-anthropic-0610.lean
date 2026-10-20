namespace P2MW.S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel

open AutomorphicForm.CuspidalConstituent

open scoped Pointwise BigOperators

noncomputable section

namespace F4Iso

section KFDglue

variable (F : Type) [Field F] [NumberField F]

theorem rightTranslate_mem_iSup_archDualTypeSubmoduleAt (tys : ArchTypeFamily F)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (g : AdelicGL2 (𝓞 F) F → ℂ)
    (hg : ∀ v : InfinitePlace F, g ∈ ⨆ i : Fin (tys.card v), archDualTypeSubmoduleAt F v (tys.rep v i))
    (v : InfinitePlace F) :
    rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ ⨆ i : Fin (tys.card v), archDualTypeSubmoduleAt F v (tys.rep v i) := by
  refine Submodule.iSup_induction _
    (motive := fun f => rightTranslate F (rowIsometryInclAt₀ F w k) f ∈
      ⨆ i : Fin (tys.card v), archDualTypeSubmoduleAt F v (tys.rep v i)) (hg v) ?_ ?_ ?_
  · intro i f hfi
    refine le_iSup (fun j => archDualTypeSubmoduleAt F v (tys.rep v j)) i ?_
    by_cases hw : v = w
    · subst hw
      exact comp_mul_mem_typeSubmodule hfi k
    · exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
        commute_adelicArchGLInclAt_of_ne F (fun h => hw h.symm) _ _
  · show rightTranslate F _ 0 ∈ _
    rw [rightTranslate_zero]; exact Submodule.zero_mem _
  · intro a b ha hb
    show rightTranslate F _ (a + b) ∈ _
    rw [rightTranslate_add]; exact Submodule.add_mem _ ha hb

end KFDglue
end F4Iso
end
end P2MW.S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule
