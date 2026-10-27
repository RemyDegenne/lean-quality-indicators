public section

universe groupUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem mem_conjugacyClassFinset
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (element selected : GroupType) : selected ∈ conjugacyClassFinset element ↔ IsConj element selected := by
  classical
  simp only [conjugacyClassFinset, Set.Finite.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_comm]

end CFSG.SignalizerFunctor.Helpers
end
