public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

namespace TopologicallySplitShortExact

variable (S : TopologicallySplitShortExact A B C)

section Connecting

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
lemma connectingQuotient_natural
    {A' B' C' : TopRep.{max v w} k G}
    (T : TopologicallySplitShortExact A' B' C') (F : S.Hom T)
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous A'] [TopRep.JointlyContinuous B'] :
    (crossedQuotientMap F.a).comp S.connectingQuotient =
      T.connectingQuotient.comp F.c.hom.mapInvariants := by
  ext c
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    connectingQuotient_apply, crossedQuotientMap_mk,
    connectingQuotient_apply]
  let c' : C'.ρ.invariants := F.c.hom.mapInvariants c
  apply (Submodule.Quotient.eq (principalCocycles A')).2
  change crossedMap F.a (S.connectingCrossed c) -
      T.connectingCrossed c' ∈ LinearMap.range (principalToCrossed A')
  let d : A' := T.retract (F.b (S.section_ c) - T.section_ c')
  have hd : T.p (F.b (S.section_ c) - T.section_ c') = 0 := by
    rw [map_sub T.p.hom, ← F.p_comm_apply, p_section_apply,
      p_section_apply]
    change F.c c - F.c c = 0
    exact sub_self _
  refine ⟨d, ?_⟩
  ext g
  apply T.injective_i
  change T.i (A'.ρ g d - d) =
    T.i (F.a (S.retract (B.ρ g (S.section_ c) - S.section_ c)) -
      T.retract (B'.ρ g (T.section_ c') - T.section_ c'))
  rw [map_sub T.i.hom, TopRep.hom_comm_apply,
    T.i_retract_of_p_eq_zero hd, map_sub T.i.hom,
    ← F.i_comm_apply,
    S.i_retract_of_p_eq_zero (S.p_section_defect_eq_zero c g),
    T.i_retract_of_p_eq_zero (T.p_section_defect_eq_zero c' g),
    map_sub F.b.hom, TopRep.hom_comm_apply]
  rw [map_sub]
  abel

end Connecting
end TopologicallySplitShortExact
end ContinuousCohomology
end
