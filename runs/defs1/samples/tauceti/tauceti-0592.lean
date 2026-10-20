public section

open CategoryTheory

namespace TauCeti

namespace SpecialLinear

universe u w

variable (n : ℕ)

variable {k : Type u} [Field k]

/-- The pointwise center quotient of `SLₙ` is naturally isomorphic to the presheaf with values
Mathlib's projective special linear groups. -/
noncomputable def centerPointwiseQuotientNatIsoPSL (hn : 0 < n) :
    CommHopfAlgCat.pointwiseQuotientFunctor
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) ≅
      pslPointsFunctor n :=
  NatIso.ofComponents
    (fun A =>
      eqToIso (CommHopfAlgCat.pointwiseQuotientFunctor_obj
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
        (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A) ≪≫
      centerPointwiseQuotientIsoPSL n hn A ≪≫
      eqToIso (pslPointsFunctor_obj n A).symm) (by
      intro A B φ
      have hprojective :
          eqToHom (pslPointsFunctor_obj n A).symm ≫
              (pslPointsFunctor n).map φ =
            GrpCat.ofHom (projectiveMap n φ.hom.toRingHom) ≫
              eqToHom (pslPointsFunctor_obj n B).symm := by
        rw [pslPointsFunctor_map]
        simp
      simpa only [Iso.trans_hom, eqToIso.hom,
        CommHopfAlgCat.pointwiseQuotientFunctor_map, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
        hprojective] using
        congrArg (fun z =>
          eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj
            (coordinateHopfAlgebra k n)
            (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))
            (CommHopfAlgCat.isNormal_centerDefiningIdeal (coordinateHopfAlgebra k n)) A) ≫
              z ≫ eqToHom (pslPointsFunctor_obj n B).symm)
          (centerPointwiseQuotientIsoPSL_hom_naturality n hn φ))

end SpecialLinear
end TauCeti
end
