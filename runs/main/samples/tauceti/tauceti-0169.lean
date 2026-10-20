public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

variable {H K L : FiniteTypeCommHopfAlgCat.{u, u} k}

@[simp]
theorem comapOfSurjective_solvableRadicalDefiningIdeal (e : H ≅ K) :
    (solvableRadicalDefiningIdeal K).comapOfSurjective (toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2 =
      solvableRadicalDefiningIdeal H := by
  let pulled := (solvableRadicalDefiningIdeal K).comapOfSurjective (toBialgHom e.hom)
    (ConcreteCategory.bijective_of_isIso e.hom).2
  have hpulled : HopfIdeal.IsSolvableRadicalCandidate H pulled :=
    (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal K).comapOfIso e
  apply le_antisymm
  · let sourcePulled := (solvableRadicalDefiningIdeal H).comapOfSurjective
      (toBialgHom e.inv) (ConcreteCategory.bijective_of_isIso e.inv).2
    have hsourcePulled : HopfIdeal.IsSolvableRadicalCandidate K sourcePulled :=
      (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).comapOfIso e.symm
    have hle : solvableRadicalDefiningIdeal K ≤ sourcePulled :=
      solvableRadicalDefiningIdeal_le K sourcePulled hsourcePulled
    intro x hx
    have hx' := hle (HopfIdeal.mem_comapOfSurjective.mp hx)
    have hx'' := HopfIdeal.mem_comapOfSurjective.mp hx'
    have hcancel : (toBialgHom e.inv) ((toBialgHom e.hom) x) = x := by
      have h := congrArg (fun f : H ⟶ H => toBialgHom f x) e.hom_inv_id
      simpa only [toBialgHom_comp, BialgHom.comp_apply, toBialgHom_id,
        BialgHom.coe_id, id_eq] using h
    rwa [hcancel] at hx''
  · exact solvableRadicalDefiningIdeal_le H pulled hpulled

end FiniteTypeCommHopfAlgCat
end
end TauCeti
end
