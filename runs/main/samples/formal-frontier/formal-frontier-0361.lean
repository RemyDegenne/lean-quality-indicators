@[expose] public section

universe uR uS uT uM

open CategoryTheory CategoryTheory.Limits

open ModuleCat (FiniteProjective)

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

namespace K0

theorem map_bijective_of_projectiveClass_map_bijective (f : R →+* S)
    (hf : Function.Bijective (ProjectiveClass.map f)) :
    Function.Bijective (map f) := by
  let e : ProjectiveClass R ≃+ ProjectiveClass S :=
    AddEquiv.ofBijective (ProjectiveClass.map f) hf
  have he : (⊤ : AddSubmonoid (ProjectiveClass R)).map e.toAddMonoidHom =
      (⊤ : AddSubmonoid (ProjectiveClass S)) := by
    rw [← AddMonoidHom.mrange_eq_map]
    exact AddMonoidHom.mrange_eq_top_of_surjective _ e.surjective
  let E : K0 R ≃+ K0 S :=
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R))).addEquivOfAddEquiv
      (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass S)))
      (j := e) he
  have hE : E.toAddMonoidHom = map f := by
    apply hom_ext_ofClass R
    intro a
    rw [map_ofClass]
    exact AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq
      (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass R)))
      (k := AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass S)))
      (j := e) he a
  rw [← hE]
  exact E.bijective

end K0
end KTheory
end
