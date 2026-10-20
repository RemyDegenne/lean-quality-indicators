@[expose] public section

universe uι uR uS uM uN

namespace KTheory

namespace K0

section Pi

variable {ι : Type uι} (Ri : ι → Type uR) [∀ i, Ring (Ri i)]

/-- Coordinate scalar extension gives an additive equivalence from K₀ of a
finite product ring to the product of the factor K₀ groups. -/
noncomputable def piEquiv [Finite ι] : K0 (∀ i, Ri i) ≃+ (∀ i, K0 (Ri i)) :=
  AddEquiv.ofBijective
    (piMap Ri) (by
      let q (i : ι) : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (ProjectiveClass (Ri i))) (K0 (Ri i)) :=
        AddLocalization.addMonoidOf (⊤ : AddSubmonoid (ProjectiveClass (Ri i)))
      let qPi : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (∀ i, ProjectiveClass (Ri i))) (∀ i, K0 (Ri i)) :=
        { toAddHom := (AddMonoidHom.piMap (fun i ↦ ofClass (Ri i))).toAddHom
          isLocalizationMap := by
            have hfun :
                (AddMonoidHom.piMap (fun i ↦ ofClass (Ri i))).toAddHom.toFun =
                  Pi.map (fun i ↦ (q i).toFun) := by
              funext a i
              exact AddMonoidHom.piMap_apply (fun i ↦ ofClass (Ri i)) a i
            rw [hfun]
            simpa only [AddSubmonoid.pi_top] using
              (AddSubmonoid.IsLocalizationMap.pi
                (fun i ↦ (⊤ : AddSubmonoid (ProjectiveClass (Ri i))))
                (fun i ↦ (q i).isLocalizationMap)) }
      have htop :
          (⊤ : AddSubmonoid (ProjectiveClass (∀ i, Ri i))).map
              (ProjectiveClass.piEquiv Ri).toAddMonoidHom =
            (⊤ : AddSubmonoid (∀ i, ProjectiveClass (Ri i))) := by
        apply le_antisymm le_top
        intro a _
        exact AddSubmonoid.mem_map.mpr
          ⟨(ProjectiveClass.piEquiv Ri).symm a, AddSubmonoid.mem_top _,
            (ProjectiveClass.piEquiv Ri).apply_symm_apply a⟩
      let qA : AddSubmonoid.LocalizationMap
          (⊤ : AddSubmonoid (ProjectiveClass (∀ i, Ri i))) (∀ i, K0 (Ri i)) :=
        qPi.ofAddEquivOfDom (k := ProjectiveClass.piEquiv Ri) htop
      let e : K0 (∀ i, Ri i) ≃+ (∀ i, K0 (Ri i)) :=
        AddLocalization.addEquivOfQuotient qA
      have hforward : e.toAddMonoidHom = piMap Ri := by
        apply hom_ext_ofClass (∀ i, Ri i)
        intro a
        change e (ofClass (∀ i, Ri i) a) =
          fun i ↦ map (Pi.evalRingHom Ri i) (ofClass (∀ i, Ri i) a)
        change AddLocalization.addEquivOfQuotient qA
          ((AddLocalization.addMonoidOf
            (⊤ : AddSubmonoid (ProjectiveClass (∀ i, Ri i)))) a) = _
        rw [AddLocalization.addEquivOfQuotient_addMonoidOf]
        funext i
        change ofClass (Ri i) (ProjectiveClass.map (Pi.evalRingHom Ri i) a) = _
        exact (map_ofClass (Pi.evalRingHom Ri i) a).symm
      rw [← hforward]
      exact e.bijective)

end Pi
end K0
end KTheory
end
