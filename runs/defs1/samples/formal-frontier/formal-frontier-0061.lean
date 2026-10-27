public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

/-- Transport of global sections along identity base change. -/
noncomputable def globalSectionsBaseChangeIdentityEquiv
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) :
    letI := p.baseChangeGlobalSectionsAlgebra k k
    letI := p.globalSectionsAlgebra k
    Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap k k))), ⊤) ≃ₐ[k]
      Γ(X, ⊤) := by
  let _ := p.baseChangeGlobalSectionsAlgebra k k
  let _ := p.globalSectionsAlgebra k
  let e := baseChangeIdentityIso k p
  letI : IsIso e.inv := by dsimp [e]; infer_instance
  letI : IsIso (e.inv.app (⊤ : (pullback p
      (Spec.map (CommRingCat.ofHom (algebraMap k k)))).Opens)) := inferInstance
  exact
    { toRingEquiv := (asIso (e.inv.app (⊤ : (pullback p
          (Spec.map (CommRingCat.ofHom (algebraMap k k)))).Opens))).commRingCatIsoToRingEquiv
      commutes' r := by
        change (e.inv.appTop.hom.comp
            ((pullback.snd p
              (Spec.map (CommRingCat.ofHom (algebraMap k k)))).appTop.hom.comp
              (ΓSpecIso (.of k)).inv.hom)) r =
          (p.appTop.hom.comp (ΓSpecIso (.of k)).inv.hom) r
        congr 1
        rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Hom.comp_appTop,
          baseChangeIdentityIso_inv_snd] }

end Scheme
end AlgebraicGeometry
end
end
