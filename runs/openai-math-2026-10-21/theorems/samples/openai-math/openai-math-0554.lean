namespace OAI

section

noncomputable section

section

namespace MaximalSeshadri.Geometry

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {X Y : Scheme.{0}}

variable {K : Type} [Field K]

lemma structuralGlobal_finrank_iso (g : X ⟶ Spec (CommRingCat.of K))
    (f : Y ⟶ X) [IsIso f] :
    letI : Algebra K Γ(X,⊤) :=
      (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    letI : Algebra K Γ(Y,⊤) :=
      ((f ≫ g).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K Γ(X,⊤) = Module.finrank K Γ(Y,⊤) := by
  let : Algebra K Γ(X,⊤) :=
    (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : Algebra K Γ(Y,⊤) :=
    ((f ≫ g).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  have : IsIso f.appTop := inferInstanceAs (IsIso (Scheme.Γ.map f.op))
  exact (AlgEquiv.ofBijective (structuralGlobalMap g f)
    (ConcreteCategory.bijective_of_isIso f.appTop)).toLinearEquiv.finrank_eq

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
