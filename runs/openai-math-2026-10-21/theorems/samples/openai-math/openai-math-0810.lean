namespace OAI

section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CoherentDual

open Scheme.Modules

variable {A : CommRingCat.{0}} (M N : ModuleCat A)

lemma affineHomLinearMap_global (f : M ⟶ N) :
    affineHomLinearMap M N ((globalHomEquiv (Spec A).sheaf (tilde M) (tilde N)
      ⊤ isTerminalTop).symm ((tilde.functor A).map f)) = f.hom := by
  have h := (tilde.toTildeΓNatIso (R := A)).hom.naturality f
  change f ≫ (tilde.isoTop N).hom =
    (tilde.isoTop M).hom ≫ moduleSpecΓFunctor.map ((tilde.functor A).map f) at h
  have hh := congrArg (fun g => g ≫ (tilde.isoTop N).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh
  change (tilde.isoTop N).inv.hom.comp
    ((moduleSpecΓFunctor.map (globalHomEquiv _ _ _ _ _ _)).hom.comp
      (tilde.isoTop M).hom.hom) = f.hom
  have he := (globalHomEquiv (Spec A).sheaf (tilde M) (tilde N) ⊤ isTerminalTop).apply_symm_apply
    ((tilde.functor A).map f)
  rw [he]
  exact congrArg (fun g => g.hom) hh.symm

end CoherentDual
end
end
end OAI
