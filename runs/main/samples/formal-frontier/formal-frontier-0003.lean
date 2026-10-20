public section

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits

namespace TopCat.Sheaf.AbelianForget

variable {Xj Xi Yj Yi : TopCat.{v}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem canonicalComponent_transition (p : Xj ⟶ Xi) (q : Yj ⟶ Yi)
    (fi : Xi ⟶ Yi) (fj : Xj ⟶ Yj) (h : p ≫ fi = fj ≫ q)
    {F : Xi.Sheaf AddCommGrpCat.{v}} {G : Xj.Sheaf AddCommGrpCat.{v}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} p).obj F ⟶ G) :
    canonicalComponent q ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).obj F) ≫
      (underlyingSheaf Yj).map
        (SquareTransition.transition AddCommGrpCat.{v} p q fi fj h a) =
      SquareTransition.transition (Type v) p q fi fj h
        (canonicalComponent p F ≫ (underlyingSheaf Xj).map a) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv _ _).injective
  calc
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv _ _)
        (canonicalComponent q ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).obj F) ≫
          (underlyingSheaf Yj).map
            (SquareTransition.transition AddCommGrpCat.{v} p q fi fj h a)) =
      (underlyingSheaf Yi).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} q).homEquiv _ _
          (SquareTransition.transition AddCommGrpCat.{v} p q fi fj h a)) :=
      canonicalComponent_mate_map q _ _ _
    _ = (underlyingSheaf Yi).map (SquareTransition.adjoint AddCommGrpCat.{v} q
        (SquareTransition.transition AddCommGrpCat.{v} p q fi fj h a)) := by
      rw [SquareTransition.adjoint_eq_homEquiv]
    _ = (underlyingSheaf Yi).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} fi).map
            (SquareTransition.adjoint AddCommGrpCat.{v} p a) ≫
          (SquareTransition.pushforwardSquareIso AddCommGrpCat.{v}
            p q fi fj h).hom.app G) := by
      rw [SquareTransition.adjoint_transition]
    _ = (TopCat.Sheaf.pushforward (Type v) fi).map
          ((underlyingSheaf Xi).map (SquareTransition.adjoint AddCommGrpCat.{v} p a)) ≫
        (SquareTransition.pushforwardSquareIso (Type v) p q fi fj h).hom.app
          ((underlyingSheaf Xj).obj G) := by
      rw [(underlyingSheaf Yi).map_comp,
        underlyingSheaf_pushforward_map, underlyingSheaf_pushforwardSquareIso_hom_app]
    _ = ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).homEquiv _ _)
        (SquareTransition.transition (Type v) p q fi fj h
          (canonicalComponent p F ≫ (underlyingSheaf Xj).map a)) := by
      rw [SquareTransition.adjoint_eq_homEquiv AddCommGrpCat.{v} p a]
      rw [← canonicalComponent_mate_map p F G a]
      rw [← SquareTransition.adjoint_eq_homEquiv (Type v) p,
        ← SquareTransition.adjoint_eq_homEquiv (Type v) q]
      exact (SquareTransition.adjoint_transition (Type v) p q fi fj h _).symm

end TopCat.Sheaf.AbelianForget
end
