public section

set_option warningAsError true

open CategoryTheory TopologicalSpace

open CategoryTheory.Functor CategoryTheory.Adjunction CategoryTheory.NatTrans
  CategoryTheory.TwoSquare

noncomputable section

universe v

namespace TopCat.Sheaf.OpenBaseChange

/-- Direct-image base change along an open inverse-image square. -/
@[expose] def baseChangeIso {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y) :
    TopCat.Sheaf.pushforward (Type v) f ⋙
        TopCat.Sheaf.pullback (Type v) V.inclusion' ≅
      TopCat.Sheaf.pullback (Type v) ((Opens.map f).obj V).inclusion' ⋙
        TopCat.Sheaf.pushforward (Type v) (preimageMap f V) := by
  let hiV : Topology.IsOpenEmbedding V.inclusion' := V.isOpenEmbedding
  let _ := hiV.functor_isContinuous
  let U := (Opens.map f).obj V
  let hiU : Topology.IsOpenEmbedding U.inclusion' := U.isOpenEmbedding
  let _ := hiU.functor_isContinuous
  let openAdjV :
      hiV.sheafPullback (Type v) ⊣
        TopCat.Sheaf.pushforward (Type v) V.inclusion' :=
    hiV.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology ((Opens.toTopCat Y).obj V))
      (Opens.grothendieckTopology Y)
  let openAdjU :
      hiU.sheafPullback (Type v) ⊣
        TopCat.Sheaf.pushforward (Type v) U.inclusion' :=
    hiU.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      (Opens.grothendieckTopology X)
  let comparisonV := CategoryTheory.Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) V.inclusion') openAdjV
  let comparisonU := CategoryTheory.Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) U.inclusion') openAdjU
  let naive :
      TopCat.Sheaf.pushforward (Type v) f ⋙
          V.isOpenEmbedding.sheafPullback (Type v) ≅
        U.isOpenEmbedding.sheafPullback (Type v) ⋙
          TopCat.Sheaf.pushforward (Type v) (preimageMap f V) := by
    exact
      Functor.sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫
        Functor.sheafPushforwardContinuousIso (preimageOpensIso f V) _ _ _ ≪≫
        (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm
  exact
    Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type v) f)
        comparisonV ≪≫
      naive ≪≫
      (Functor.isoWhiskerRight comparisonU
        (TopCat.Sheaf.pushforward (Type v) (preimageMap f V))).symm

end TopCat.Sheaf.OpenBaseChange
end
end
