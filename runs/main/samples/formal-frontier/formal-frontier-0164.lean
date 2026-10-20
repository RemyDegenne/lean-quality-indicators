@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X]

theorem existsUnique_hom_of_isOpenCover
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X)) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) :
    ∀ (G : Type v) [Group G]
      (φU : FundamentalGroup U (⟨p.1, p.2.1⟩ : U) →* G)
      (φV : FundamentalGroup V (⟨p.1, p.2.2⟩ : V) →* G),
      φU.comp (map (ContinuousMap.inclusion
          (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X)) Set.inter_subset_left) p) =
        φV.comp (map (ContinuousMap.inclusion
          (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X)) Set.inter_subset_right) p) →
      ∃! φ : FundamentalGroup X p.1 →* G,
        φ.comp (map (ContinuousMap.subtypeVal (U : Set X)) (⟨p.1, p.2.1⟩ : U)) = φU ∧
        φ.comp (map (ContinuousMap.subtypeVal (V : Set X)) (⟨p.1, p.2.2⟩ : V)) = φV := by
  classical
  intro G _ φU φV hcompat
  let pU : U := ⟨p.1, p.2.1⟩
  let pV : V := ⟨p.1, p.2.2⟩
  let kU : C(↑(U ⊓ V), U) := ContinuousMap.inclusion Set.inter_subset_left
  let kV : C(↑(U ⊓ V), V) := ContinuousMap.inclusion Set.inter_subset_right
  let jU := ContinuousMap.subtypeVal (U : Set X)
  let jV := ContinuousMap.subtypeVal (V : Set X)
  let cI := fun x : FundamentalGroupoid ↑(U ⊓ V) => intersectionArrow U V hI p x.as
  let cU := fun x : FundamentalGroupoid U => leftArrow U V hU hI p x.as
  let cV := fun x : FundamentalGroupoid V => rightArrow U V hV hI p x.as
  let TI := frameHomFunctor (FundamentalGroupoid.mk p) cI (φU.comp (map kU p))
  let TU := frameHomFunctor (FundamentalGroupoid.mk pU) cU φU
  let TV := frameHomFunctor (FundamentalGroupoid.mk pV) cV φV
  have hUI : FundamentalGroupoid.map kU ⋙ TU = TI :=
    frameHomFunctor_restrict (FundamentalGroupoid.map kU) (FundamentalGroupoid.mk p)
      cI cU (fun x => leftArrow_on_intersection U V hU hI p x.as)
      (φU.comp (map kU p)) φU rfl
  have hVI : FundamentalGroupoid.map kV ⋙ TV = TI :=
    frameHomFunctor_restrict (FundamentalGroupoid.map kV) (FundamentalGroupoid.mk p)
      cI cV (fun x => rightArrow_on_intersection U V hV hI p x.as)
      (φU.comp (map kU p)) φV hcompat.symm
  let W : Bool → Opens X := fun | false => U | true => V
  have hW : IsOpenCover W := by
    change (⨆ b, W b) = ⊤
    apply top_unique
    rw [← hcover]
    exact sup_le (le_iSup W false) (le_iSup W true)
  let F : ∀ b, FundamentalGroupoid (W b) ⥤ SingleObj G :=
    fun | false => TU | true => TV
  have hF : ∀ i j,
      (FundamentalGroupoid.openCoverDiagram W).map (Pairwise.Hom.left i j) ⋙ F i =
        (FundamentalGroupoid.openCoverDiagram W).map (Pairwise.Hom.right i j) ⋙ F j := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact hUI.trans hVI.symm
    · -- Reverse ordered overlaps use the same intersection, with swapped proofs.
      let swap : C(↑(V ⊓ U), ↑(U ⊓ V)) :=
        ContinuousMap.inclusion (fun _ hx => ⟨hx.2, hx.1⟩)
      -- These composites equal the native intersection inclusions as continuous maps.
      have hswapV : kV.comp swap =
          ((Opens.toTopCat (TopCat.of X)).map (Opens.infLELeft V U)).hom := by
        apply ContinuousMap.ext
        intro x
        rfl
      have hswapU : kU.comp swap =
          ((Opens.toTopCat (TopCat.of X)).map (Opens.infLERight V U)).hom := by
        apply ContinuousMap.ext
        intro x
        rfl
      have h := congrArg (fun T => FundamentalGroupoid.map swap ⋙ T)
        (hVI.trans hUI.symm)
      have hcomp : FundamentalGroupoid.map (kV.comp swap) ⋙ TV =
          FundamentalGroupoid.map (kU.comp swap) ⋙ TU := by
        simpa only [← CategoryTheory.Functor.assoc, ← FundamentalGroupoid.map_comp] using h
      rw [hswapV, hswapU] at hcomp
      exact hcomp
    · rfl
  let D := FundamentalGroupoid.descOfIsOpenCover hW F hF
  let φ : FundamentalGroup X p.1 →* G := vertexHom (FundamentalGroupoid.mk p.1) D
  have hφU : φ.comp (map jU pU) = φU := by
    calc
      φ.comp (map jU pU) = vertexHom (FundamentalGroupoid.mk pU)
          (FundamentalGroupoid.map jU ⋙ D) :=
        vertexHom_comp (FundamentalGroupoid.map jU) (FundamentalGroupoid.mk pU) D
      _ = vertexHom (FundamentalGroupoid.mk pU) TU :=
        congrArg (vertexHom (FundamentalGroupoid.mk pU))
          (FundamentalGroupoid.inclusion_comp_descOfIsOpenCover hW F hF false)
      _ = φU := vertexHom_frameHomFunctor (FundamentalGroupoid.mk pU) cU
        (leftArrow_unit U V hU hI p) φU
  have hφV : φ.comp (map jV pV) = φV := by
    calc
      φ.comp (map jV pV) = vertexHom (FundamentalGroupoid.mk pV)
          (FundamentalGroupoid.map jV ⋙ D) :=
        vertexHom_comp (FundamentalGroupoid.map jV) (FundamentalGroupoid.mk pV) D
      _ = vertexHom (FundamentalGroupoid.mk pV) TV :=
        congrArg (vertexHom (FundamentalGroupoid.mk pV))
          (FundamentalGroupoid.inclusion_comp_descOfIsOpenCover hW F hF true)
      _ = φV := vertexHom_frameHomFunctor (FundamentalGroupoid.mk pV) cV
        (rightArrow_unit U V hV hI p) φV
  refine ⟨φ, ⟨hφU, hφV⟩, ?_⟩
  intro ψ hψ
  let cX := fun x : FundamentalGroupoid X => globalArrow U V hcover hU hV hI p x.as
  let K := frameHomFunctor (FundamentalGroupoid.mk p.1) cX ψ
  have hK : ∀ b, FundamentalGroupoid.map (ContinuousMap.subtypeVal (W b : Set X)) ⋙ K =
      F b := by
    intro b
    cases b
    · exact frameHomFunctor_restrict (FundamentalGroupoid.map jU)
        (FundamentalGroupoid.mk pU) cU cX
        (fun x => globalArrow_left U V hcover hU hV hI p x.as) φU ψ hψ.1
    · exact frameHomFunctor_restrict (FundamentalGroupoid.map jV)
        (FundamentalGroupoid.mk pV) cV cX
        (fun x => globalArrow_right U V hcover hU hV hI p x.as) φV ψ hψ.2
  calc
    ψ = vertexHom (FundamentalGroupoid.mk p.1) K :=
      (vertexHom_frameHomFunctor (FundamentalGroupoid.mk p.1) cX
        (globalArrow_unit U V hcover hU hV hI p) ψ).symm
    _ = vertexHom (FundamentalGroupoid.mk p.1) D :=
      congrArg (vertexHom (FundamentalGroupoid.mk p.1))
        (FundamentalGroupoid.descOfIsOpenCover_unique hW F hF K hK)
    _ = φ := rfl

end FundamentalGroup
end
end
