public section

open CategoryTheory Limits ComposableArrows

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section SpectralObject

variable {ι : Type*} [Category* ι] (F : ι ⥤ CochainComplex C ℤ)

lemma spectralObject_δ_comp_spectralObjectHIsoCokernel_hom {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    [Mono (F.map f)] [Mono (F.map g)] (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (spectralObject F).δ f g n₀ n₁ h ≫ (spectralObjectHIsoCokernel F f n₁).hom =
      (spectralObjectHIsoCokernel F g n₀).hom ≫
        (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact (F.map f) (F.map g)).δ
          n₀ n₁ (by simp [← h]) := by
  rw [spectralObject_δ, spectralObjectHIsoCokernel_hom, spectralObjectHIsoCokernel_hom]
  let A := (spectralObjectHIso F g n₀).hom
  let S := (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
    (mappingConeCompTriangle (F.map f) (F.map g)).mor₃ n₀ n₁ (by lia)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (fun t => A ≫ t) ((Category.assoc _ _ _).trans
      (congrArg (fun t => S ≫ t) (Iso.inv_hom_id_assoc _ _)))).trans <|
    (congrArg (fun t => A ≫ t)
      (mappingCone.shiftMap_mappingConeCompTriangle_mor₃ (F.map f) (F.map g) n₀ n₁
        (by lia))).trans (Category.assoc _ _ _).symm

end SpectralObject
end CochainComplex
end
