@[expose] public section

set_option warningAsError true

namespace AlgebraicGeometry.Proj

open CategoryTheory HomogeneousLocalization TopologicalSpace

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

variable {X : Scheme.{u}} (f g : A →+* Γ(X, ⊤)) (unit : Γ(X, ⊤)ˣ)

variable (hscale : ∀ d (a : A), a ∈ 𝒜 d →
  g a = (unit : Γ(X, ⊤)) ^ d * f a)

set_option backward.isDefEq.respectTransparency.types false in
lemma fromOfGlobalSectionsOfIsOpenCover_eq_of_unitScaling
    (hscale : ∀ n (a : A), a ∈ 𝒜 n →
      g a = (unit : Γ(X, ⊤)) ^ n * f a)
    (hcoverf : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (f ir.2.1)))
    (hcoverg : IsOpenCover (fun ir : Σ' d t, 0 < d ∧ t ∈ 𝒜 d ↦
      X.basicOpen (g ir.2.1))) :
    fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf =
      fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg := by
  let cover := openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf
  refine cover.hom_ext _ _ (fun ir ↦ ?_)
  obtain ⟨d, t, hd, ht⟩ := ir
  change (X.basicOpen (f t)).ι ≫ fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf =
    (X.basicOpen (f t)).ι ≫ fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg
  have hleft : (X.basicOpen (f t)).ι ≫
      fromOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf =
      toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫ (basicOpen 𝒜 t).ι := by
    change (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf).f ⟨d, t, hd, ht⟩ ≫ _ = _
    exact (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 f hcoverf).ι_glueMorphisms
      _ _ ⟨d, t, hd, ht⟩
  have hright : (X.basicOpen (g t)).ι ≫
      fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg =
      toBasicOpenOfGlobalSections 𝒜 g rfl hd ht ≫ (basicOpen 𝒜 t).ι := by
    change (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg).f ⟨d, t, hd, ht⟩ ≫ _ = _
    exact (openCoverOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg).ι_glueMorphisms
      _ _ ⟨d, t, hd, ht⟩
  have heq : X.basicOpen (f t) = X.basicOpen (g t) :=
    (basicOpen_eq_of_unitScaling 𝒜 f g unit hscale ht).symm
  calc
    _ = toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫ (basicOpen 𝒜 t).ι := hleft
    _ = ((X.isoOfEq heq).hom ≫ toBasicOpenOfGlobalSections 𝒜 g rfl hd ht) ≫
        (basicOpen 𝒜 t).ι := by
      rw [toBasicOpenOfGlobalSections_eq_of_unitScaling 𝒜 f g unit hscale hd ht]
    _ = (X.isoOfEq heq).hom ≫ (X.basicOpen (g t)).ι ≫
        fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg := by
      rw [Category.assoc, hright]
    _ = (X.basicOpen (f t)).ι ≫
        fromOfGlobalSectionsOfIsOpenCover 𝒜 g hcoverg := by
      rw [Scheme.isoOfEq_hom_ι_assoc]

end AlgebraicGeometry.Proj
end
