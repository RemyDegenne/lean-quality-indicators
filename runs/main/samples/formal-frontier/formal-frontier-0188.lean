@[expose] public section

set_option warningAsError true

noncomputable section

namespace AlgebraicGeometry.Proj

open CategoryTheory HomogeneousLocalization TopologicalSpace

universe u v w

variable {A B : Type u} {σ : Type v} {τ : Type w}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (ℬ : ℕ → τ) [GradedRing ℬ]

set_option backward.isDefEq.respectTransparency.types false in
theorem degreeScaledChartMap_preimage_basicOpen (f : A →+* B) (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ n a, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    (i : Σ m : PNat, 𝒜 m) {n : ℕ} (r : A) (hr : r ∈ 𝒜 n) (hn : 0 < n) :
    (degreeScaledChartMap 𝒜 ℬ f d hd hdeg i) ⁻¹ᵁ basicOpen 𝒜 r =
      (basicOpen ℬ (f (i.2 : A))).ι ⁻¹ᵁ basicOpen ℬ (f r) := by
  ext x
  obtain ⟨y, rfl⟩ := (basicOpenIsoSpec ℬ (f (i.2 : A))
    (hdeg i.1 (i.2 : A) i.2.2) (Nat.mul_pos hd i.1.2)).inv.homeomorph.surjective x
  have hh := congrArg (fun V : (Spec ↧(Away ℬ (f (i.2 : A)))).Opens => y ∈ V)
    (degreeScaledChartSpec_preimage_basicOpen 𝒜 ℬ f d hd hdeg i r hr hn)
  simpa only [Scheme.Hom.homeomorph_apply, SetLike.mem_coe,
    Scheme.Hom.mem_preimage,
    ← Scheme.Hom.comp_apply,
    degreeScaledChartMap, Category.assoc, Iso.inv_hom_id_assoc,
    Category.id_comp, basicOpenIsoSpec_inv_ι] using hh.to_iff

end AlgebraicGeometry.Proj
end
end
