public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopPair

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {S Y : TopCat.{w}} [T1Space S] {a : S ⟶ S} {p : S} {U : Set S}

theorem comp_singularHomologyMap_ofSubsetMap_eq_one_add_smul (ha : Function.Involutive a)
    (hp : a p ≠ p) (hapU : a p ∉ U) {y : Y} (f : S ⟶ Y) (hf : ∀ s, f (a s) = f s)
    (hfP : Set.MapsTo f ({p}ᶜ ∩ {a p}ᶜ) {y}ᶜ)
    (n : ℕ) (ε : ℤ) {M : A} (s : M ⟶ (ofSubset ({p}ᶜ ∩ {a p}ᶜ : Set S)).singularHomology R n)
    (hs : s ≫ TopPair.singularHomologyMap (ofSubsetMap a (B := {p}ᶜ ∩ {a p}ᶜ)
      (B' := {p}ᶜ ∩ {a p}ᶜ) fun x hx ↦
        ⟨fun h ↦ hx.2 ((ha x).symm.trans (congrArg a h)), fun h ↦ hx.1 (ha.injective h)⟩) R n =
          ε • s)
    (t : M ⟶ (interPair U {p}ᶜ).singularHomology R n)
    (ht : t ≫ TopPair.singularHomologyMap (excisionMap U {p}ᶜ) R n =
      s ≫ TopPair.singularHomologyMap (ofSubsetMap (𝟙 S) (by exact fun _ h ↦ h.1)) R n) :
    s ≫ TopPair.singularHomologyMap (ofSubsetMap f hfP) R n =
      (1 + ε) • (t ≫ TopPair.singularHomologyMap
        (ofSubsetMap (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ f)
          (B := (Subtype.val ⁻¹' {p}ᶜ : Set U)) (B' := {y}ᶜ) fun u hu ↦
            hfP ⟨hu, fun h ↦ hapU (Set.mem_singleton_iff.1 h ▸ u.2)⟩) R n) := by
  have haP : Set.MapsTo a ({p}ᶜ ∩ {a p}ᶜ) ({p}ᶜ ∩ {a p}ᶜ) := fun x hx ↦
    ⟨fun h ↦ hx.2 ((ha x).symm.trans (congrArg a h)), fun h ↦ hx.1 (ha.injective h)⟩
  have hfU : Set.MapsTo (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ f)
      (Subtype.val ⁻¹' {p}ᶜ : Set U) {y}ᶜ := fun u hu ↦
    hfP ⟨hu, fun h ↦ hapU (Set.mem_singleton_iff.1 h ▸ u.2)⟩
  have hcov : interior ({p}ᶜ : Set S) ∪ interior {a p}ᶜ = Set.univ := by
    rw [isOpen_compl_singleton.interior_eq, isOpen_compl_singleton.interior_eq,
      ← Set.compl_inter, Set.singleton_inter_eq_empty.2 (Set.mem_singleton_iff.not.2 hp.symm),
      Set.compl_empty]
  have hρa := ofSubsetMap_comp_ofSubsetMap_id_eq ha haP
  have haρ := ofSubsetMap_comp_ofSubsetMap_id_comp_complSingletonMap ha haP
  -- The class `s` is the sum of its contribution `t` near `p` and the image of `ε • t` under `a`.
  have hdec : s = t ≫ TopPair.singularHomologyMap (interPairToComplPair hapU) R n + ε • (t ≫
      TopPair.singularHomologyMap (interPairToComplPair hapU ≫ ofSubsetMap a haP) R n) := by
    refine singularHomology_inter_hom_ext R hcov (fun _ h ↦ h.1) (fun _ h ↦ h.2) n ?_ ?_
    · rw [Preadditive.add_comp, Linear.smul_comp, Category.assoc, Category.assoc,
        ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
        interPairToComplPair_comp_ofSubsetMap_id, ht, Category.assoc,
        singularHomologyMap_interPairToComplPair_comp_ofSubsetMap_comp_eq_zero R ha hapU haP,
        comp_zero, smul_zero, add_zero]
    · calc s ≫ TopPair.singularHomologyMap (ofSubsetMap (𝟙 S) (by exact fun _ h ↦ h.2)) R n
          = (s ≫ TopPair.singularHomologyMap (ofSubsetMap a haP) R n) ≫
              TopPair.singularHomologyMap (ofSubsetMap (𝟙 S) (by exact fun _ h ↦ h.1)) R n ≫
                TopPair.singularHomologyMap (complSingletonMap ha) R n := by
            rw [Category.assoc, ← TopPair.singularHomologyMap_comp,
              ← TopPair.singularHomologyMap_comp, haρ]
        _ = ε • (t ≫ TopPair.singularHomologyMap (excisionMap U {p}ᶜ) R n ≫
              TopPair.singularHomologyMap (complSingletonMap ha) R n) := by
            rw [hs, Linear.smul_comp, reassoc_of% ht]
        _ = (t ≫ TopPair.singularHomologyMap (interPairToComplPair hapU) R n +
              ε • (t ≫ TopPair.singularHomologyMap
                (interPairToComplPair hapU ≫ ofSubsetMap a haP) R n)) ≫
              TopPair.singularHomologyMap (ofSubsetMap (𝟙 S) (by exact fun _ h ↦ h.2)) R n := by
            conv_rhs => rw [Preadditive.add_comp, Linear.smul_comp, Category.assoc,
              Category.assoc, ← TopPair.singularHomologyMap_comp,
              ← TopPair.singularHomologyMap_comp,
              singularHomologyMap_interPairToComplPair_comp_eq_zero R hapU, comp_zero, zero_add,
              Category.assoc, hρa, ← Category.assoc, interPairToComplPair_comp_ofSubsetMap_id,
              TopPair.singularHomologyMap_comp]
  rw [hdec, Preadditive.add_comp, Linear.smul_comp, Category.assoc, Category.assoc,
    ← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_comp,
    interPairToComplPair_comp_ofSubsetMap hapU f hfP hfU, Category.assoc,
    interPairToComplPair_comp_ofSubsetMap_comp_ofSubsetMap hapU f hf haP hfP hfU, add_smul,
    one_smul]

end TopPair
end
end
