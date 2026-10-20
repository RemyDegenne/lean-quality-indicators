public section

open CategoryTheory Set Topology

open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {U : ι → Set X}

namespace TauCeti

namespace FundamentalGroupoid

open _root_.FundamentalGroupoid

theorem functor_ext (hU : ∀ x, ∃ i, U i ∈ 𝓝 x) {D : Type*} [Category D]
    {F G : _root_.FundamentalGroupoid X ⥤ D}
    (h : ∀ i, map (ContinuousMap.subtypeVal (U i)) ⋙ F =
      map (ContinuousMap.subtypeVal (U i)) ⋙ G) :
    F = G := by
  have hobj : ∀ c, F.obj c = G.obj c := by
    rintro ⟨x⟩
    obtain ⟨i, hi⟩ := hU x
    have hx := CategoryTheory.Functor.congr_obj (h i) (mk ⟨x, mem_of_mem_nhds hi⟩)
    -- `(map f ⋙ F).obj (mk a)` is by definition `F.obj (mk (f a))`, since `map f` sends `mk a` to
    -- `mk (f a)`; here `f` is `Subtype.val`, so `f ⟨x, _⟩` is `x`.
    change F.obj (mk x) = G.obj (mk x) at hx
    exact hx
  -- The morphisms on which `F` and `G` agree form a subgroupoid.
  let S : Subgroupoid (_root_.FundamentalGroupoid X) :=
    { arrows := fun c d ↦ {f | F.map f = eqToHom (hobj c) ≫ G.map f ≫ eqToHom (hobj d).symm}
      inv := fun {c d f} hf ↦ by
        simp only [mem_ofPred_eq, Groupoid.inv_eq_inv, Functor.map_inv] at hf ⊢
        simp [hf]
      mul := fun {c d e f} hf {g} hg ↦ by
        simp only [mem_ofPred_eq, Functor.map_comp] at hf hg ⊢
        simp [hf, hg] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← iSup_im_map_subtypeVal_eq_top hU]
    refine iSup_le fun i ↦ ?_
    rw [Subgroupoid.im, Subgroupoid.map_le_iff_le_comap]
    rintro ⟨a, b, g⟩ -
    -- Membership in `Subgroupoid.comap φ S` is by definition membership of `φ.map g` in `S`, and
    -- `(φ ⋙ F).map g` is by definition `F.map (φ.map g)`.
    exact CategoryTheory.Functor.congr_hom (h i) g
  refine CategoryTheory.Functor.ext hobj fun c d f ↦ ?_
  have hf : f ∈ S.arrows c d := by
    rw [hS]
    trivial
  exact hf

end FundamentalGroupoid
end TauCeti
end
