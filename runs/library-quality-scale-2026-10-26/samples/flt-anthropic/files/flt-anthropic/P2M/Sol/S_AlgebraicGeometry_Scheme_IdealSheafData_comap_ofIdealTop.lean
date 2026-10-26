import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (I : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f
      = Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  let ι := {p : X.affineOpens × Y.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : Y.Opens)}
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : ι => i.1.1) ?_ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, hxU⟩
  · rintro ⟨⟨U, V⟩, hUV⟩
    rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le _ f V U hUV, Scheme.IdealSheafData.ofIdealTop_ideal,
      Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    congr 1
    simp only [Scheme.Hom.appTop, Scheme.Hom.appLE]
    rw [← Category.assoc, f.naturality, Category.assoc, ← Functor.map_comp]
    rfl
