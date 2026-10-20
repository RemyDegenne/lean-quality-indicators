public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology Set TopCat Metric Module

open scoped RealInnerProductSpace

universe w u

namespace TauCeti

section General

variable {A : Type w} [Ring A] (M : ModuleCat.{w} A) {Y : Type w} [TopologicalSpace Y] [T2Space Y]
  (hY : ∀ (y : Y) (n : ℕ), IsZero ((reducedSingularHomologyFunctor M n).obj (of ↥({y}ᶜ : Set Y))))

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

include hY in
/-- **The homology of the complement of an embedded sphere.** Let `Y` be a Hausdorff space in which
the complement of every point has vanishing reduced homology, and let `h` be a continuous injection
into `Y` of the unit sphere of a real normed space of dimension `d`. Then
`H_redᵢ(Y ∖ h(Sᵈ⁻¹)) ≅ H_redᵢ₊d(Y)`, with coefficients in any module.

This is Hatcher, *Algebraic Topology*, Proposition 2B.1(b), in a general form. The isomorphism
depends on a chosen point of each sphere in the induction on the dimension, and is not a canonical
identification. -/
def reducedSingularHomologyComplRangeSphereIso {h : sphere (0 : E) 1 → Y} (hc : Continuous h)
    (hi : Function.Injective h) (i : ℕ) :
    (reducedSingularHomologyFunctor M i).obj (of ↥(range h)ᶜ) ≅
      (reducedSingularHomologyFunctor M (i + finrank ℝ E)).obj (of Y) :=
  -- Replace `E` by a Euclidean space of the same dimension, which has the same unit sphere.
  let e := sphereHomeomorphOfFinrankEq (E := E) (F := EuclideanSpace ℝ (Fin (finrank ℝ E)))
    finrank_euclideanSpace_fin.symm
  (reducedSingularHomologyFunctor M i).mapIso
      (isoOfHomeo (Homeomorph.setCongr (by rw [e.symm.surjective.range_comp h]))) ≪≫
    reducedSingularHomologyComplRangeSphereIsoAux M hY _ _ finrank_euclideanSpace_fin
      (h ∘ e.symm) (hc.comp e.symm.continuous) (hi.comp e.symm.injective) i

end General
end TauCeti
end
end
