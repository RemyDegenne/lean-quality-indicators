import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_of_span_range_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (u : Series B) (I : Ideal (MvPowerSeries (Fin 2) B)) (h : ℕ)
    (huI : Ideal.span (Set.range u) = I)
    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hrank : ∀ (κ : Type) [Field κ] (f : B →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ I.map (MvPowerSeries.map f)) = p ^ h) :
    FormalODModule.HasKernelOfDegree u (p ^ h) := by
  refine ⟨?_, ?_, fun κ _ f => ?_⟩
  · show Module.Finite B (MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range u))
    rw [huI]; exact hfin
  · show Module.Projective B (MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range u))
    rw [huI]; exact hproj
  · have hmap : Ideal.span (Set.range (u.map f)) = I.map (MvPowerSeries.map f) := by
      rw [← huI, Ideal.map_span, ← Set.range_comp]
      rfl
    show Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range (u.map f))) = p ^ h
    rw [hmap]
    exact hrank κ f
