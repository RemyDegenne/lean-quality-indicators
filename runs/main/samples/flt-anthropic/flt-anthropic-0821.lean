namespace P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_subst_eq_of_invariant_of_span_range_eq_of_free

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace QAClosing

open MvPowerSeries

noncomputable section Setup

variable {B : Type} [CommRing B]

variable {C : Type} [CommRing C] [Algebra B C] (π : A B →ₐ[B] C) (I : Ideal (A B))

variable {π I}

theorem isNilpotent_ybar (H : Hyp π I) (l : Fin 2) : IsNilpotent (ybar π l) := by
  obtain ⟨q, hq⟩ := H.map_X_pow
  exact ⟨q + 1, by rw [ybar, ← map_pow]; exact hq l⟩

end Setup
end QAClosing
end P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_subst_eq_of_invariant_of_span_range_eq_of_free
