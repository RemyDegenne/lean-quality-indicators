namespace P2MW.S_CerednikDrinfeld_FormalODModule_isIsogenyOfHeight_four_of_map_eq_sub_verschiebungInt_edgeRingCharP

attribute [-instance] instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup

set_option autoImplicit false

universe u

open MvFormalGroup MvFormalGroup.CartierModule

namespace B29CMU

variable {p : ℕ} [hp : Fact p.Prime]

section generic

variable {R : Type u} [CommRing R] {d d' : ℕ} {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}
  [Φ.IsComm] [Φ'.IsComm]

local notation "VV" => (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ)

local notation "VV'" => (verschiebungInt : CartierModule p Φ' →+ CartierModule p Φ')

@[scoped simp] theorem iterV_apply (N : ℕ) (a : CartierModule p Φ) : iterV (p := p) (Φ := Φ) N a = (⇑VV)^[N] a :=
  rfl

end generic
end B29CMU
end P2MW.S_CerednikDrinfeld_FormalODModule_isIsogenyOfHeight_four_of_map_eq_sub_verschiebungInt_edgeRingCharP
