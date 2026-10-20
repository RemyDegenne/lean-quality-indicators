namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_forall_le_cover_isAdmissible_and_n_eq_and_act_pow_mem_span

attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace S3X

open MvPowerSeries

variable {p : ℕ}

variable [Fact p.Prime]

section rig

variable {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}

variable {B B' : Type} [CommRing B] [CommRing B']

@[scoped simp] theorem pad_X (t : Rigidified p Φ B) (d : ℕ) : (pad t d).X = t.X := rfl

end rig
end S3X
end P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_forall_le_cover_isAdmissible_and_n_eq_and_act_pow_mem_span
