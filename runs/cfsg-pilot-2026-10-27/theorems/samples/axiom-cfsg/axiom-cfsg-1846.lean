public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

open CFSG.Quasithin.F53Mod

open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E8

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {δ : Geo H M}

omit [Finite G] in
theorem act_fixed_of_comm_eq_one (c : Ch.Chart δ) {u b : G} (hu : u ∈ stab δ) (hb : b ∈ Vn δ)
    (h : ⁅b, u⁆ = 1) : orth.act (th c u) (pg c b) = pg c b := by
  refine (comm_iff c hu hb).mp ?_
  have : u * b * u⁻¹ * b⁻¹ = ⁅u, b⁆ := (commutatorElement_def u b).symm
  rw [this, ← commutatorElement_inv, h, inv_one]
  exact (Zv δ).one_mem

end S35.E8
end F53.Stellmacher
end CFSG.Quasithin
end
