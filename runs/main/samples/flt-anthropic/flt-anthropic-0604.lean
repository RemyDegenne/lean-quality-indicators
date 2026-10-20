set_option autoImplicit false

open MvPowerSeries

namespace MvPowerSeries.Restricted

universe u v w

variable {𝓞 : Type u} [CommRing 𝓞] {σ : Type v}

section Eval

variable (p : ℕ) {Y : Type w} [CommRing Y] [Algebra 𝓞 Y]

variable (hY : Cplt p Y)

include hY

theorem evalT_sub_psum_mem {S : MvPowerSeries σ 𝓞} (hS : Tendsto0 p S) (x : σ → Y) {N : ℕ}
    {T : Finset (σ →₀ ℕ)} (hT : hS.bad N ⊆ T) :
    evalT p hY x S - psum x T S ∈ Ideal.span {(p : Y) ^ N} := by
  have h1 := evalT_sub_psum_bad_mem p hY hS x N
  have h2 := psum_sub_psum_mem p hS x subset_rfl hT
  have := Ideal.add_mem _ h1 h2
  rwa [sub_add_sub_cancel] at this

end Eval
end MvPowerSeries.Restricted
