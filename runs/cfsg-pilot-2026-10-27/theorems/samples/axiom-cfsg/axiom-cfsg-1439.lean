public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace DSit

variable {δ μ γ γ' : Geo H M} (hs : DSit H M S δ μ γ γ')

include hs

theorem exists_q : ∃ q ∈ Qv δ, q ∉ Qv μ := by
  by_contra hcon
  push Not at hcon
  have hle : Qv δ ≤ Qv μ := fun q hq => hcon q hq
  have h1 : stab μ ⊓ stab δ = Qv μ := by rw [← hs.prod, sup_eq_left.mpr hle]
  have h2 := hs.idx
  rw [h1, Subgroup.relIndex_self] at h2
  omega

end DSit
end S34
end F53.Stellmacher
end CFSG.Quasithin
end
