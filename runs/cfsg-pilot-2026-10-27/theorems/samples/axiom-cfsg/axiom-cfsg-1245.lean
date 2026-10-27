public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
  {U₀ : Subgroup (V ≃ₗ[K] V)}

theorem card_span_pair [Finite K] [Finite V] {c r : V} (hc : c ≠ 0)
    (hr : r ∉ Submodule.span K {c}) : Nat.card (Submodule.span K {c, r}) = Nat.card K ^ 2 := by
  have hli : LinearIndependent K ![c, r] := by
    rw [LinearIndependent.pair_iff' hc]
    intro a ha
    apply hr
    rw [← ha]
    exact (Submodule.span K {c}).smul_mem a (Submodule.mem_span_singleton_self c)
  have hrange : Set.range ![c, r] = ({c, r} : Set V) := Matrix.range_cons_cons_empty c r _
  have hfin : Module.finrank K (Submodule.span K ({c, r} : Set V)) = 2 := by
    have h := finrank_span_eq_card hli
    rw [hrange, Fintype.card_fin] at h
    exact h
  haveI : Module.Finite K (Submodule.span K ({c, r} : Set V)) :=
    FiniteDimensional.span_of_finite K (Set.toFinite ({c, r} : Set V))
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(Submodule.span K ({c, r} : Set V))), hfin]

end CFSG.RankThree.GF2n.Smith81
end
