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

theorem psiHom_surjective (ψ : M₀.E ≃ₗ[K] V) : Function.Surjective (psiHom ψ) := by
  intro v
  obtain ⟨x, hx, hxv⟩ := M₀.π_surj (ψ.symm (Multiplicative.toAdd v))
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  show ψ (M₀.π x) = Multiplicative.toAdd v
  rw [hxv]
  simp

end CFSG.RankThree.GF2n.Smith81
end
