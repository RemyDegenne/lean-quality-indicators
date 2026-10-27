@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- If the index of the `n`-th power image is `n`, a supplied topological
generator determines the continuous equivalence from the multiplicative
`ZMod n` to the finite quotient, sending the additive class of one to its
quotient class. The inverse gives the corresponding map to `ZMod n`. -/
noncomputable def powerImage_zmodContinuousMulEquiv (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (n : ℕ) (hn : 0 < n)
    (hindex : (powerImage G hG n : Subgroup G).index = n) :
    Multiplicative (ZMod n) ≃ₜ*
      (G ⧸ (powerImage G hG n : Subgroup G)) := by
  let H := (powerImage G hG n : Subgroup G)
  letI : DiscreteTopology (G ⧸ H) :=
    QuotientGroup.discreteTopology (powerImage_isOpen G hG n hn)
  have hgen : ∀ x : G ⧸ H,
      x ∈ Subgroup.zpowers ((QuotientGroup.mk' H) g) := by
    intro x
    rw [powerImage_quotient_zpowers_eq_top G hG g hg n hn]
    trivial
  have hcard : Nat.card (G ⧸ H) = n := H.index_eq_card.symm.trans hindex
  exact ContinuousMulEquiv.mk
    (zmodMulEquivOfGenerator hgen hcard)
    continuous_of_discreteTopology continuous_of_discreteTopology

end ProfiniteGrp
end
