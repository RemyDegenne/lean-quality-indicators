public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

open scoped commutatorElement Pointwise

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem commute_of_ne
    {J₁ J₂ : Set.range D.classOrbit} (h : J₁ ≠ J₂) {x y : ModGL τ k}
    (hx : x ∈ (D.withOrbit J₁).rootSpanJ) (hy : y ∈ (D.withOrbit J₂).rootSpanJ) :
    Commute x y :=
  (Subgroup.mem_centralizer_iff.1
    (unionRootSpan_le_centralizer_of_disjoint (D.disjoint_of_ne h) hx) y hy).symm

end OrthogonalSemilinearFixedRootDatum
end CFSG.LieType.Chevalley
end
