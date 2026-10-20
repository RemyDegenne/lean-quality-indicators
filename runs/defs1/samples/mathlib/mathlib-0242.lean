@[expose] public section

open Function

universe u v w u₁

variable (ι : Type v) (β : ι → Type w)

scoped[DirectSum] notation3 "⨁ "(...)", "r:(scoped f => DirectSum _ f) => r

/-- The canonical isomorphism of a finite direct sum of additive commutative monoids
and the corresponding finite product. -/
def DirectSum.addEquivProd {ι : Type*} [Fintype ι] (G : ι → Type*) [(i : ι) → AddCommMonoid (G i)] :
    DirectSum ι G ≃+ ((i : ι) → G i) :=
  ⟨DFinsupp.equivFunOnFintype, fun g h ↦ funext fun _ ↦ by
    simp only [DFinsupp.equivFunOnFintype, Equiv.toFun_as_coe, Equiv.coe_fn_mk,
      ← DFinsupp.add_apply, Pi.add_apply]⟩

end
