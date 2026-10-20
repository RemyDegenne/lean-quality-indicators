@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp.FreeProduct

variable {ι : Type v} (G : ι → ProfiniteGrp.{u})

variable {G}

variable {P : ProfiniteGrp.{max u v}}

variable (G)

variable {G}

variable {Q : ProfiniteGrp.{max u v}}

/-- Continuous homomorphisms out of the free profinite product are equivalent
to families of continuous homomorphisms out of its factors.

The universal property uses Mathlib’s group coproduct and profinite-completion
approach; no particular printed source theorem is asserted for this construction. -/
noncomputable def homEquiv : (product G ⟶ P) ≃ (∀ i, G i →ₜ* P) where
  toFun f i := f.hom.comp (of G i)
  invFun := lift
  left_inv f := by
    apply hom_ext
    intro i
    exact lift_of (fun j ↦ f.hom.comp (of G j)) i
  right_inv f := funext fun i ↦ lift_of f i

end ProfiniteGrp.FreeProduct
end
