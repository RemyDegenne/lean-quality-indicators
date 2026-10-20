public section

namespace TauCeti

open CategoryTheory Function TensorProduct

open _root_.Representation (IntertwiningMap)

universe u v

variable (k : Type u) [Ring k] (G : Type v) [Monoid G]

/-- **The reduction** `k ⊗_ℤ V` of a `G`-module `V`, with `G` acting on the second factor, as a
finitely generated representation of `G` over `k`; it is defined when `k ⊗_ℤ V` is finitely
generated over `k`, for instance when `V` is a finitely generated abelian group or, in
characteristic `ℓ`, when `V ⧸ ℓV` is finite (`TauCeti.finite_baseChange_of_finite_quotSMulTop`). -/
@[expose]
noncomputable def reduction (V : Type u) [AddCommGroup V] [DistribMulAction G V]
    [Module.Finite k (k ⊗[ℤ] V)] : FDRep k G :=
  ⟨FGModuleCat.of k (k ⊗[ℤ] V),
    (MulEquiv.toMonoidHom (MulEquiv.symm InducedCategory.endEquiv)).comp
      ((ModuleCat.endRingEquiv (ModuleCat.of k (k ⊗[ℤ] V))).symm.toMonoidHom.comp
        (Representation.baseChange k (Representation.ofDistribMulAction ℤ G V)))⟩

end TauCeti
end
