@[expose] public section

open Module Polynomial

noncomputable section

universe u v

section CommRing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {f : R[X]}

namespace IsAdjoinRootMonic

variable (h : IsAdjoinRootMonic S f)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `α` generates `S` as an algebra and `S` is free and finite,
then `S` is given by adjoining a root of `minpoly R α`.
Does not require that `R` is an integral domain, unlike `mkOfAdjoinEqTop`. -/
@[simps]
def mkOfAdjoinEqTop' [Module.Finite R S] [Module.Free R S] {α : S} (hα : Algebra.adjoin R {α} = ⊤) :
    IsAdjoinRootMonic S (minpoly R α) where
  __ : IsAdjoinRoot S (minpoly R α) :=
    have monic := minpoly.monic (Algebra.IsIntegral.isIntegral (R := R) α)
    haveI := monic.free_adjoinRoot
    haveI := monic.finite_adjoinRoot
    let φ := AdjoinRoot.liftAlgHom _ (Algebra.ofId R S) _ (minpoly.aeval R α)
    IsAdjoinRoot.ofAdjoinRootEquiv <| AlgEquiv.ofBijective φ <| by
      refine OrzechProperty.bijective_of_surjective_of_finrank_le φ.toLinearMap (fun s ↦ ?_) ?_
      · rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hα
        rcases hα s with ⟨p, hp⟩
        exact ⟨AdjoinRoot.mk (minpoly R α) p, by simp [φ, ← aeval_def, hp]⟩
      · nontriviality R
        exact finrank_quotient_span_eq_natDegree' monic ▸ minpoly.natDegree_le α
  map := aeval α
  monic := minpoly.monic (Algebra.IsIntegral.isIntegral α)

end IsAdjoinRootMonic
end CommRing
end
end
