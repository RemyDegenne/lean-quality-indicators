public section

open scoped TensorProduct commutatorElement

open WithConv

namespace TauCeti.HopfIdeal

noncomputable section

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

theorem eq_zero_of_forall_liftQuotientPoint_apply_eq_zero
    (S : Subgroup (WithConv (H →ₐ[k] k)))
    (x : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) (vanishingIdeal S))
    (hx : ∀ g : S, (CommHopfAlgCat.liftQuotientPoint (_root_.CommHopfAlgCat.of k H)
      (vanishingIdeal S) (CommAlgCat.of k k) g.val
      (fun y hy ↦ (mem_vanishingIdeal S y).mp hy g)).ofConv x = 0) : x = 0 := by
  apply quotientEval_separates S x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (pointKernelIdeal S) x
  intro g
  rw [Ideal.Quotient.mkₐ_eq_mk, quotientEval_mk]
  rw [Ideal.Quotient.mkₐ_eq_mk] at hx
  exact (CommHopfAlgCat.liftQuotientPoint_mk (_root_.CommHopfAlgCat.of k H)
    (vanishingIdeal S) (CommAlgCat.of k k) g.val
    (fun y hy ↦ (mem_vanishingIdeal S y).mp hy g) x).symm.trans (hx g)

end
end TauCeti.HopfIdeal
end
