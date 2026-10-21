namespace OAI

section

noncomputable section

noncomputable section

noncomputable section

open MeasureTheory Filter Set

open scoped Topology

noncomputable section

open MeasureTheory Filter Set

open scoped Topology ENNReal

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

namespace SingleLatticeCovering.BrokenCircuit

open scoped BigOperators

open Submodule

variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]

section FiniteField

attribute [local instance] Classical.propDecidable

variable {τ κ : Type*} [Fintype τ] [Fintype κ]

lemma card_fiber_mul_card_of_surjective
    {V U : Type*} [AddCommGroup V] [AddCommGroup U]
    [Module K V] [Module K U] [Fintype V] [Fintype U]
    (f : V →ₗ[K] U) (hf : Function.Surjective f) (b : U) :
    Fintype.card {x // f x = b} * Fintype.card U = Fintype.card V := by
  classical
  have hc (u : U) : Fintype.card {x // f x = u} = Fintype.card f.ker := by
    exact Fintype.card_congr (f.toAddMonoidHom.fiberEquivKerOfSurjective hf u)
  have hs := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Fintype.card_sigma] at hs
  simpa only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using hs

end FiniteField
end SingleLatticeCovering.BrokenCircuit
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end OAI
