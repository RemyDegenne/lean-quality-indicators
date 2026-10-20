public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

variable (hns : ∀ i : V, ∃ j, G.Adj i j)

local notation "Z" => nonisolatedZigzagQuotient k G

local notation "P" => zigzagProjective k G

local notation "R" => zigzagProjectiveRadicalPower k G

local notation "H" => zigzagProjectiveRadicalLayer k G

@[simp]
theorem zigzagProjectiveMiddleEquivNeighborHeads_mk (i : V) (x : R i 1)
    (j : G.neighborSet i) :
    (((zigzagProjectiveHeadEquivSocle k G hns j.1
      (zigzagProjectiveMiddleEquivNeighborHeads k G hns i (Submodule.Quotient.mk x) j) :
      R j.1 2) : P j.1) : Z) =
        (zigzagBasis k G hns).coord (.inr (.inl ⟨(i, j.1), j.2⟩)) (x.1 : Z) •
          zigzagVolume k G j.1 := by
  simp only [zigzagProjectiveMiddleEquivNeighborHeads, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    LinearEquiv.piCongrRight_apply, LinearEquiv.apply_symm_apply,
    middleToSocles_apply, coe_radical_smul, coe_socleVector]

end TauCeti
end
