@[expose] public section

universe uR uM uI

namespace LinearMap

variable {R : Type uR} [Semiring R]

variable {M : Type uM} [AddCommGroup M] [Module R M]

variable {I : Type uI}

variable [Finite I]

@[simp]
theorem commutingIdempotentsPiEquiv_apply (p : I → Module.End R M)
    (hp : ∀ i, IsIdempotentElem (p i))
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (x : M) (ε : I → Bool) :
    commutingIdempotentsPiEquiv p hp hcomm x ε = jointComponent p hp hcomm ε x := by
  classical
  let : Fintype (I → Bool) := Fintype.ofFinite (I → Bool)
  apply Subtype.ext
  simp only [commutingIdempotentsPiEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply, LinearEquiv.coe_ofEq_apply,
    CompleteOrthogonalIdempotents.coe_piRangeEquiv_apply, jointComponent_apply]

end LinearMap
end
