@[expose] public section

universe uR uM uI

namespace LinearMap

variable {R : Type uR} [Semiring R]

variable {M : Type uM} [AddCommGroup M] [Module R M]

variable {I : Type uI}

/-- The joint projector is the commuting product of the supplied maps at true
bits and their endomorphism-ring complements at false bits. -/
noncomputable def jointProjector [Finite I] (p : I → Module.End R M)
    (hcomm : Pairwise (fun i j ↦ Commute (p i) (p j))) (ε : I → Bool) :
    Module.End R M := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  exact Finset.univ.noncommProd (fun i ↦ if ε i then p i else 1 - p i) (by
    intro i hi j hj hij
    exact jointFactors_pairwise p hcomm ε hij)

end LinearMap
end
