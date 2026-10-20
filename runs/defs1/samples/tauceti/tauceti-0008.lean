public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  {d : ι → K} {root : ι → L}

variable (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
  (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))

/-- **The subset-product quadratic subfield of `M` attached to a nonempty subset.** Under
square-class independence, each nonempty subset `S` of the index type names the quadratic subfield
`K(∏_{i ∈ S} root i)` of `M = K(rootᵢ : i)`. -/
def quadraticSubfieldOfFinset (S : {S : Finset ι // S.Nonempty}) :
    {F : IntermediateField K (adjoin K (Set.range root)) // Module.finrank K F = 2} :=
  ⟨adjoin K {prodRootMem (K := K) root S.1}, finrank_adjoin_prodRootMem hroot (hindep S.1 S.2)⟩

end TauCeti.Multiquadratic
end
