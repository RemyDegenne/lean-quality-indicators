public section

open Matrix

open scoped TensorProduct

universe u

namespace TauCeti

namespace YoungTableau

variable (k : Type u) [CommRing k] [Algebra ℚ k] (n : ℕ) {μ : YoungDiagram}

/-- **The Weyl module** of a `μ`-tableau `t`: the image of the Young symmetrizer `c_t` acting on
the `|μ|`-fold tensor power of the standard representation of `GL n k`, a subrepresentation
because the symmetric-group and general-linear actions commute.

Fulton and Harris write this as `𝕊^μ(kⁿ)`, the value at `kⁿ` of the Schur functor of `μ`; only
the value is built here, and no functoriality in the underlying module is claimed. -/
noncomputable def weylModule (t : YoungTableau μ) :
    Subrepresentation (tensorPowerRep k n μ.card) :=
  tensorPowerRange (stdRep k n) μ.card (youngSymmetrizerOver k t)

end YoungTableau
end TauCeti
end
