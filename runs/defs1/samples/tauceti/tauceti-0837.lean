public section

open CategoryTheory

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

variable {G R}

section Intertwining

variable (G R) (G' : GridDiagram n)
  {σ σ' : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] (e : GridChainMinus R n ≃ₛₗ[σ] GridChainMinus R n)
  (he : ∀ c, G'.unblockedDifferential R (e c) = e (G.unblockedDifferential R c))

include he

/-- **The equivalence of unblocked grid homologies induced by an intertwining map.** A
semilinear equivalence `e` of chain modules with `∂⁻' ∘ e = e ∘ ∂⁻` induces a semilinear
equivalence `GH⁻(G) ≃ GH⁻(G')`, sending the class of a cycle `z` to the class of `e z`. -/
noncomputable def unblockedHomologyEquivOfIntertwining :
    G.unblockedHomology R ≃ₛₗ[σ] G'.unblockedHomology R :=
  (G.unblockedHomologyIso R).toLinearEquiv.trans <|
    (Submodule.Quotient.equiv _ _ (G.unblockedCyclesEquivOfIntertwining R G' e he)
      (G.map_boundariesInKer_unblockedCyclesEquivOfIntertwining R G' e he)).trans
        (G'.unblockedHomologyIso R).toLinearEquiv.symm

end Intertwining
end GridDiagram
end TauCeti
end
