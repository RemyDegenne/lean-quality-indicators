public section

namespace TauCeti

open scoped BigOperators

namespace YoungTableau

variable {μ : YoungDiagram}

noncomputable section

/-- Acting on `{t}` gives the canonical intertwining map from the Young-symmetrizer ideal to
the polytabloid Specht module. -/
def spechtIdealToSubrepresentation (t : YoungTableau μ) :
    (spechtIdealRep t).ρ.IntertwiningMap (spechtSubrepresentation μ).toRepresentation where
  toLinearMap :=
    { toFun := fun x =>
        ⟨(permutationRep μ).asAlgebraHom
            (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)))
            (MonoidAlgebra.single (tabloid t) 1), spechtIdeal_apply_tabloid_mem t x⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp
      map_smul' := fun r x => by
        apply Subtype.ext
        simp }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearMap.comp_apply]
    -- Unpack the two restricted actions so that the group-algebra multiplication law applies.
    change
      (permutationRep μ).asAlgebraHom
          (((spechtIdealRep t).ρ g x : spechtIdeal t) :
            MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)))
          (MonoidAlgebra.single (tabloid t) 1) =
        (permutationRep μ) g
          ((permutationRep μ).asAlgebraHom
            (x : MonoidAlgebra ℚ (Equiv.Perm (Fin μ.card)))
            (MonoidAlgebra.single (tabloid t) 1))
    rw [spechtIdealRep_ρ_apply_coe, map_mul,
      Representation.asAlgebraHom_single_one, Module.End.mul_apply]

end
end YoungTableau
end TauCeti
end
