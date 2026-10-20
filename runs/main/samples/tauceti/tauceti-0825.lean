public section

open scoped MonoidAlgebra

namespace TauCeti

universe u v w

section Block

variable {k : Type u} {G : Type v} [CommSemiring k] [Monoid G] {ι : Type w} {d : ι → ℕ}
  (e : k[G] ≃ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)

@[simp]
theorem asAlgebraHom_blockRepresentation (i : ι) :
    (blockRepresentation e i).asAlgebraHom = blockAlgHom e i := by
  refine AlgHom.ext fun x => ?_
  induction x using MonoidAlgebra.induction_on with
  | of g => rw [Representation.asAlgebraHom_of]; simp [blockRepresentation]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul r x hx => rw [map_smul, map_smul, hx]

end Block
end TauCeti
end
