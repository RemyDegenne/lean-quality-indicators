public section

namespace TauCeti

open Finset

universe u v w x

namespace NumericalType

attribute [instance] componentFintype componentDecidableEq componentNonempty

variable (T : NumericalType.{u})

/-- The numerical type obtained by transporting the component set along an equivalence.

The finiteness and decidable equality of the new component set are transported along the
equivalence, so the target needs no instances of its own and may live in any universe. -/
@[expose]
def reindex {C : Type v} (e : T.Component ≃ C) : NumericalType.{v} :=
  letI : Fintype C := Fintype.ofEquiv _ e
  letI : DecidableEq C := e.symm.decidableEq
  { Component := C
    componentNonempty := T.componentNonempty.map e
    multiplicity c := T.multiplicity (e.symm c)
    weight c := T.weight (e.symm c)
    intersection := T.intersection.submatrix e.symm e.symm
    intersection_isSymm := T.intersection_isSymm.submatrix _
    offDiagonal_nonneg _ _ h := T.offDiagonal_nonneg _ _ fun hh ↦ h (e.symm.injective hh)
    connected i j := by
      have key : ∀ a b : T.Component,
          Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < T.intersection x y) a b →
          Relation.ReflTransGen
            (fun x y : C ↦ x ≠ y ∧ 0 < T.intersection.submatrix e.symm e.symm x y) (e a) (e b) := by
        intro a b hab
        induction hab with
        | refl => exact Relation.ReflTransGen.refl
        | @tail c d _ hcd ih =>
          refine ih.tail ⟨fun hh ↦ hcd.1 (e.injective hh), ?_⟩
          simpa using hcd.2
      simpa using key (e.symm i) (e.symm j) (T.connected _ _)
    fiber_relation i :=
      (Fintype.sum_equiv e.symm _
        (fun k ↦ (T.multiplicity k : ℤ) * T.intersection (e.symm i) k) fun _ ↦ rfl).trans
        (T.fiber_relation (e.symm i))
    weight_dvd _ _ := T.weight_dvd _ _
    genus c := T.genus (e.symm c) }

end NumericalType
end TauCeti
end
