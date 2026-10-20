public section

set_option warningAsError true

open Filter Function Set Topology

open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X Y : ι → Type*}

variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]

variable (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))

variable (e : ∀ i, X i →* Y i →* Circle)

variable [∀ i, TopologicalSpace (X i)]

omit [∀ i, TopologicalSpace (X i)] in
open scoped Classical in
@[simp]
theorem finset_prod_mulSingle_apply (s : Finset ι) (x : ∀ i, X i) (i : ι) :
    (∏ j ∈ s, mulSingle U j (x j)) i = if i ∈ s then x i else 1 := by
  change evalMonoidHom X i (∏ j ∈ s, mulSingle U j (x j)) = _
  rw [map_prod]
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    calc
      ∏ j ∈ s, evalMonoidHom X i (mulSingle U j (x j)) =
          evalMonoidHom X i (mulSingle U i (x i)) :=
        Finset.prod_eq_single_of_mem i hi fun j _ hji ↦ by
          simp [mulSingle_eq_of_ne U (x j) hji.symm]
      _ = x i := by simp
  · simp only [hi, ↓reduceIte]
    apply Finset.prod_eq_one
    intro j hj
    have hji : i ≠ j := fun hij ↦ hi (hij ▸ hj)
    simp [mulSingle_eq_of_ne U (x j) hji]

end RestrictedProduct
end
