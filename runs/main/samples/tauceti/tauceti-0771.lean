public section

open scoped BigOperators DirectSum TensorProduct

namespace TauCeti.TensorWords

universe uR uM

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

theorem isHomogeneous_deconcatenation (G : InternalGrading R M) :
    LinearMap.IsHomogeneous (deconcatenation R M) (grading G).piece
      ((grading G).tensorProduct (grading G)).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p w hw
  simp only [grading_piece, add_zero] at hw ⊢
  refine gradedPiece_induction
    (motive := fun w ↦ deconcatenation R M w ∈
      ((grading G).tensorProduct (grading G)).piece p) hw ?_ ?_ ?_ ?_
  · intro n d x hx hd
    rw [deconcatenation_of, deconcatenationComponent_tprod]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    let dl : Fin i.1 → ℤ := fun j ↦ d (Fin.castLE (by have := i.isLt; omega) j)
    let dr : Fin (n - i.1) → ℤ := fun j ↦ d ⟨i.1 + j.1, by have := j.isLt; omega⟩
    have hsum : (∑ j, dl j) + (∑ j, dr j) = p := by
      rw [← hd]
      have hi : i.1 + (n - i.1) = n := by have := i.isLt; omega
      calc
        _ = ∑ j : Fin (i.1 + (n - i.1)), d (Fin.cast hi j) := by
          simpa only [dl, dr, Fin.castLE, Fin.cast, Fin.castAdd, Fin.natAdd] using
            (Fin.sum_univ_add (fun j : Fin (i.1 + (n - i.1)) ↦ d (Fin.cast hi j))).symm
        _ = ∑ j, d j := Equiv.sum_comp (finCongr hi) d
    rw [← hsum]
    apply InternalGrading.tmul_mem_tensorProduct
    · exact mem_gradedPiece_of_tprod G _ dl (fun j ↦ hx _)
    · exact mem_gradedPiece_of_tprod G _ dr (fun j ↦ hx _)
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro r x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ r hx

end TauCeti.TensorWords
end
