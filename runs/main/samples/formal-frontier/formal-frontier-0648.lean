@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

theorem homotopyMap_face_before {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    (ordinalMap (R := Polynomial R) (SimplexCategory.δ i.castSucc)).comp
      (homotopyMap (n + 1) j.succ) =
    (homotopyMap n j).comp (ordinalMap (SimplexCategory.δ i)) := by
  apply polynomialPolyRing_hom_ext
  · intro r; simp
  · simp only [RingHom.comp_apply, homotopyMap_X, map_mul, ordinalMap_coefficient,
      ordinalMap_tail_face]
    have hcut :
        (if (i.castSucc).val < (j.succ).val + 1 then (j.succ).val + 1 - 1
          else (j.succ).val + 1) = j.val + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hle : i.val ≤ j.val := by
        simpa only [Fin.val_castSucc] using (Fin.le_iff_val_le_val.mp hij)
      have hcutpos : i.val < j.val + 1 + 1 := by omega
      rw [ite_eq_left hcutpos]
      omega
    rw [hcut]
  · intro k
    rw [homotopyMap_ordinal_generator, ordinal_homotopyMap_generator,
      SimplexCategory.δ_comp_σ_of_le hij]

end
end CentralPolynomialSimplex
end
