public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

section Certificates

theorem parabolicGradedDet_torusElt {J : Set (Fin τ.rank)} {d : ℤ} (hd : d ≠ 0)
    (i : Fin τ.rank) (u : Kˣ) :
    parabolicGradedDet (K := K) J d ⟨torusElt τ K i u, torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup i u)⟩ =
      u ^ gradedWeight τ J d i := by
  refine Units.ext ?_
  rw [coe_parabolicGradedDet, ← LinearMap.det_toMatrix (gradedBasis (K := K) hd)]
  have hdiag : LinearMap.toMatrix (gradedBasis (K := K) hd) (gradedBasis (K := K) hd)
      (gradedRestrictHom (K := K) J d
        ⟨torusElt τ K i u, torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup i u)⟩) =
      Matrix.diagonal
        (fun α : {α // α ∈ gradedRoots τ J d} =>
          ((u ^ (∑ j, τ.cartan i j * α.1 j) : Kˣ) : K)) := by
    ext α β
    rw [LinearMap.toMatrix_apply, gradedRestrictHom_torusElt hd, map_smul,
      Module.Basis.repr_self, Finsupp.smul_single, Matrix.diagonal_apply]
    by_cases h : α = β
    · subst h; simp
    · simp [h]
  have hprod : (∏ α : {α // α ∈ gradedRoots τ J d},
      u ^ (∑ j, τ.cartan i j * α.1 j)) = u ^ gradedWeight τ J d i := by
    rw [Finset.prod_zpow_eq_zpow_sum]
    congr 1
    simpa [gradedWeight] using
      (Finset.sum_coe_sort (gradedRoots τ J d) (fun α => ∑ j, τ.cartan i j * α j))
  rw [hdiag, Matrix.det_diagonal, ← Units.coe_prod, hprod]

end Certificates
end CFSG.LieType.Chevalley
end
