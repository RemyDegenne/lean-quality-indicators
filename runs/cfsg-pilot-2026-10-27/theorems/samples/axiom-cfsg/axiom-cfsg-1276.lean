public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank Matrix Polynomial CFSG.RankThree.PartOne CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

namespace SevSpNs

variable {F : Type} [Field F] {n e s r p : ℕ}
  {A₀ : GL (Fin n ⊕ Fin n) F} {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r}
  {C : Matrix (Fin e) (Fin e) F}

omit [Field F] in
theorem nsCore_submatrix_perm [Field F] (C : Matrix (Fin e) (Fin e) F) (k : Fin s → ℕ)
    (σ : Equiv.Perm (Fin s)) :
    (SLNS.nsCore (r := r) C (k ∘ σ)).submatrix
        (Equiv.sumCongr (Equiv.prodCongr (Equiv.refl (Fin e)) σ.symm) (Equiv.refl (Fin r)))
        (Equiv.sumCongr (Equiv.prodCongr (Equiv.refl (Fin e)) σ.symm) (Equiv.refl (Fin r))) =
      SLNS.nsCore C k := by
  ext (⟨a, i⟩ | u) (⟨b, j⟩ | v) <;>
    simp [SLNS.nsCore, Matrix.blockDiagonal_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

end SevSpNs
end CFSG.StandardType
end
