namespace OAI

noncomputable section

open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

open Matrix

open Set Filter

open scoped Topology

open scoped BigOperators

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder

open scoped BigOperators Topology

open Filter Set

open Matrix

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace PolynomialPEPS.PinnedEntropy.NestedFilter

lemma jointEigenSpace_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily ℂ (fun c => JointEigenSpace A B c)
      (fun c => (JointEigenSpace A B c).subtypeₗᵢ) := by
  let f : Module.End.Eigenvalues B × Module.End.Eigenvalues A → ℂ × ℂ := fun c => (c.1.val, c.2.val)
  have hf : Function.Injective f := by
    intro c d h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  intro i j hij x y
  exact hA.orthogonalFamily_eigenspace_inf_eigenspace hB (hf.ne hij) x y

end PolynomialPEPS.PinnedEntropy.NestedFilter
end
end OAI
