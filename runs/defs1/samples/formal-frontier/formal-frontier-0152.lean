@[expose] public section

noncomputable section

open scoped DirectSum TensorProduct

namespace exteriorPower

universe u v w

/-- The ordered component of the existing exterior-power direct-sum decomposition.
The `M` block precedes the `N` block. Its data uses only the stock equivalence,
component inclusion, and the ambient-preserving transport of the right degree. -/
@[no_expose]
noncomputable def prodPairing
    (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i j : ℕ) :
    ((⋀[R]^i M) ⊗[R] (⋀[R]^j N)) →ₗ[R] ⋀[R]^(i + j) (M × N) :=
  let t : Fin (i + j + 1) :=
    ⟨i, Nat.lt_succ_iff.mpr (Nat.le_add_right i j)⟩
  let rightDegree : (⋀[R]^j N) ≃ₗ[R] ⋀[R]^((i + j) - i) N :=
    LinearEquiv.ofEq (ExteriorAlgebra.exteriorPower R j N)
      (ExteriorAlgebra.exteriorPower R ((i + j) - i) N)
      (congrArg (fun n : ℕ ↦ ExteriorAlgebra.exteriorPower R n N)
        (Nat.add_sub_cancel_left i j).symm)
  (prodEquivDirectSum R M N (i + j)).symm.toLinearMap ∘ₗ
    DirectSum.lof R (Fin (i + j + 1))
      (fun a ↦ (⋀[R]^a.1 M) ⊗[R] (⋀[R]^((i + j) - a.1) N)) t ∘ₗ
        (TensorProduct.congr (LinearEquiv.refl R (⋀[R]^i M)) rightDegree).toLinearMap

end exteriorPower
end
end
