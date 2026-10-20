@[expose] public section

open scoped TrivSqZeroExt

namespace SymmetricAlgebra

universe uR uM uN

variable {R : Type uR} {M : Type uM}

variable [CommRing R] [AddCommGroup M] [Module R M]

variable {N : Type uN} [AddCommGroup N] [Module R N]

theorem map_augmentationIdeal (f : M →ₗ[R] N) :
    augmentationIdeal (R := R) (M := M) ≤
      (augmentationIdeal (R := R) (M := N)).comap (map f) := by
  have compatibility : (algebraMapInv (R := R) (M := N)).comp (map f) =
      algebraMapInv (R := R) (M := M) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    simp [algebraMapInv]
  intro x hx
  apply (mem_augmentationIdeal_iff (R := R) (M := N) (map f x)).mpr
  rw [← AlgHom.comp_apply, compatibility]
  exact (mem_augmentationIdeal_iff (R := R) (M := M) x).mp hx

end SymmetricAlgebra
end
