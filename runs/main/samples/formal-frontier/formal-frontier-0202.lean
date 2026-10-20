public section

open scoped TensorProduct

universe uR uS uM

namespace ExteriorAlgebra

variable {R : Type uR} {S : Type uS} {M : Type uM}

variable [CommRing R] [CommRing S] [Algebra R S]

variable [AddCommGroup M] [Module R M]

@[simp] theorem equivBaseChange_symm_apply_tmul_ι (s : S) (m : M) :
    (equivBaseChange (R := R) (S := S) (M := M)).symm
        (s ⊗ₜ[R] ExteriorAlgebra.ι R m) =
      ExteriorAlgebra.ι S (s ⊗ₜ[R] m) := by
  exact ofBaseChange_tmul_ι s m

end ExteriorAlgebra
end
