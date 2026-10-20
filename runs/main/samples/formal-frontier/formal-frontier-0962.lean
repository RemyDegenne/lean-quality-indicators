set_option warningAsError true

@[expose] public section

namespace AdicCompletion

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

@[simp]
theorem restrictScalarsEquiv_symm_eval (I : Ideal R) (x : AdicCompletion I M) (n : ℕ) :
    eval (I.map (algebraMap R S)) M n ((restrictScalarsEquiv I M).symm x) =
      (restrictScalarsLevelEquiv I M n).symm (eval I M n x) :=
  rfl

end AdicCompletion
end
