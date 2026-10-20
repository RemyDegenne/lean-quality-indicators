set_option warningAsError true

@[expose] public section

namespace AdicCompletion

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

@[simp]
theorem restrictScalarsEquiv_of (I : Ideal R) (x : M) :
    restrictScalarsEquiv I M (of (I.map (algebraMap R S)) M x) = of I M x := by
  apply AdicCompletion.ext
  intro n
  exact restrictScalarsLevelEquiv_mk I n x

end AdicCompletion
end
