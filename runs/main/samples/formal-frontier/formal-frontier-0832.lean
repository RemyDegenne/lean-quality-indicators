@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]

theorem invariantBasisNumber (f : R →+* S) [InvariantBasisNumber S] :
    InvariantBasisNumber R := by
  apply invariantBasisNumber_iff_matrix.mpr
  intro n m a b hab hba
  apply (invariantBasisNumber_iff_matrix.mp (inferInstance : InvariantBasisNumber S))
    n m (a.map f) (b.map f)
  · simp only [← Matrix.map_mul, hab, Matrix.map_one f (map_zero f) (map_one f)]
  · simp only [← Matrix.map_mul, hba, Matrix.map_one f (map_zero f) (map_one f)]

end RingHom
end
