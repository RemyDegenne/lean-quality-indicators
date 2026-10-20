public section

namespace AlgHom

variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

theorem finSepDegree_fieldRange (f : K →ₐ[F] L) [Algebra K L] (h : ∀ z, algebraMap K L z = f z) :
    Field.finSepDegree f.fieldRange L = Field.finSepDegree K L := by
  let _ : Algebra K f.fieldRange := (f.equivFieldRange).toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower K f.fieldRange L :=
    IsScalarTower.of_algebraMap_eq fun z ↦ by
      rw [RingHom.algebraMap_toAlgebra]
      exact (h z).trans (AlgHom.equivFieldRange_apply_coe f z).symm
  exact Field.finSepDegree_eq_of_surjective fun r ↦
    ⟨f.equivFieldRange.symm r, by
      rw [RingHom.algebraMap_toAlgebra]; exact f.equivFieldRange.apply_symm_apply r⟩

end AlgHom
end
