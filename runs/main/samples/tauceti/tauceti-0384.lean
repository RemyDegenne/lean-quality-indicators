public section

open IsDedekindDomain NumberField

open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

theorem rayClassToClassGroup_eq_oneEquivClassGroup_comp_classMap (m : Modulus K) :
    rayClassToClassGroup m =
      oneEquivClassGroup.toMonoidHom.comp (classMap (Modulus.one_dvd m)) := by
  refine MonoidHom.ext fun c ↦ ?_
  obtain ⟨I, rfl⟩ := rayClassMk_surjective m c
  rw [rayClassToClassGroup_rayClassMk, MonoidHom.comp_apply, classMap_rayClassMk,
    MulEquiv.coe_toMonoidHom, oneEquivClassGroup_rayClassMk,
    NumberFieldArithmetic.coe_idealsAwayInclusion]

end TauCeti.GlobalNumberFields
end
