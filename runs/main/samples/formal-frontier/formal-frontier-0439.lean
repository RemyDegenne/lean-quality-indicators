@[expose] public section

universe u v

open CategoryTheory

universe uS

namespace KTheory

namespace K0

section PrincipalIdealDomainDimension

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem pidDimension_bijective :
    Function.Bijective
      ((finrankHom (FractionRing R)).comp (map (algebraMap R (FractionRing R)))) := by
  let : IsPrincipalIdealRing Rᵐᵒᵖ :=
    IsPrincipalIdealRing.of_surjective (RingEquiv.toOpposite R).toRingHom
      (RingEquiv.toOpposite R).surjective
  have hmap : Function.Bijective (map (algebraMap R (FractionRing R))) :=
    map_bijective_of_projectiveClass_map_bijective _
      (ProjectiveClass.map_bijective_of_projective_free _ fun X ↦
        Module.Projective.free_of_pid Rᵐᵒᵖ X)
  have hdimension : Function.Bijective (finrankHom (FractionRing R)) := by
    rw [← finrankEquiv_toAddMonoidHom]
    exact (finrankEquiv (FractionRing R)).bijective
  exact hdimension.comp hmap

end PrincipalIdealDomainDimension
end K0
end KTheory
end
