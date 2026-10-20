public section

open CategoryTheory TensorProduct

universe u v

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] (I : Ideal R)

theorem reducedMap_bijective_of_tower (B C : Type v) [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    (hB : Function.Bijective (reducedMap I B))
    (hC : Function.Bijective (reducedMap (I.map (algebraMap R B)) C)) :
    Function.Bijective (reducedMap I C) := by
  have he : (I.map (algebraMap R B)).map (algebraMap B C) = I.map (algebraMap R C) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let e := Ideal.quotientEquivAlgOfEq C he
  have hcomp : e.toRingEquiv.toRingHom.comp
      ((reducedMap (I.map (algebraMap R B)) C).comp (reducedMap I B)) = reducedMap I C := by
    ext r
    simp only [RingHom.comp_apply, reducedMap_mk, ← IsScalarTower.algebraMap_apply]
    exact Ideal.quotientEquivAlgOfEq_mk C he _
  rw [← hcomp]
  exact e.bijective.comp (hC.comp hB)

end TauCeti.Henselization
end
