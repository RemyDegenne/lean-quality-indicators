public section

open Filter Topology

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace Pair

section

variable [IsTopologicalRing A]

variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- A morphism of Huber pairs is a continuous ring homomorphism carrying `A⁺` into `B⁺`. -/
structure Hom [IsHuberRing A] [IsHuberRing B] (S : Pair A) (T : Pair B) where
  /-- The underlying ring homomorphism. -/
  toRingHom : A →+* B
  /-- The underlying ring homomorphism is continuous. -/
  continuous_toRingHom : Continuous toRingHom
  /-- The underlying ring homomorphism carries `A⁺` into `B⁺`. -/
  map_mem_plus : ∀ a ∈ S.plus, toRingHom a ∈ T.plus

end
end Pair
end TauCeti.Huber
end
