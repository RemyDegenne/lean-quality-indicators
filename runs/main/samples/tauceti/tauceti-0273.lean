public section

namespace TauCeti

open AlgebraicGeometry

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

theorem isFractionRing_holomorphyRing (hF : IsFunctionField k F) {S : Set (Place k F)}
    (hS : Sᶜ.Nonempty) : IsFractionRing ↥(holomorphyRing S) F where
  map_units y :=
    (Units.mk0 (y : F) fun h ↦ nonZeroDivisors.ne_zero y.2 (Subtype.ext h)).isUnit
  surj z := by
    obtain ⟨Q, hQ⟩ := hS
    obtain ⟨y, hy0, hyS, hyzS⟩ := exists_ne_zero_mem_holomorphyRing_and_mul_mem hF hQ z
    refine ⟨⟨⟨y * z, hyzS⟩, ⟨⟨y, hyS⟩, mem_nonZeroDivisors_of_ne_zero fun h ↦ hy0 ?_⟩⟩, ?_⟩
    · exact congrArg Subtype.val h
    · exact mul_comm z y
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

end TauCeti
end
