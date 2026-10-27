public section

namespace CFSG.Fischer.Classification.Symplectic

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SympConfig

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (C : SympConfig V)

section Basic

theorem b_add_left (u u' v : V) : C.b (u + u') v = C.b u v + C.b u' v := by
  rw [map_add, LinearMap.add_apply]

end Basic
end SympConfig
end CFSG.Fischer.Classification.Symplectic
end
