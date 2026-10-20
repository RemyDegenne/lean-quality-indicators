set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

open scoped commutatorElement

/-- Coefficient mapping restricted to the stable elementary subgroups. -/
noncomputable def StableGL.mapElementary
    {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S) :
    stableElementarySubgroup R →* stableElementarySubgroup S where
  toFun e := ⟨StableGL.map f e.1,
    StableGL.map_elementarySubgroup_le f (Subgroup.mem_map_of_mem _ e.2)⟩
  map_one' := Subtype.ext (map_one (StableGL.map f))
  map_mul' _ _ := Subtype.ext (map_mul (StableGL.map f) _ _)

end Matrix.GeneralLinearGroup
end
