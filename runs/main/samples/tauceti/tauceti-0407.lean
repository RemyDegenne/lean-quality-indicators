public section

namespace TauCeti

universe u v w

@[simp]
theorem finiteGroupClassTrivial_mem_iff (H : Type w) [Group H] [Finite H] :
    finiteGroupClassTrivial.mem H ↔ Subsingleton H :=
  Iff.rfl

end TauCeti
end
