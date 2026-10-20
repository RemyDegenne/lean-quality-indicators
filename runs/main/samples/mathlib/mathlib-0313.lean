@[expose] public section

namespace PointedCone

variable {R M N : Type*}

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

@[simp]
lemma DualFG.dual_dual_flip {C : PointedCone R N} (hC : C.DualFG p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, hDualFG, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

end PointedCone
end
