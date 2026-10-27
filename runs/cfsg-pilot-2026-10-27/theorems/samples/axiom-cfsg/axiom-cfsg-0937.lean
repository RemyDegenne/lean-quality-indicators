public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Vol2.Ch10.SecA

open scoped commutatorElement

section Transport

variable {W : Type} [CommGroup W]

theorem stabSub_map_eq (g : MulAut W) (V : Subgroup W) :
    stabSub (V.map g.toMonoidHom) = conjBy g (stabSub V) := by
  have key : ∀ w : W, w ∈ V.map g.toMonoidHom ↔ g⁻¹ w ∈ V := fun w => by
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
    · intro h
      exact ⟨g⁻¹ w, h, by simp⟩
  ext x
  rw [mem_conjBy_iff, mem_stabSub, mem_stabSub]
  constructor
  · intro h u
    have := h (g u)
    rw [key, key] at this
    simpa [MulAut.mul_apply] using this
  · intro h w
    rw [key, key]
    have := h (g⁻¹ w)
    simpa [MulAut.mul_apply] using this

end Transport
end CFSG.Quasithin.H13
end
