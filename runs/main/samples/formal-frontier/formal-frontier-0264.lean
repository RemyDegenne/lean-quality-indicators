@[expose] public section

universe u v w

namespace MulActionHom

variable {G : Type u} [Group G] {H : Subgroup G}

variable {X : Type v} [MulAction G X]

theorem quotientEquivFixedPoints_symm_stabilizer (x : X) :
    (((quotientEquivFixedPoints G (MulAction.stabilizer G x) X).symm ⟨x, le_rfl⟩) :
      (G ⧸ MulAction.stabilizer G x) → X) = MulAction.ofQuotientStabilizer G x := by
  funext q
  refine Quotient.inductionOn' q ?_
  intro g
  rw [quotientEquivFixedPoints_symm_apply_mk, MulAction.ofQuotientStabilizer_mk]

end MulActionHom
end
