@[expose] public section

open CategoryTheory

universe u v w

namespace MulAction

theorem isPretransitive_centralizer_iff_stabilizer_normal
    {G : Type u} {X : Type v} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) :
    MulAction.IsPretransitive
      (Subgroup.centralizer (Set.range (MulAction.toPermHom G X))) X ↔
      (MulAction.stabilizer G x).Normal := by
  let C := Subgroup.centralizer (Set.range (MulAction.toPermHom G X))
  constructor
  · intro h
    let : IsPretransitive C X := h
    let : SMulCommClass G C X := ⟨fun g c y => by
      have hgc : toPermHom G X g * (c : Equiv.Perm X) =
          (c : Equiv.Perm X) * toPermHom G X g := c.property _ ⟨g, rfl⟩
      exact congrArg (fun p : Equiv.Perm X => p y) hgc⟩
    exact stabilizer_normal_of_pretransitive_commuting (H := C) x
  · intro h
    let : (stabilizer G x).Normal := h
    apply IsPretransitive.of_orbit (x₀ := x)
    intro y
    obtain ⟨g, rfl⟩ := exists_smul_eq G x y
    let n : Subgroup.normalizer (stabilizer G x : Set G) :=
      ⟨g⁻¹, by
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _⟩
    refine ⟨Action.autEquivPermCentralizer G X
      (normalizerQuotientEquivAut (G := G) x (QuotientGroup.mk n)), ?_⟩
    change (Action.autEquivPermCentralizer G X
      (normalizerQuotientEquivAut (G := G) x (QuotientGroup.mk n)) : Equiv.Perm X) x = g • x
    rw [Action.autEquivPermCentralizer_apply, normalizerQuotientEquivAut_mk_apply_self]
    change (g⁻¹)⁻¹ • x = g • x
    rw [inv_inv]

end MulAction
end
