public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (ringAut_card_and_cyclic cyclic_involutions_eq)

section Linearization

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

theorem normalizes_endRing {L : Subgroup (Module.End k W)ˣ} (a : (Module.End k W)ˣ)
    (hnorm : ∀ g ∈ L, a⁻¹ * g * a ∈ L) (δ : EndRing (repOfSubgroup L)) :
    ∃ y : EndRing (repOfSubgroup L),
      epsHom _ y = a.val * epsHom _ δ * (a⁻¹).val := by
  have hz : ∀ (g : ↥L) (v : W),
      (a.val * epsHom _ δ * (a⁻¹).val) (repOfSubgroup L g v) =
        repOfSubgroup L g ((a.val * epsHom _ δ * (a⁻¹).val) v) := by
    intro g v
    have hg' : a⁻¹ * g.1 * a ∈ L := hnorm g.1 g.2
    have e1 : a⁻¹ * g.1 = (a⁻¹ * g.1 * a) * a⁻¹ := by group
    have e2 : a * (a⁻¹ * g.1 * a) = g.1 * a := by group
    have h1 : a⁻¹.val (g.1.val v) = (a⁻¹ * g.1 * a).val (a⁻¹.val v) := by
      exact congrArg (fun u : (Module.End k W)ˣ => u.val v) e1
    have h2 : epsHom _ δ ((a⁻¹ * g.1 * a).val (a⁻¹.val v)) =
        (a⁻¹ * g.1 * a).val (epsHom _ δ (a⁻¹.val v)) :=
      epsHom_commutes (repOfSubgroup L) δ ⟨_, hg'⟩ _
    have h3 : a.val ((a⁻¹ * g.1 * a).val (epsHom _ δ (a⁻¹.val v))) =
        g.1.val (a.val (epsHom _ δ (a⁻¹.val v))) := by
      exact congrArg (fun u : (Module.End k W)ˣ => u.val (epsHom _ δ (a⁻¹.val v))) e2
    simp only [Module.End.mul_apply, repOfSubgroup_apply]
    rw [h1, h2, h3]
  obtain ⟨y, hy⟩ := (mem_endRing_iff (repOfSubgroup L)
    (a.val * epsHom _ δ * (a⁻¹).val)).mpr hz
  exact ⟨y, LinearMap.ext fun w => congrFun hy w⟩

end Linearization
end CFSG.QuasithinUnique.Setup.SL2Modules
end
