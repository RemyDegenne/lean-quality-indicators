@[expose] public section

open BoundedContinuousFunction Complex

namespace BoundedContinuousFunction

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {he : Continuous e} {hL : Continuous fun p : V × W ↦ L p.1 p.2}

set_option backward.isDefEq.respectTransparency false in
lemma star_mem_range_charAlgHom (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {x : V →ᵇ ℂ} (hx : x ∈ (charAlgHom he hL).range) :
    star x ∈ (charAlgHom he hL).range := by
  simp only [AlgHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  let z := y.map (starRingEnd _).toAddMonoidHom
  let f : W ↪ W := ⟨fun x ↦ -x, (fun _ _ ↦ neg_inj.mp)⟩
  refine ⟨.ofCoeff <| z.coeff.embDomain f, ?_⟩
  ext
  simp [charAlgHom_apply, Finsupp.sum_embDomain, z, Finsupp.sum_mapRange_index, f]

end BoundedContinuousFunction
end
