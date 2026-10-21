namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing

variable {V : Type u_1}

lemma lowDegree_invariant (p : Equiv.Perm V) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree edgeCoord d) :
    act p f ∈ lowDegree edgeCoord d := by
  apply Submodule.span_induction (p := fun f _ => act p f ∈ lowDegree edgeCoord d)
    _ _ _ _ hf
  · rintro f ⟨l, hl, rfl⟩
    have hprod : act p ((l.map edgeCoord).prod) =
        ((l.map (fun e => (p e.1, p e.2))).map edgeCoord).prod := by
      clear hl
      induction l with
      | nil => exact act_pointwise_one p
      | cons e l ih =>
        simp only [List.map_cons, List.prod_cons, act_pointwise_mul,
          act_edgeCoord, ih]
    rw [hprod]
    exact Submodule.subset_span ⟨_, by simpa, rfl⟩
  · simp
  · intro f g _ _ hf hg
    simpa only [map_add] using (lowDegree edgeCoord d).add_mem hf hg
  · intro c f _ hf
    simpa only [map_smul] using (lowDegree edgeCoord d).smul_mem c hf

end Pairing
end MatchingSmoothing
end OAI
