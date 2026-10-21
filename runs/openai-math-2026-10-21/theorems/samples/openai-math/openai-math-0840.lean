namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation

universe u v

variable {V : Type u} {E : Type v}

section TwoLegGeometry

attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor

variable {G : BondGraph V E} {k : ℕ}

theorem counted_split_legs (r : RawCorridor G k) (D : Set V) (ω B : Set E)
    (x y u v : V) (hc : r.counted Set.univ ω x y)
    (hr : r.retained ⊆ ω ∩ internalEdges G D) (hB : B ⊆ ω)
    (hd : Disjoint B r.retained) (huv : Conn G B u v)
    (hxu : Conn G (ω ∩ internalEdges G D) x u)
    (hvy : Conn G (ω ∩ internalEdges G D) v y)
    (hne : ¬Conn G (ω ∩ internalEdges G D) u v) :
    r.counted D ω x u ∨ r.counted D ω v y := by
  obtain ⟨e,he⟩ := r.retained_nonempty (by have := hc.1; omega)
  by_cases hp : ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x u
  · exact Or.inl (r.counted_one_leg D ω B x y u v hc hr hB hd huv hxu hvy hne e he hp)
  · have hxu' : Conn G ((ω ∩ internalEdges G D) \ {e}) x u := not_not.mp hp
    have hp' : ¬Conn G ((ω ∩ internalEdges G D) \ {e}) y v := by
      intro hyv
      apply (hc.2.2.2.1 e he).2
      have huniv : ω ∩ internalEdges G Set.univ = ω := by
        apply Set.Subset.antisymm Set.inter_subset_left
        exact fun _ he => ⟨he,fun _ _ => trivial⟩
      rw [huniv]
      have hB' : Conn G (ω \ {e}) u v := conn_mono G (show B ⊆ ω \ {e} from fun f hf => ⟨hB hf,fun hfe =>
        Set.disjoint_left.mp hd hf ((Set.mem_singleton_iff.mp hfe).symm ▸ he)⟩) huv
      exact conn_trans G _ (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) hxu')
        (conn_trans G _ hB' (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) (conn_symm G _ hyv)))
    exact Or.inr ((r.counted_symm D ω y v).mp (r.counted_one_leg D ω B y x v u
      ((r.counted_symm Set.univ ω x y).mp hc) hr hB hd (conn_symm G B huv)
      (conn_symm G _ hvy) (conn_symm G _ hxu) (fun h => hne (conn_symm G _ h)) e he hp'))

end RawCorridor
end TwoLegGeometry
end Percolation
end OAI
