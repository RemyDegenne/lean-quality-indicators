@[expose] public section

@[inherit_doc] notation:25 E " →ₛₗ.[" σ:25 "] " F:0 => LinearPMap σ E F

notation:25 E " →ₗ.[" R:25 "] " F:0 => LinearPMap (RingHom.id R) E F

variable {R S T : Type*} [Ring R] [Ring S] [Ring T] {σ : R →+* S} {τ : S →+* T} {E : Type*}
  [AddCommGroup E] [Module R E] {F : Type*} [AddCommGroup F] [Module S F] {G : Type*}
  [AddCommGroup G] [Module T G]

namespace LinearPMap

section Graph

variable {M : Type*} [Monoid M] [DistribMulAction M F] [Module R F] [SMulCommClass R M F] (y : M)

theorem le_graph_of_le {f g : E →ₗ.[R] F} (h : f ≤ g) : f.graph ≤ g.graph := by
  intro x hx
  rw [mem_graph_iff] at hx ⊢
  obtain ⟨y, hx⟩ := hx
  use ⟨y, h.1 y.2⟩
  simp only [hx, true_and]
  convert hx.2 using 1
  refine (h.2 ?_).symm
  simp only [hx.1]

end Graph
end LinearPMap
end
