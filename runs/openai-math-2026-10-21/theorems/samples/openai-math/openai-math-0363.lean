namespace OAI

noncomputable section

attribute [instance] BoundedSystem.fP BoundedSystem.fE

namespace TorsionFreeZeroDivisors.ShortClosure

section

open scoped Classical BigOperators

open PortSubdivision WeightedMoore

variable {V D : Type} [Fintype V] [Fintype D] (Γ : PortGraph V D)
    (allowed : D → Prop) (z : V)

omit [Fintype V] in
lemma chain_mem {k : ℕ} {l : List D} (hl : l∈walks Γ allowed z k) :
    l.IsChain (PortWalk.step Γ.origin Γ.reverse) := by
  induction k generalizing l with
  | zero => have := Finset.mem_singleton.mp hl; subst l; simp
  | succ k ih =>
    obtain ⟨p,hp,d,hd,rfl⟩ := (mem_walks_succ Γ allowed z).mp hl
    have hd := (Finset.mem_filter.mp hd).2
    refine (ih hp).append (by simp) ?_
    intro e he f hf
    have hf : f=d := by simpa [eq_comm] using hf
    subst f
    refine ⟨?_,hd.2.2 e he⟩
    have he' : p.getLast?=some e := he
    simpa only [endpoint,he',Option.map_some,Option.getD_some] using hd.2.1.symm

end
end TorsionFreeZeroDivisors.ShortClosure
end
end OAI
