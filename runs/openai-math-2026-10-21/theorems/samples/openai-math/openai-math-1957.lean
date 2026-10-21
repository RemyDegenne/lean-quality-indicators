namespace OAI

namespace PartitionPilot.Forcing

open SetRealization

universe u

theorem IterationTraceCode.value {B : Type u} (s : Presentation B) (f : B → B) (b : B)
    {n : Nat} {t : ZFSet.{u}}
    (trace : IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier
      (s.graph s f) (s.encode b) t) :
    ∀ k ≤ n, ZFSet.pair (natSetCode k) (s.encode (natIterate f b k)) ∈ t := by
  intro k
  induction k with
  | zero => exact fun _ => trace.seed
  | succ k ih =>
    intro hk
    have domain := (natSetCode_mem_iff (k + 1) (n + 1)).2 (by omega)
    obtain ⟨y, rel, _⟩ := trace.function.2 (natSetCode (k + 1)) domain
    have hy := (ZFSet.pair_mem_prod.1 (trace.function.1 rel)).2
    obtain ⟨c, eq⟩ := (s.mem_carrier y).1 hy
    have step := trace.next (natSetCode k) ((natSetCode_mem_iff k n).2 (by omega))
      (natSetCode (k + 1)) domain _ (s.encode_mem _) y hy rfl (ih (by omega)) rel
    rw [← eq] at step
    have output := (s.pair_mem_graph s f _ c).1 step
    have same : y = s.encode (natIterate f b (k + 1)) := eq.symm.trans (congrArg s.encode output.symm)
    exact same ▸ rel

end PartitionPilot.Forcing
end OAI
