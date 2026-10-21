namespace OAI

namespace Erdos970

section

namespace ErdosHypotheticalTag

open ErdosInverseAlignment ErdosAlignedProgression ErdosInverseCounts

attribute [local instance] Classical.decEq

theorem hypothetical_mod_agrees (a : ℕ → ℕ) (r : ℚ) (p : ℕ) [NeZero p] (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) (s : ℕ) :
    hypotheticalClass a r p s % s = a s % s := by
  by_cases hsp : s = p
  · subst s
    have hD := aligned_den_coprime_prime a r p hp ha
    have hh := hypothetical_aligns a r p hp hD
    exact (aligned_prime_hit_iff a r p (hypotheticalClass a r p p) hp ha).mpr
      ((aligns_iff_modEq (fun s => (hypotheticalClass a r p s : ℤ)) r p).mp hh)
  · rw [hypothetical_other a r p s hsp]

end ErdosHypotheticalTag
end
end Erdos970
end OAI
