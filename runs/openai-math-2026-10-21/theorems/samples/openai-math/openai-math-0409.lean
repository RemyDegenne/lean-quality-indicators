namespace OAI

section

namespace ExactQuantumFactoring.Primality

open Polynomial

open scoped BigOperators

lemma Introspective.mul_poly {F : Type*} [CommRing F] {s k : ℕ} {f g : F[X]}
    (hf : Introspective s k f) (hg : Introspective s k g) :
    Introspective s k (f*g) := by
  intro z hz
  simp only [eval_mul, mul_pow]
  rw [hf z hz, hg z hz]

end ExactQuantumFactoring.Primality
end
end OAI
