public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- **Branching of the standard representation of `GL (Fin (n + 1)) k` to `GL (Fin n) k`.**  The
restriction along the block inclusion is the standard representation of the smaller group plus a
trivial summand, carried by the splitting of a vector into its first `n` coordinates and its last
one. -/
noncomputable def stdRepBlockSuccEquiv :
    Representation.Equiv
      ((stdRep k (n + 1)).comp (glBlockSucc k n) :
        Representation k (GL (Fin n) k) (Fin (n + 1) → k))
      ((stdRep k n).prod (Representation.trivial k (GL (Fin n) k) k)) :=
  Representation.Equiv.mk (LinearEquiv.piFinSnoc k fun _ => k) fun g => LinearMap.ext fun v =>
    Prod.ext (by simp [blockSucc_mulVec]) (by simp [blockSucc_mulVec])

end CommRing
end TauCeti
end
