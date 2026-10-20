@[expose] public section

namespace Complexity

namespace RAM

namespace Structured

namespace Scanner

theorem spaceBound_bigO_quasilinear (spec : Spec) :
    spaceBound spec =O quasilinearBound spec := by
  have hpoint : ∀ n, spaceBound spec n ≤ 2 * quasilinearBound spec n := by
    intro n
    simp only [spaceBound, quasilinearBound]
    calc
      (n + inputBase spec) * (2 * bitlen (n + inputBase spec))
          = 2 * ((n + inputBase spec) * bitlen (n + inputBase spec)) := by ring
      _ ≤ 2 * ((n + inputBase spec) *
            (bitlen (n + inputBase spec) + 1)) :=
        Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left (n + inputBase spec) (by omega))
  exact (BigO.of_le hpoint).trans
    (BigO.const_mul_left 2 (BigO.refl (quasilinearBound spec)))

end Scanner
end Structured
end RAM
end Complexity
end
