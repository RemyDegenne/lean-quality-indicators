@[expose] public section

universe uR uM uι

namespace Module.Basis

variable {R : Type uR} [Ring R]

variable {M : Type uM} [AddCommGroup M] [Module R M]

variable {ι : Type uι}

theorem HasMinimalSupport.coord_ne_apply_of_apply_eq_zero
    {b : Basis ι R M} {x : M} (hb : b.HasMinimalSupport x)
    {j : ι} (hj : j ∈ (b.repr x).support)
    (φ : M →ₗ[R] R) (hφj : φ (b j) = 0) :
    b.repr x j ≠ φ x := by
  classical
  intro hcoord
  let e : M ≃ₗ[R] M := LinearEquiv.transvection hφj
  let b' : Basis ι R M := b.map e
  have hrepr : b'.repr x = (b.repr x).erase j := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [b', e, LinearEquiv.transvection.symm_eq,
        LinearMap.transvection.apply, hφj, hcoord]
    · simp [b', e, LinearEquiv.transvection.symm_eq,
        LinearMap.transvection.apply, hφj, hkj]
  have hle := hb b'
  rw [hrepr, Finsupp.support_erase] at hle
  exact (Nat.not_lt_of_ge hle) (Finset.card_erase_lt_of_mem hj)

end Module.Basis
end
