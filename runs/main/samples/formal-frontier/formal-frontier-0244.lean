@[expose] public section

universe u

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {k : Type u} [CommRing k] [CharP k p]

theorem isRegular_p_iff_isReduced :
    IsRegular (p : WittVector p k) ↔ IsReduced k := by
  constructor
  · intro hreg
    apply (isReduced_iff_pow_one_lt p (Fact.out : p.Prime).one_lt).mpr
    intro a ha
    have hx : (mk p fun _ : ℕ => a) * (p : WittVector p k) = 0 := by
      apply (mul_p_eq_zero_iff_coeff_pow_eq_zero _).mpr
      intro n
      simpa only [coeff_mk] using ha
    have hzero : (mk p fun _ : ℕ => a) = (0 : WittVector p k) :=
      hreg.right (by simpa only [zero_mul] using hx)
    simpa only [coeff_mk, zero_coeff] using
      congrArg (fun x : WittVector p k => x.coeff 0) hzero
  · intro hk
    letI : IsReduced k := hk
    have hker (x : WittVector p k) (hx : x * (p : WittVector p k) = 0) : x = 0 := by
      apply WittVector.ext
      intro n
      rw [zero_coeff]
      exact eq_zero_of_pow_eq_zero
        ((mul_p_eq_zero_iff_coeff_pow_eq_zero x).mp hx n)
    have hright : IsRightRegular (p : WittVector p k) := by
      intro x y hxy
      exact sub_eq_zero.mp (hker (x - y) (by
        rw [sub_mul]
        exact sub_eq_zero.mpr hxy))
    refine ⟨?_, hright⟩
    intro x y hxy
    apply hright
    simpa only [mul_comm] using hxy

end WittVector
end
