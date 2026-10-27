namespace P2MW.S_ModularCurve_index_heckeUpper

set_option autoImplicit false

open Matrix CongruenceSubgroup Subgroup HeckeEis

open scoped MatrixGroups

namespace ModularCurve

namespace IndexHeckeUpper

section HCE

section Representatives

variable {N ℓ : ℕ}

def bezoutRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Gamma0 N :=
  ⟨⟨!![Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), (ℓ : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination hecke_bezout hℓ hℓN⟩, by
    rw [Gamma0_mem]
    show ((N : ℤ) : ZMod N) = 0
    rw [Int.cast_natCast]
    exact ZMod.natCast_self N⟩

end Representatives
end HCE
end IndexHeckeUpper
end ModularCurve
end P2MW.S_ModularCurve_index_heckeUpper
