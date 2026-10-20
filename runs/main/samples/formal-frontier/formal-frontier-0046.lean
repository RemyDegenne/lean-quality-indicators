@[expose] public section

universe u

open Polynomial IsLocalRing

namespace Polynomial

theorem Monic.eq_factors_of_isCoprime_map
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) [IsLocalHom φ] {g h g' h' : R[X]}
    (hg : g.Monic) (hg' : g'.Monic) (hprod : g * h = g' * h')
    (hmap : g.map φ = g'.map φ) (hcoprime : IsCoprime (g.map φ) (h.map φ)) :
    g = g' ∧ h = h' := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    have hzero : IsUnit (0 : R) :=
      IsUnit.of_map φ 0 (isUnit_of_subsingleton _)
    letI : Subsingleton R := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hzero)
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  letI := hS
  have hcross : IsCoprime g' h := (hg'.isCoprime_map_iff (q := h) φ).mp (by
    rw [← hmap]
    exact hcoprime)
  have hdvd : g' ∣ g := hcross.dvd_of_dvd_mul_right ⟨h', hprod⟩
  have hdegree : g.natDegree = g'.natDegree := by
    simpa only [hg.natDegree_map, hg'.natDegree_map] using congrArg natDegree hmap
  have heq : g = g' :=
    eq_of_monic_of_dvd_of_natDegree_le hg' hg hdvd hdegree.le
  refine ⟨heq, hg.isRegular.left ?_⟩
  simpa only [heq] using hprod

end Polynomial
end
