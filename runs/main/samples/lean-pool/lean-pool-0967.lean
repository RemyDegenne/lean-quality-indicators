@[expose] public section

open scoped BigOperators symmDiff

noncomputable section

namespace Chvatal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem two_spectral_eq_boundary (F : Family ι) (g : Finset ι → ℝ) :
    2 * (∑ T, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Odd (S ∩ T).card),
      fourier F.indicator S ^ 2 * fourier g T ^ 2) =
      (∑ x ∈ F, ∑ y ∈ Fᶜ, fourier g (x ∆ y) ^ 2) /
        Fintype.card (Finset ι) := by
  rw [two_spectral_eq_weighted_flip, weighted_flip_energy, cubeMean,
    indicator_boundary_sum F (fun x y => fourier g (x ∆ y) ^ 2)
      (fun x y => by rw [symmDiff_comm])]
  ring

end Chvatal
end
end
