set_option warningAsError true

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PullbackOpenImmersion

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

theorem fstTarget_sup_sndTarget (f : R →+* T) (g : S →+* T) :
    fstTarget f g ⊔ sndTarget f g = commonTarget f g := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus (↑(RingHom.ker (f.pullbackSnd g)) : Set (f.pullback g)))ᶜ ∪
      (PrimeSpectrum.zeroLocus (↑(RingHom.ker (f.pullbackFst g)) : Set (f.pullback g)))ᶜ =
      (PrimeSpectrum.zeroLocus (↑(RingHom.ker (toBase f g)) : Set (f.pullback g)))ᶜ
  rw [← Set.compl_inter, Set.inter_comm, ← PrimeSpectrum.zeroLocus_sup,
    ← ker_toBase]

end AlgebraicGeometry.PullbackOpenImmersion
end
end
