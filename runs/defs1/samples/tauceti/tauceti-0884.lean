public section

namespace TauCeti

open CartanMatrix CartanMatrix.Relations LieAlgebra

variable {B : Type*} [DecidableEq B] (R : Type*) [CommRing R] (CM : Matrix B B ℤ)

variable {L : Type*} [LieRing L] [LieAlgebra R L]

/-- Three families `H`, `E`, `F` of elements of a Lie algebra form a *Serre system* for the matrix
`CM` when they satisfy Serre's relations for `CM`. The fields are in bijection with the six
families of relators generating `CartanMatrix.Relations.toIdeal`, the `⁅E, F⁆` family being split
into its diagonal and off-diagonal halves. -/
structure IsSerreSystem (H E F : B → L) : Prop where
  /-- The `Hᵢ` commute. -/
  lie_H_H : ∀ i j, ⁅H i, H j⁆ = 0
  /-- `⁅Eᵢ, Fᵢ⁆` is `Hᵢ`. -/
  lie_E_F_self : ∀ i, ⁅E i, F i⁆ = H i
  /-- `Eᵢ` and `Fⱼ` commute for `i ≠ j`. -/
  lie_E_F_of_ne : ∀ i j, i ≠ j → ⁅E i, F j⁆ = 0
  /-- `Eⱼ` is an eigenvector of `ad Hᵢ` of eigenvalue `CMᵢⱼ`. -/
  lie_H_E : ∀ i j, ⁅H i, E j⁆ = CM i j • E j
  /-- `Fⱼ` is an eigenvector of `ad Hᵢ` of eigenvalue `-CMᵢⱼ`. -/
  lie_H_F : ∀ i j, ⁅H i, F j⁆ = -(CM i j • F j)
  /-- The higher Serre relation on the `E`'s. -/
  ad_pow_lie_E_E : ∀ i j, (ad R L (E i) ^ (-CM i j).toNat) ⁅E i, E j⁆ = 0
  /-- The higher Serre relation on the `F`'s. -/
  ad_pow_lie_F_F : ∀ i j, (ad R L (F i) ^ (-CM i j).toNat) ⁅F i, F j⁆ = 0

end TauCeti
end
