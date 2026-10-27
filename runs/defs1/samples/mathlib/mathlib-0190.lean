@[expose] public section

section CommMonoid

variable {M : Type*} [CommMonoid M] {S : Submonoid M} {N : Type*} [CommMonoid N] {P : Type*}
  [CommMonoid P]

namespace AddSubmonoid

namespace LocalizationMap

section AwayMap

variable {A : Type*} [AddCommMonoid A] (x : A) {B : Type*} [AddCommMonoid B] (F : AwayMap x B)
  {C : Type*} [AddCommMonoid C] {g : A →+ C}

/-- Given `x : A`, a localization map `F : A →+ B` away from `x`, and a map of `AddCommMonoid`s
`g : A →+ C` such that `g x` is invertible, the homomorphism induced from `B` to `C` sending
`z : B` to `g y - n • g x`, where `y : A, n : ℕ` are such that `z = F y - n • F x`. -/
noncomputable def AwayMap.lift (hg : IsAddUnit (g x)) : B →+ C :=
  AddSubmonoid.LocalizationMap.lift F fun y ↦
    show IsAddUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn]
      dsimp
      rw [g.map_nsmul]
      exact IsAddUnit.map (nsmulAddMonoidHom n : C →+ C) hg

end AwayMap
end LocalizationMap
end AddSubmonoid
end CommMonoid
end
