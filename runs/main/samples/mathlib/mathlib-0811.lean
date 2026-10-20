@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace RingHom

variable {P Q : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop}

section IsStableUnderBaseChange

theorem IsStableUnderBaseChange.mk (h₁ : RespectsIso @P)
    (h₂ : ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T],
      P (algebraMap R T) → P (algebraMap S (S ⊗[R] T))) :
    IsStableUnderBaseChange @P := by
  introv R h H
  let e := h.symm.1.equiv
  let f' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
    (IsScalarTower.toAlgHom R S S')
  have hef (x : _) : e x = f' x := by
    suffices e.toLinearMap.restrictScalars R = f'.toLinearMap from congr($this x)
    exact ext' fun x y ↦ by simp [e, f', IsBaseChange.equiv_tmul, Algebra.smul_def]
  have hemul (x y : _) : e (x * y) = e x * e y := by simp_rw [hef, map_mul]
  convert h₁.1 _ { e with map_mul' := hemul } (h₂ H)
  ext x
  simp [e, h.symm.1.equiv_tmul, Algebra.smul_def]

end IsStableUnderBaseChange
end RingHom
end
