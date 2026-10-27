public noncomputable section

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

open CFSG.GroupTheory.GL52 (F4 F4poly F4poly_natDegree F4poly_ne_zero)

open Polynomial

variable {W : Type*} [CommGroup W] [Finite W]

section Module

variable (hw2 : ∀ w : W, w ^ 2 = 1)

variable (x : MulAut W)

variable {x}

section CentralizerExplicit

theorem card_inf_centralizer_dvd_180 {W : Type*} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (hx3 : x ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (G X : Subgroup (MulAut W)) (hxgen : X = Subgroup.zpowers x)
    (hW : Nat.card W = 16) :
    Nat.card ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W))) ∣ 180 := by
  let f := hGLHom hw2 x hx3 hfix G X hxgen hW
  have hinj : Function.Injective f := hGLHom_injective hw2 x hx3 hfix G X hxgen hW
  have hcard : Nat.card ↥(G ⊓ Subgroup.centralizer (X : Set (MulAut W))) =
      Nat.card (MonoidHom.range f) := by
    exact Nat.card_congr (Equiv.ofInjective f hinj)
  have hdvd := (MonoidHom.range f).card_subgroup_dvd_card
  rw [← hcard] at hdvd
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 2) = 4 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) = 180 := by
    rw [Matrix.card_GL_field]
    simp [Fin.prod_univ_two, hq]
  simpa [hGL] using hdvd

end CentralizerExplicit
end Module
end CFSG.LocalAnalysis.WeakClosure81
end
end
