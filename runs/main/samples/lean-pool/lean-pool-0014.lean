@[expose] public noncomputable section

open scoped MatrixOrder

open Filter

namespace ViscositySolns

variable {n : Nat}

theorem closedSuperjet_of_closedSuperjet_normalizedLeftOfBlockGradient
    {K : Set (Point n)} {u : Point n -> Real} {x0 : Point n} {P : BlockPoint n}
    {X : Hessian n}
    (hJ : ({ gradient := 0, hessian := X } : Jet n) ∈
      ClosedSuperjet K (normalizedLeftOfBlockGradient (n := n) u x0 P) 0) :
    ({ gradient := blockPointLeft P, hessian := X } : Jet n) ∈
      ClosedSuperjet ((fun x : Point n => x0 + x) '' K) u x0 := by
  let p : Point n := blockPointLeft P
  let uComp : Point n -> Real := fun x => u (x0 + x)
  let φ : Point n -> Real := fun x => -u x0 - dotProduct p x
  let A : Point n -> Jet n := fun _x => ({ gradient := -p, hessian := 0 } : Jet n)
  have hfun :
      normalizedLeftOfBlockGradient (n := n) u x0 P = fun x => uComp x + φ x := by
    funext x
    simp [normalizedLeftOfBlockGradient, uComp, φ, p]
    ring
  have hφ :
      ∀ y : Point n, y ∈ K -> HasSecondOrderExpansionWithin K φ y (A y) := by
    intro y _hy
    have hquad :=
      hasSecondOrderExpansionWithin_quadraticModel_recenter
        (C := K) (x0 := 0) (r := -u x0) (p := -p) (X := (0 : Hessian n)) y
    have hφ_eq :
        φ =
          fun z : Point n => quadraticModel 0 (-u x0) (-p) (0 : Hessian n) z := by
      funext z
      simp [φ, quadraticModel]
      ring
    have hA_eq :
        A y = quadraticModelJetAt 0 (-p) (0 : Hessian n) y := by
      apply (Jet.equivProd n).injective
      simp [A, Jet.equivProd, quadraticModelJetAt]
    simpa [hφ_eq, hA_eq] using hquad
  have hφ_cont : Continuous φ :=
    continuous_const.sub (continuous_const.dotProduct continuous_id)
  have hA_cont : Continuous A := continuous_const
  have hK :
      ({ gradient := blockPointLeft P, hessian := X } : Jet n) ∈ ClosedSuperjet K uComp 0 := by
    have hshift :
        ({ gradient := 0, hessian := X } : Jet n) - A 0 ∈ ClosedSuperjet K uComp 0 :=
      closedSuperjet_sub_of_add_hasSecondOrderExpansionWithin
        (C := K) (u := uComp) (φ := φ) (x := 0)
        (J := ({ gradient := 0, hessian := X } : Jet n))
        (A := A) hφ hφ_cont hA_cont (by simpa [hfun] using hJ)
    have hjet :
        ({ gradient := 0, hessian := X } : Jet n) - A 0 =
          ({ gradient := blockPointLeft P, hessian := X } : Jet n) := by
      apply (Jet.equivProd n).injective
      simp [A, p, Jet.equivProd]
    simpa [hjet, uComp] using hshift
  simpa [uComp] using closedSuperjet_translate_add_left (x0 := x0) (x := 0) hK

end ViscositySolns
end
