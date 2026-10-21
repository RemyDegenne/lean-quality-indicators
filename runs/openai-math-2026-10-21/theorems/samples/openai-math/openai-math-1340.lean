namespace OAI

namespace PolynomialVacuumAlgebra

open MvPolynomial Classical

theorem basePolyThree_bound_6_2 :
    (basePolyThree (X (0:Fin 3)) (X 1) (X 2) .minus .zero .plus).degreeOf 2 ≤ 1 := by
  have h0 : ((C (q-q^3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h1 : ((X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h2 : (((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h0 h1
  have h3 : ((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := by simp [degreeOf_X]
  have h4 : ((C (q^2) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h5 : ((X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤1 := by simp
  have h6 : (((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤1 := dmul h4 h5
  have h7 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤1 := dadd (h3.trans (by omega)) (h6.trans (by omega))
  have h8 : ((C (q^6) : MvPolynomial (Fin 3) ℂ)).degreeOf (2:Fin 3)≤0 := le_of_eq (degreeOf_C _ _)
  have h9 : (((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))).degreeOf (2:Fin 3)≤0 := dmul h8 h1
  have h10 : (((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))).degreeOf (2:Fin 3)≤0 := (degreeOf_sub_le _ _ _).trans (max_le (h3.trans (by omega)) (h9.trans (by omega)))
  have h11 : ((((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))))).degreeOf (2:Fin 3)≤1 := dmul h7 h10
  have h12 : ((((C (q-q^3) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ))*(((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)+((C (q^2) : MvPolynomial (Fin 3) ℂ)*(X (2:Fin 3) : MvPolynomial (Fin 3) ℂ)))*((X (1:Fin 3) : MvPolynomial (Fin 3) ℂ)-((C (q^6) : MvPolynomial (Fin 3) ℂ)*(X (0:Fin 3) : MvPolynomial (Fin 3) ℂ)))))).degreeOf (2:Fin 3)≤1 := dmul h2 h11
  simpa only [basePolyThree,basePolyThreeFactor,basePolyTwo] using h12

end PolynomialVacuumAlgebra
end OAI
