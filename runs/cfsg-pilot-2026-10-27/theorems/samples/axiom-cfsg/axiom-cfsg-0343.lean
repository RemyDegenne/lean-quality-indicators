public section

namespace CFSG.GF2Type.Smith1979.Case2.U43Lin

open Module

open scoped Classical

variable {K : Type} [Field K]

theorem card_le_eight_of_subgroup [Finite K] (h2 : (2 : K) ≠ 0)
    (A : Subgroup (GL (Fin 4) K)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a * a = 1) (hdet : ∀ a ∈ A, (a : Matrix (Fin 4) (Fin 4) K).det = 1) :
    Nat.card A ≤ 8 := by
  have hsqM : ∀ a : A, ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    intro a
    rw [← Units.val_mul, hsq _ a.2, Units.val_one]
  refine card_le_eight (V := Fin 4 → K) (Module.finrank_fin_fun K) h2
    (fun a : A => Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) ?_ ?_ ?_ ?_
  · intro a
    show Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hsqM a, Matrix.toLin'_one]
    rfl
  · intro a b
    show Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.toLin' ((b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.toLin' ((b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
    congr 1
    rw [← Units.val_mul, ← Units.val_mul, hcomm _ a.2 _ b.2]
  · intro a
    show LinearMap.det (Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = 1
    rw [LinearMap.det_toLin']
    exact hdet _ a.2
  · intro a b hab
    have hM : ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := Matrix.toLin'.injective hab
    exact Subtype.ext (Units.ext hM)

end CFSG.GF2Type.Smith1979.Case2.U43Lin
end
