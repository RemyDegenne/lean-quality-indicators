public section

open Module MvPolynomial

universe u

namespace TauCeti

open YoungDiagram (ofPartition card_ofPartition)

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}

theorem char_weylRepOfShape_ofPartition_diagonal_eq_sum_spechtChar {d : ℕ} (μ : d.Partition)
    (x : Fin n → kˣ) :
    Representation.character (V := (weylModuleOfShape k n (ofPartition μ)).toSubmodule)
        (weylRepOfShape k n (ofPartition μ)) (diagGL x) =
      (d.factorial : k)⁻¹ * eval (fun i => (x i : k))
        (∑ σ : Equiv.Perm (Fin d), spechtChar μ σ • psumPart (Fin n) k σ.partition) := by
  simp_rw [char_weylRepOfShape_ofPartition_eq_sum_spechtChar,
    trace_permTensorAction_mul_tensorPowerRep_diagGL, map_sum, map_zsmul]

end TauCeti
end
