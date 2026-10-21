namespace OAI

universe u_m u_n u_A u_X u_Y u_I u_R u_B

noncomputable section

open scoped BigOperators MatrixOrder ComplexOrder

open Matrix

namespace ThresholdParallelRepetition

open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law MeasurementTransport

namespace MixedExposure

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

namespace Refinement

variable {S : EventSystem X Y I R m n} (T : Refinement S A B)

omit [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] in
lemma avg_if_massAt (i : I) (hi : i ∈ S.l) (V : X×Y → Bool)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ) :
    S.μ.avg (fun q => if V q then massAt S.μ S.θ S.p i S.C F H q else 0) =
      (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
        (if V (z i) then prob S.C (F r z) (H r z) else 0)) := by
  have he : (fun q => if V q then massAt S.μ S.θ S.p i S.C F H q else 0) =
      (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
        (if V ((Function.update z i q) i) then prob S.C (F r (Function.update z i q)) (H r (Function.update z i q)) else 0))) := by
    funext q
    simp only [Function.update_self]
    split <;> simp_all [massAt, avg, smul_eq_mul]
  rw [he, avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ i S.θ
    (fun r => S.localθL r i hi) (fun r => S.localθR r i hi)
    (fun r z => if V (z i) then prob S.C (F r z) (H r z) else 0)

end Refinement
end MixedExposure
end ThresholdParallelRepetition
end
end OAI
