namespace OAI

noncomputable section

open scoped BigOperators TensorProduct

namespace BoundaryOnly.FormalObstruction.BlockTensor

open MixedForms SquareZero SignedTensor

variable {k t : Type*} [Field k] [Fintype t] [LinearOrder t]

variable (A K : t → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)]
  [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]

variable {A K}

variable (pd : ∀ i, K i → Derivation k (A i) (A i)) (q : ∀ i, A i)

local notation "PV" => (P (k := k) (A := A) (K := K))

variable (c : ∀ i, BlockCohomology.Contraction (pd i) (q i))

omit [Fintype t] in
theorem project_S (s : ∀ i, A i) (I : Finset t) :
    (p pd q c).comp ((tensorAction (V (k := k) A K) (S s) I).comp (j pd q c)) =
      tensorAction (H pd q) (HS pd q s) I := by
  apply project_tensor_map
  intro i
  by_cases hi : i ∈ I
  · apply LinearMap.ext; intro x
    simpa only [tensorAction, ite_eq_left hi, LinearMap.comp_apply, S, HS]
      using (c i).project_coefficient (s i) x
  · apply LinearMap.ext; intro x
    simpa only [tensorAction, ite_eq_right hi, LinearMap.comp_apply, LinearMap.id_apply]
      using (c i).p_j x

end BoundaryOnly.FormalObstruction.BlockTensor
end
end OAI
