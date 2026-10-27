public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus

open Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

section Involutions

namespace KGC

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {d f : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem conclusion_of_reps (hR : EvenOrthogonalRealization Q f) {g₁ g₂ : similarityPairs Q}
    (hg₁ : g₁ ∈ unitMultiplierPairs Q) (hg₂ : g₂ ∈ unitMultiplierPairs Q)
    (h₁ : matrixProjectiveConjugationHom Q g₁ ≠ 1) (h₂ : matrixProjectiveConjugationHom Q g₂ ≠ 1)
    (h₁₁ : matrixProjectiveConjugationHom Q g₁ * matrixProjectiveConjugationHom Q g₁ = 1)
    (h₂₂ : matrixProjectiveConjugationHom Q g₂ * matrixProjectiveConjugationHom Q g₂ = 1)
    (h₁₂ : matrixProjectiveConjugationHom Q g₁ * matrixProjectiveConjugationHom Q g₂ =
      matrixProjectiveConjugationHom Q g₂ * matrixProjectiveConjugationHom Q g₁)
    (hσ₂ : g₂.val.right = 1) :
    g₁.val.right * g₁.val.right = 1 ∧
      (∀ v, Q (coordinateSemilinearMap g₁.val v) = g₁.val.right (Q v)) ∧
      (∀ v, coordinateSemilinearMap g₁.val (coordinateSemilinearMap g₁.val v) = v) ∧
      (∀ v, Q (coordinateSemilinearMap g₂.val v) = Q v) ∧
      (∀ v, coordinateSemilinearMap g₂.val (coordinateSemilinearMap g₂.val v) = v) ∧
      ∀ v, coordinateSemilinearMap g₂.val (coordinateSemilinearMap g₁.val v) =
        coordinateSemilinearMap g₁.val (coordinateSemilinearMap g₂.val v) := by
  obtain ⟨-, -, -, huniq, _Fp, -, -, -, hinv⟩ := hR
  have ho₁ : orderOf (matrixProjectiveConjugationHom Q g₁) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact h₁₁) h₁
  have ho₂ : orderOf (matrixProjectiveConjugationHom Q g₂) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact h₂₂) h₂
  obtain ⟨hgg₁, hT₁, -⟩ := hinv _ ⟨g₁, rfl⟩ ho₁ g₁ hg₁ rfl
  obtain ⟨-, hT₂, -⟩ := hinv _ ⟨g₂, rfl⟩ ho₂ g₂ hg₂ rfl
  have hc : g₁ * g₂ = g₂ * g₁ :=
    (huniq _ ⟨g₁ * g₂, rfl⟩).unique ⟨mul_mem hg₁ hg₂, rfl⟩
      ⟨mul_mem hg₂ hg₁, by rw [map_mul, map_mul]; exact h₁₂.symm⟩
  refine ⟨?_, hg₁, hT₁, fun v => ?_, hT₂, fun v => ?_⟩
  · have h := congrArg (fun g : similarityPairs Q => g.val.right) hgg₁
    exact h
  · rw [(mem_unitMultiplierPairs_iff Q g₂).1 hg₂ v, hσ₂]
    rfl
  · have h := congrArg (fun g : similarityPairs Q => coordinateSemilinearMap g.val v) hc
    change coordinateSemilinearMap (g₁.val * g₂.val) v =
      coordinateSemilinearMap (g₂.val * g₁.val) v at h
    rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_mul] at h
    exact h.symm

end KGC
end Involutions
end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlus
end
