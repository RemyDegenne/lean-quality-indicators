public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank

theorem irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders
    {f : ℕ} {K : Type} [Field K] (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K)
    {W : Type} [CommGroup W] [Finite W] [Nontrivial W]
    (hW : ∀ w : W, w * w = 1) (L : Subgroup (MulAut W)) (hperf : Group.IsPerfect L)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (α : L ⧸ Subgroup.center L ≃* unitaryPSU h 3) :
    (∃ φ : unitarySU 2 f K 3 →* L, Function.Surjective φ ∧ φ.ker ≤ unitaryScalars h 3 ∧
      (unitaryScalars h 3).map φ = Subgroup.center L ∧
      ∀ s, α (QuotientGroup.mk (φ s)) = unitaryProj h 3 s) ∧
    Nat.card (Subgroup.center L) ∣ Nat.gcd 3 (2 ^ f + 1) ∧
    (∀ t ∈ L, t * t = 1 → t ≠ 1 → 2 ^ (2 * f) ≤ (fixV (Subgroup.zpowers t)).index) ∧
    (∀ a ∈ Subgroup.normalizer (L : Set (MulAut W)), a * a = 1 →
      (¬ ∃ l ∈ L, ∀ x ∈ L, ∃ z ∈ L, (∀ y ∈ L, y * z = z * y) ∧
        a * x * a⁻¹ = l * x * l⁻¹ * z) →
      2 ^ (3 * f) ≤ (fixV (Subgroup.zpowers a)).index) ∧
    (∀ A : Subgroup (MulAut W), A ≤ Subgroup.normalizer (L : Set (MulAut W)) → A ≠ ⊥ →
      IsElemAbelian2 A → Nat.card A * Nat.card (fixV A) < Nat.card W) :=
  irreducible_even_unitary_three_full_normalizer_excludes_binary_offenders_of hf h
    threeInvolutionProduct_holds outerInverter_holds hW L hperf hirr α

end CFSG.QuasithinUnique.Setup.X5
end
