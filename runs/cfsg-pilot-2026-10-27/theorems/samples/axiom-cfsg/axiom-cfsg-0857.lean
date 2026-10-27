public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Kt

variable {G : Type} [Group G]

theorem kfKt_of_data [Finite G] (hK0 : KFK0) {p f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {E : Subgroup G}
    (hEel : IsElementaryAbelian p E) {t : MulAut E} (hmovne : autMovedInG E t ≠ ⊥)
    (hex : kExceptional p (kZero p E t) f) {K : Subgroup G} (hKle : K ≤ kZero p E t)
    (hmod : StatedClassicalModel ↥K .PSL 2 2 f) (hmov : autMovedInG E t ≤ K)
    (hcent : E ⊓ Subgroup.centralizer (K : Set G) = autFixedInG E t)
    (hlift : ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)),
      k ∈ K ∧ E.normalizerMonoidHom ⟨k, hk⟩ = t) : KFKt p E f t K := by
  have hIsKt : ∀ K' : Subgroup G, K' ≤ kZero p E t → StatedClassicalModel ↥K' .PSL 2 2 f →
      autMovedInG E t ≤ K' → IsKt p E t K' := by
    intro K' hle hm hmv
    refine ⟨fun f' hf' => ?_, fun hne => absurd ⟨f, hex⟩ hne⟩
    have hff : f = f' := psu_three_degree_unique hex.2.2 hf'.2.2
    subst hff
    exact ⟨hle, hm, hmv⟩
  refine ⟨hIsKt K hKle hmod hmov, fun K' hK' => ?_, hmod, hcent, hmov, hlift⟩
  obtain ⟨hle', hm', hmv'⟩ := hK'.1 f hex
  exact hK0 G p E t f hp h5 hEel hmovne hex K' K hle' hKle hm' hmod hmv' hmov

end Kt
end CFSG.RankThree.PartOne.KF132
end
