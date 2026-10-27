public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem setting46_of [IsSimpleGroup X] [Finite X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hKF : AutPSL2FusionInput) (hI : AutPSL2InvolutionInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    {t : X} {L : Subgroup X} {p f : ℕ} (h : Standing t L p f)
    (hmax : ∀ (t' : X) (L' : Subgroup X) (p' f' : ℕ), Config t' L' p' f' →
      twoPart (centralizer ({t'} : Set X)) ≤ twoPart (centralizer ({t} : Set X)))
    {S : Subgroup X} (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) {w z : X}
    (hσ : Standing.Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V
      (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {i j : ℕ}
    (hβ : IsBeta411 t L S w z V (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hβmax : ∀ β' : X, IsBeta411 t L S w z V β' →
      twoPart (centralizer ({β'} : Set X)) ≤
        twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hu : IsBeta411 t L S w z V (w ^ (orderOf w / 2)) ∧
      twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) ≤
        twoPart (centralizer ({w ^ (orderOf w / 2)} : Set X)) →
      w ^ (orderOf w / 2) * t ^ i * z ^ j = w ^ (orderOf w / 2)) :
    Setting46 t L p f S w z V i j where
  standing := h
  max_config := hmax
  sylow := hS
  setup := hσ
  sylow_V := hV
  le_V := hSV
  beta := hβ
  max_beta := hβmax
  pref_u := hu
  lemma45 := hσ.isLemma45 hFC hKC i j
  pLayer_M := hσ.pLayer_M hFC hKC i j
  lemma44a_z := hσ.isPGroup_quot_centralizer_z hI
  lemma44a_X := hσ.isPGroup_quot_centralizer_X hI hKC
  lemma44a_T := hσ.isPGroup_quot_normalizer_T hI
  lemma44b := fun _ hτS hτ2 hτ1 hτt hτ => hσ.lemma44b hI hKF hKC hτS hτ2 hτ1 hτt hτ
  lemma44e := fun _ hτS hτT hτ2 => ⟨hσ.dihedral_CL_of_not_mem_T hI hτS hτT hτ2,
    hσ.isSylowOf_z_CL_of_not_mem_T hI hτS hτT hτ2, hσ.isPGroup_quot_of_not_mem_T hI hτS hτT hτ2⟩
  lemma46a := ⟨hσ.layerIn_centralizer_tBar hFC hKC i j,
    hσ.layerIn_layer_centralizer_tBar hnonab hK hSch hFC hKC i j⟩
  lemma46b := hσ.lemma46b hFC hKC i j
  lemma46f := hσ.lemma46f hnonab hK hSch hFC hKC i j

end CFSG.ComponentClassification.HarrisLit
end
