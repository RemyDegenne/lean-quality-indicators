namespace P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SolCHint

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Step2

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (CommRingCat.of A)} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (D : ChartData f)

namespace ChartData

scoped instance nonempty_O (k : Fin D.m) : Nonempty (D.O k : Scheme.{u}) := by
  obtain ⟨x, hx⟩ := D.V_nonempty k
  exact ⟨⟨x, D.V_le_preimage_Ω k hx⟩⟩

scoped instance isProper_ek (k : Fin D.m) : IsProper (D.ek k) := by
  haveI : IsClosedImmersion (D.ιΩ k) := D.isClosedImmersion_ιΩ k
  haveI : IsProper (D.ek k ≫ (D.ιι ∣_ D.Ω k)) := by rw [ek_comp]; infer_instance
  exact IsProper.of_comp _ (D.ιι ∣_ D.Ω k)

theorem V_eq_O (k : Fin D.m) : D.V k = D.O k := by
  refine le_antisymm (D.V_le_preimage_Ω k) ?_

  have hclopen : IsClopen (Set.range (D.ek k)) :=
    ⟨(D.ek k).isClosedMap.isClosed_range, (D.ek k).isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range (D.ek k)).Nonempty := by
    obtain ⟨x, hx⟩ := D.V_nonempty k
    exact ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩
  have huniv := hclopen.eq_univ hne
  intro x hx
  obtain ⟨v, hv⟩ : (⟨x, hx⟩ : (D.O k : Scheme.{u})) ∈ Set.range (D.ek k) := by
    rw [huniv]; trivial
  have h1 : ((D.ek k) v).1 = x := congrArg Subtype.val hv
  rw [Scheme.homOfLE_apply] at h1
  rw [← h1]
  exact v.2

end ChartData
end Step2
end SolCHint
end
end P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral
