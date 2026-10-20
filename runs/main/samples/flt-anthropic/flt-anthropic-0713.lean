namespace P2MW.S_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open IsDedekindDomain

open AutomorphicForm

open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward

open scoped ENNReal

noncomputable section

namespace R1S83TAE

open Filter Topology AutomorphicForm.TransversalMeasure

open scoped TensorProduct.RightActions NumberField.LiesOver

attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel NumberField.Idele.ideleBorel
  M4aHerbrand.ArchSemilocal.extLiesOver

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

scoped instance borelSpace_idele : BorelSpace (AdeleRing (𝓞 L) L)ˣ := NumberField.Idele.borelSpace_ideleBorel L

scoped instance borelSpace_semiLocalUnits (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (L ⊗[K] v.adicCompletion K)ˣ := ⟨rfl⟩

scoped instance borelSpace_archUnits (v : InfinitePlace K) : BorelSpace (∀ w : v.Extension L, w.1.Completion)ˣ := ⟨rfl⟩

theorem isClosed_G (Sf : Finset (HeightOneSpectrum (𝓞 K))) : IsClosed (G K L Sf) := by
  have : G K L Sf = ⋂ v ∈ (↑Sf : Set (HeightOneSpectrum (𝓞 K)))ᶜ,
      semiLocalIdele K L v ⁻¹' (integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
    ext t
    simp only [G, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe,
      SetLike.mem_coe]
  rw [this]
  exact isClosed_biInter fun v _ => (isClosed_integralUnits K L v).preimage (continuous_semiLocalIdele K L v)

end R1S83TAE
end
end P2MW.S_AutomorphicForm_TwistedBruhat_ae_mem_structuredBox_of_transversal
