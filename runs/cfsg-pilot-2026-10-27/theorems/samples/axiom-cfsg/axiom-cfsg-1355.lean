public noncomputable section

namespace CFSG.LieType.Chevalley.EvenE6AllInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem exists_four_group_of_outer_E6
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (β : MulAut (adjointGroup TwistTag.E6.tag K)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (adjointGroup TwistTag.E6.tag K)) :
    ∃ A : Subgroup (adjointGroup TwistTag.E6.tag K), A ≤ β.toMonoidHom.eqLocus (MonoidHom.id _) ∧
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  obtain ⟨-, -, hexist⟩ :=
    ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hexpr⟩ := hexist β
  by_cases hσ : σ = 1
  · subst hσ
    have hid : ∀ h : ModGL TwistTag.E6.tag K,
        Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) h = h := fun h =>
      Units.ext (entrywise_id _)
    obtain ⟨ε, hε⟩ := ε
    have hε' : ε = 0 ∨ ε = 1 := by
      change ε < 2 at hε
      omega
    rcases hε' with rfl | rfl
    ·
      exfalso
      refine hβo (mem_inner_of_conj_mul_rootDiagAut hK hf g a ?_ hβ2)
      refine MulEquiv.ext fun h => Subtype.ext ?_
      have e := hexpr h
      have hQ0 : exactQ TwistTag.E6.tag K ((⟨0, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) = 1 :=
        pow_zero _
      rw [hQ0, hid, mul_one, inv_one, mul_one] at e
      rw [e, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    ·
      have hQ1 : exactQ TwistTag.E6.tag K ((⟨1, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) =
          diagramMap TwistTag.E6 K := pow_one _
      refine (even_E6_graph_involution_fixed_four_group f hf).1 K hK β
        (g : ModGL TwistTag.E6.tag K) a g.2 (fun h => ?_) hβ2
      have e := hexpr h
      rw [hQ1, hid] at e
      refine e.trans ?_
      group
  · exact even_E6_field_involution_fixed_four_group_of_expr hf K hK β hβ2 g a σ ε hexpr hσ

end CFSG.LieType.Chevalley.EvenE6AllInvolution
end
