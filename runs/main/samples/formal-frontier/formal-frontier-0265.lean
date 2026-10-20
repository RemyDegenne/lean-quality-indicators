@[expose] public section

universe a w p r v

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

theorem tensorNormalizedChainComplexXIso_hom_d (A : Type a) [AddCommGroup A]
    (S : SSet.{w}) (i j : ℕ) :
    (tensorNormalizedChainComplexXIso.{a, w, p} A S i).hom ≫
        (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).d i j =
      tensorNormalizedDifferential.{a, w, p} A S i j ≫
        (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom := by
  classical
  by_cases hij : i = j + 1
  · subst i
    rw [tensorNormalizedDifferential_succ]
    apply tensorNormalizedChainComplexX_hom_ext.{a, w, p} A S (j + 1)
    intro s x
    change
      ((S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).d (j + 1) j).hom
          ((tensorNormalizedChainComplexXIso.{a, w, p} A S (j + 1)).hom.hom
            (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x))) =
        (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom.hom
          ((tensorNormalizedBoundary.{a, w, p} A S j).hom
            (ULift.up (Finsupp.single s 1 ⊗ₜ[ℤ] x)))
    have hd :
        ((S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).d (j + 1) j).hom
            ((S.ιNormalizedChainComplex
              (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val).hom (ULift.up x)) =
          ∑ k : Fin (j + 2), ((-1 : ℤ) ^ k.val) •
            (S.ιNormalizedChainComplex
              (R := ModuleCat.of ℤ (ULift.{max w p} A)) (S.δ k s.val)).hom (ULift.up x) := by
      -- Evaluation is additive, so it preserves the alternating sum.
      let ev :
          (ModuleCat.of ℤ (ULift.{max w p} A) ⟶
            (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X j) →+
              (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X j :=
        (LinearMap.evalAddMonoidHom
          (ULift.up x : ModuleCat.of ℤ (ULift.{max w p} A))).comp
            ModuleCat.homAddEquiv.toAddMonoidHom
      exact (congrArg ev
        (S.ιNormalizedChainComplex_d
          (R := ModuleCat.of ℤ (ULift.{max w p} A)) s.val)).trans
        ((map_sum ev _ Finset.univ).trans
          (Finset.sum_congr rfl (fun k _ ↦ map_zsmul ev ((-1 : ℤ) ^ k.val) _)))
    refine (congrArg
      (fun z : (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X (j + 1) ↦
        ((S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).d (j + 1) j).hom z)
      (tensorNormalizedChainComplexXIso_hom_single.{a, w, p} A S (j + 1) s x)).trans
        (hd.trans ?_)
    symm
    refine (congrArg
      (fun z : tensorNormalizedChainComplexX.{a, w, p} A S j ↦
        (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom.hom z)
      (tensorNormalizedBoundary_single.{a, w, p} A S j s x)).trans
        ((map_sum (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom.hom
          _ Finset.univ).trans ?_)
    apply Finset.sum_congr rfl
    intro k _
    exact (map_zsmul (tensorNormalizedChainComplexXIso.{a, w, p} A S j).hom.hom
      ((-1 : ℤ) ^ k.val) _).trans
      (congrArg
        (fun z : (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).X j ↦
          ((-1 : ℤ) ^ k.val) • z)
        (tensorNormalizedChainComplexXIso_hom_simplex.{a, w, p} A S (S.δ k s.val) x))
  · rw [tensorNormalizedDifferential_eq_zero.{a, w, p} A S i j hij,
      (S.normalizedChainComplex (ModuleCat.of ℤ (ULift.{max w p} A))).shape i j
        (fun h ↦ hij h.symm), comp_zero, zero_comp]

end SSet
end
