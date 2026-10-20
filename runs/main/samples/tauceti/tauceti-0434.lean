public section

namespace TauCeti.ContCohomology

open _root_.Subgroup

universe uG uH uM uN uK uA

section

variable {G : Type uG} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

@[simp]
theorem explicitConj1_mul (N : Subgroup G) [N.Normal] (g h : G) :
    explicitConj1 (M := M) N (g * h) =
      (explicitConj1 (M := M) N g).comp (explicitConj1 (M := M) N h) := by
  unfold explicitConj1
  have hφ : inverseConjugationHom N (g * h) =
      (inverseConjugationHom N h).comp (inverseConjugationHom N g) :=
    inverseConjugationHom_mul N g h
  have hf : DistribSMul.toAddMonoidHom M (g * h) =
      (DistribSMul.toAddMonoidHom M g).comp (DistribSMul.toAddMonoidHom M h) := by
    ext m
    simp [mul_smul]
  have hcomp := (inverseConjugationHom N h).comp_map_smul (inverseConjugationHom N g)
    (DistribSMul.toAddMonoidHom M h) (DistribSMul.toAddMonoidHom M g)
    (inverseConjugationHom_smul N h) (inverseConjugationHom_smul N g)
  have hcontg : Continuous (DistribSMul.toAddMonoidHom M g) := by
    exact (continuous_const_smul g).congr fun _ => rfl
  have hconth : Continuous (DistribSMul.toAddMonoidHom M h) := by
    exact (continuous_const_smul h).congr fun _ => rfl
  have hcontgh : Continuous (DistribSMul.toAddMonoidHom M (g * h)) := by
    exact (continuous_const_smul (g * h)).congr fun _ => rfl
  have hmap := explicitMap1_congr_of_eq (G := N) (M := M) (H := N) (N := M)
    (φ := inverseConjugationHom N (g * h))
    (ψ := (inverseConjugationHom N h).comp (inverseConjugationHom N g))
    (f := DistribSMul.toAddMonoidHom M (g * h))
    (q := (DistribSMul.toAddMonoidHom M g).comp (DistribSMul.toAddMonoidHom M h))
    (hf := hcontgh) (hq := hcontg.comp hconth)
    (hφ := inverseConjugationHom_smul N (g * h)) (hψ := hcomp)
    (hφeq := hφ) (hfeq := hf)
  exact hmap.trans (explicitMap1_comp N M N M (inverseConjugationHom N h)
      (DistribSMul.toAddMonoidHom M h) hconth
      (inverseConjugationHom_smul N h) N M (inverseConjugationHom N g)
      (DistribSMul.toAddMonoidHom M g) hcontg
      (inverseConjugationHom_smul N g) hcomp)

end
end TauCeti.ContCohomology
end
