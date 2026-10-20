@[expose] public section

open Bundle

open scoped ComplexConjugate

namespace VectorBundle

variable (𝕜 : Type*) [RCLike 𝕜] {B : Type*} [TopologicalSpace B]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module 𝕜 (E b)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

/-- A continuous Hermitian fiber metric on a finite-dimensional vector bundle over a paracompact
Hausdorff base, compatible with the existing fiber topologies. This is the `RCLike` version of
Hatcher's Hermitian remark following Proposition 1.2 of *Vector Bundles and K-Theory* (v2.2).
No inner-product structure on the normed model, nor any norm on the fibers, is assumed. -/
noncomputable def continuousHermitianMetric
    [T2Space B] [ParacompactSpace B] [FiniteDimensional 𝕜 F] :
    Bundle.ContinuousHermitianMetric 𝕜 F E := by
  classical
  let e := fun b : B ↦ trivializationAt F E b
  let hcover := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun b : B ↦ (e b).baseSet) (fun b ↦ (e b).open_baseSet) (by
      intro b _
      exact Set.mem_iUnion.mpr ⟨b, FiberBundle.mem_baseSet_trivializationAt F E b⟩)
  let ρ := hcover.choose
  have hρ := hcover.choose_spec
  let φ := fun (i b : B) ↦ ((ρ i b : ℝ) : 𝕜)
  have hφ_support (i : B) : tsupport (φ i) = tsupport (ρ i) := by
    change closure (Function.support (φ i)) = closure (Function.support (ρ i))
    congr 1
    ext b
    simp [φ, Function.mem_support]
  let m := Bundle.HermitianMetric.ofFiniteDimensional 𝕜 F
  let q := m.inner ()
  let t := fun (i b : B) ↦ (e i).weightedSesquilinearForm q (φ i) b
  let g := fun b : B ↦ ∑ i ∈ ρ.finsupport b, t i b
  have ht_zero (i b : B) (h : ρ i b = 0) : t i b = 0 := by
    ext v w
    simp [t, φ, h]
  have hg_sum (b : B) : (∑ᶠ i, t i b) = g b := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    exact (ρ.mem_finsupport b).2 fun h ↦ hi (ht_zero i b h)
  have hsymm (b : B) (v w : E b) : conj (g b w v) = g b v w := by
    simp only [g, sum_apply, Trivialization.weightedSesquilinearForm_apply, t, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [φ, map_mul, RCLike.conj_ofReal] using
      congrArg (fun r : 𝕜 ↦ φ i b * r)
        (m.symm () ((e i).continuousLinearMapAt 𝕜 b v)
          ((e i).continuousLinearMapAt 𝕜 b w))
  have hnonneg (u : F) : 0 ≤ RCLike.re (q u u) := m.re_inner_self_nonneg () u
  have hpos (b : B) (v : E b) (hv : v ≠ 0) : 0 < RCLike.re (g b v v) := by
    simp only [g, sum_apply, Trivialization.weightedSesquilinearForm_apply, t, map_sum,
      φ, RCLike.re_ofReal_mul]
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (ρ.nonneg i b) (hnonneg _)
    · obtain ⟨i, hi⟩ := ρ.exists_pos (Set.mem_univ b)
      refine ⟨i, ?_, ?_⟩
      · simpa only [PartitionOfUnity.mem_finsupport, Function.mem_support] using hi.ne'
      · have hbe : b ∈ (e i).baseSet := hρ i (subset_tsupport (ρ i) hi.ne')
        have hcoord : (e i).continuousLinearMapAt 𝕜 b v ≠ 0 := by
          rw [← Trivialization.coe_continuousLinearEquivAt_eq (e i) hbe]
          intro hzero
          exact hv (((e i).continuousLinearEquivAt 𝕜 b hbe).map_eq_zero_iff.mp hzero)
        exact mul_pos hi (m.pos () _ hcoord)
  refine
    { inner := g
      symm := hsymm
      pos := hpos
      isVonNBounded := fun b ↦ (g b).isVonNBounded_re_unit_sublevel_of_equiv
        (hsymm b) (hpos b) ((e b).continuousLinearEquivAt 𝕜 b
          (FiberBundle.mem_baseSet_trivializationAt F E b)).symm
      continuous := ?_ }
  have ht_cont (i : B) : Continuous
      (fun b ↦ TotalSpace.mk' (F →L⋆[𝕜] F →L[𝕜] 𝕜) b (t i b)) :=
    (e i).continuous_weightedSesquilinearForm q (φ i)
      (RCLike.continuous_ofReal.comp (ρ i).continuous) (by
        rw [hφ_support]
        exact hρ i)
  have ht_lf : LocallyFinite fun i : B ↦ {b | t i b ≠ 0} := by
    apply ρ.locallyFinite.subset
    intro i b hb
    change ρ i b ≠ 0
    intro h
    exact hb (ht_zero i b h)
  apply (VectorBundle.continuous_finsum_section 𝕜 ht_cont ht_lf).congr
  intro b
  exact congrArg (TotalSpace.mk' (F →L⋆[𝕜] F →L[𝕜] 𝕜) b) (hg_sum b)

end VectorBundle
end
