public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem uCited_mem_normalizer_root_iff (h : UnitaryFieldData p f K) (i : Fin r)
    (g : ↥(hypSU h r ε)) :
    g ∈ Subgroup.normalizer (uCitedRoot h r ε (Pi.single (Sum.inl i) (1 : K)) :
        Set ↥(hypSU h r ε)) ↔
      ∃ c : K, c ≠ 0 ∧
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
            (Pi.single (Sum.inl i) (1 : K) : HypIndex r ε → K) =
          c • (Pi.single (Sum.inl i) (1 : K) : HypIndex r ε → K) := by
  set v : HypIndex r ε → K := Pi.single (Sum.inl i) (1 : K) with hvdef
  have h0 : v ≠ 0 := by
    intro hzero
    have := congrFun hzero (Sum.inl i)
    simpa [hvdef] using this
  have hinj : Function.Injective (Matrix.mulVec
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit (g : GL (HypIndex r ε) K))
  have hne : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ≠ 0 :=
    fun hh => h0 (hinj (by rw [hh, Matrix.mulVec_zero]))
  have hvv : hypForm h r ε v v = 0 := by
    simpa [hvdef] using hypForm_single_inl_self h i
  have hiso : hypForm h r ε
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v)
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) = 0 := by
    have h1 := hypForm_smul_smul h g v v
    simpa [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec, hvv] using h1
  have hmap : (uCitedRoot h r ε v).map (↑(MulAut.conj g)) =
      uCitedRoot h r ε
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) :=
    map_conj_uCitedRoot h g hvv
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hmap]
  constructor
  · intro heq
    obtain ⟨μ, hμ⟩ := exists_smul_of_uCitedRoot_eq h h0 hne hvv hiso heq.symm
    refine ⟨μ, ?_, hμ⟩
    intro hμ0
    exact hne (by rw [hμ, hμ0, zero_smul])
  · rintro ⟨c, hc0, hc⟩
    rw [hc, uCitedRoot_smul h hvv hc0]

end CFSG.LocalAnalysis.WeakClosure81
end
