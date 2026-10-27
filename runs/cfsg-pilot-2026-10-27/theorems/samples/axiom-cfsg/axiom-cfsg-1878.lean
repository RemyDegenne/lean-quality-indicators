public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

namespace ExcUntw

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms

open scoped MatrixGroups

section F4

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof CFSG.RankThree.PartOne.KE CFSG.Timmesfeld

open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi exists_b2Hom hom_block_eq blk spBlock)

open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  symplecticBlockStandardPair_le_sup)

open CFSG.SeitzReduction.SymplecticPilot (isSimpleGroup_commutator_statedSp_two)

open scoped Matrix

theorem innerRecogOver_f4_C3_fam {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 0 < f) (hK : Nat.card K = p ^ f) :
    InnerRecogOver p (p ^ f) ↥(subsystemGroup .F4 K f4LeviC3) := by
  classical
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨ψ0, hψ0a, hψ0b⟩ : ∃ ψ : SL(3, K) →* adjointGroup .F4 K,
      ψ.comp (blk K 0) = ρF (f4Node 2) ∧ ψ.comp (blk K 1) = ρF (f4Node 3) := by
    obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (i := f4Node 2) (j := f4Node 3)
      (k := f4Node 1) f4Node_two_ne_three f4_cartan_23 f4_cartan_32 f4_sl3_witness
    exact ⟨emb, sl3_comp_blk hv (hρFv (f4Node 2)) (hρFv (f4Node 3))⟩
  obtain ⟨φ, hφl, hφs⟩ : ∃ φ : StatedSp 2 K →* adjointGroup .F4 K,
      φ.comp (spBlock K 1) = ρF (f4Node 1) ∧ φ.comp (spBlock K 0) = ρF (f4Node 2) := by
    obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
      exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
    obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
    exact ⟨φ, hb1, hb0⟩
  obtain ⟨Ψ, hker, hrange, -⟩ := ClassicalInvolution.Q3.Q3V.weakCT_symplectic_subgroup_of_family
    hadm le_rfl hK (G := adjointGroup .F4 K)
    (fun k => rankOne (f4Datum K).rootGroup (c3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact (f4_commutes_rankOne_one_three b hb a ha).symm)
    (fun k => ρF (c3Node k)) (fun k => ⟨hρFi _, hρFr _⟩)
    (fun _ _ => ψ0)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0a)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0b)
    φ hφl hφs
  refine innerRecogOver_of_spRange hp hf hK (by norm_num) (by simp)
    ((adjointGroup .F4 K).subtype.comp Ψ) ?_ ?_
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_c3]

end F4
end ExcUntw
end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
end
