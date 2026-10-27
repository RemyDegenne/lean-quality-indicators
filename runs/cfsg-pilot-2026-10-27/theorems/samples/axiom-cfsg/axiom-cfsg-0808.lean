public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace SuzukiAut

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

open CFSG.BenderSuzuki.PFAppendixIII

variable (m : ℕ)

theorem invDichotomyAt_rootSub (hm : 0 < m) [Finite (SuzukiMatrixGroup m)]
    (S : Sylow 2 (SuzukiMatrixGroup m)) (hS : (S : Subgroup (SuzukiMatrixGroup m)) = rootSub m) :
    InvDichotomyAt (S : Subgroup (SuzukiMatrixGroup m)) := by
  obtain ⟨hNR, hcard⟩ := normalizer_and_card_sylow m hm
  obtain ⟨hSE, -, -, -⟩ := benderBorel_sylowCenter (bender_suzukiMatrixGroup_borel m hm) S
  have : IsSimpleGroup (SuzukiMatrixGroup m) := isSimpleGroup_suzukiMatrixGroup m hm
  have hHN : torusSub m ≤ Subgroup.normalizer (((S : Subgroup (SuzukiMatrixGroup m))) : Set _) := by
    rw [hS]
    exact torusSub_le_normalizer m
  rw [← hS] at hNR hcard
  have hS₁ : weyl m • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer m
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  have hHN₁ : torusSub m ≤
      Subgroup.normalizer
        ((((weyl m • S : Sylow 2 _)) : Subgroup (SuzukiMatrixGroup m)) : Set _) := by
    intro h hh
    obtain ⟨x, rfl⟩ := (mem_torusSub m hm).mp hh
    rw [Omega.mem_normalizer_conj_smul_iff, weyl_inv_conj_torus]
    exact hHN (torus_mem m x⁻¹)
  apply invDichotomyAt_of_twisted hSE hcard hS₁
  intro α' hα'α' hα'S hα'S₁ _ _ _
  left
  have hα'R : ∀ s ∈ rootSub m, α' s ∈ rootSub m := by
    intro s hs
    rw [← hS] at hs ⊢
    exact InvInner.apply_mem_of_smul_eq hα'S hs
  have hα'H : ∀ x : (BinaryGaloisField (2 * m + 1))ˣ, ∃ x', α' (torus m x) = torus m x' := by
    intro x
    have h1 := Omega.mem_normalizer_smul (α := α') (hHN (torus_mem m x))
    have h2 := Omega.mem_normalizer_smul (α := α') (hHN₁ (torus_mem m x))
    rw [hα'S] at h1
    rw [hα'S₁] at h2
    exact (mem_torusSub m hm).mp
      (Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2)
  have hcentral := centralizes_root m hm α' hα'R
    (centralizes_center_of_involutive m hm α' hα'α' hα'R hα'H) hα'H
  intro s hs
  rw [hS] at hs
  obtain ⟨a, b, rfl⟩ := (mem_rootSub m).mp hs
  exact hcentral a b

end SuzukiAut
end Bender
end CFSG.ComponentClassification.AschbacherToolkit
end
