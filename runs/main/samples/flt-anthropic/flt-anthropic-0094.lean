namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq

set_option autoImplicit false

universe u

namespace RelVersch

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

section CT

open PiTensorProduct

open scoped TensorProduct

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (D : Type u) [CommRing D] [Algebra k D]

theorem sum_eq_zero_of_sh_stable {κ : Type u} {M : Type u} [AddCommGroup M] [Module k M]
    (t : (ZMod p → κ) → M) (ht : ∀ f, t (sh p f) = t f) :
    ∀ (S : Finset (ZMod p → κ)), (∀ f ∈ S, sh p f ∈ S) → (∀ f ∈ S, ¬ ∀ i, f i = f 0) → ∑ f ∈ S, t f = 0 := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hstab hnc
    rcases S.eq_empty_or_nonempty with hS | ⟨f₀, hf₀⟩
    · rw [hS, Finset.sum_empty]

    let O : Finset (ZMod p → κ) := Finset.image (fun m : ZMod p => shBy p m f₀) Finset.univ
    have hOS : O ⊆ S := by
      intro f hf
      rw [Finset.mem_image] at hf
      obtain ⟨m, -, rfl⟩ := hf
      exact shBy_induction p (fun g => g ∈ S) (fun g hg => hstab g hg) f₀ hf₀ m
    have htO : ∀ m : ZMod p, t (shBy p m f₀) = t f₀ :=
      fun m => shBy_induction p (fun g => t g = t f₀) (fun g hg => (ht g).trans hg) f₀ rfl m
    have hsumO : ∑ f ∈ O, t f = 0 := by
      rw [Finset.sum_image (fun k _ l _ hkl => shBy_injective p f₀ (hnc f₀ hf₀) hkl)]
      simp only [htO, Finset.sum_const, Finset.card_univ]
      rw [ZMod.card, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k p, zero_smul]
    have hO_ne : O.Nonempty := ⟨shBy p 0 f₀, Finset.mem_image.2 ⟨0, Finset.mem_univ _, rfl⟩⟩
    have hlt : S \ O ⊂ S := Finset.sdiff_ssubset hOS hO_ne
    have hstab' : ∀ f ∈ S \ O, sh p f ∈ S \ O := by
      intro f hf
      rw [Finset.mem_sdiff] at hf ⊢
      refine ⟨hstab f hf.1, fun hmem => hf.2 ?_⟩
      rw [Finset.mem_image] at hmem ⊢
      obtain ⟨m, -, hm⟩ := hmem
      refine ⟨m - 1, Finset.mem_univ _, ?_⟩
      funext i
      have := congr_fun hm (i - 1)
      simp only [sh, shBy, sub_add_cancel] at this
      simp only [shBy]
      rw [← this]; congr 1; ring
    have hnc' : ∀ f ∈ S \ O, ¬ ∀ i, f i = f 0 := fun f hf => hnc f (Finset.mem_sdiff.1 hf).1
    rw [← Finset.sum_sdiff hOS, ih _ hlt hstab' hnc', hsumO, add_zero]

end CT
end
end RelVersch
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nsmulPt_eq_of_mapPt_relFrobenius_eq
