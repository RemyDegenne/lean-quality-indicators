public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

open scoped Matrix

namespace RootOne

variable {G : Type} [Group G] {D : Set G}

namespace ModConf

variable {a d x y : G} {C : LineConf D a d x y} {K : Type*} [Field K]
  {φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K}
  {θ₀ θ₁ : (Fin 2 → K) → G} (M : ModConf C φ θ₀ θ₁)

include M

theorem exists_matrix {s : G}
    (hsX : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, s * g * s⁻¹ ∈ rootGroup D x ⊔ rootGroup D y)
    (hsT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, s * t * s⁻¹ ∈ rootGroup D a ⊔ rootGroup D d)
    (hsa : ∀ t ∈ rootGroup D a, Commute s t) :
    ∃ c β : K, β ≠ 0 ∧ ∀ v, s * θ₀ v * s⁻¹ = θ₀ (!![1, c; 0, β] *ᵥ v) := by
  classical
  have hθ := M.nat₀
  have hex : ∀ v, ∃ w, θ₀ w = s * θ₀ v * s⁻¹ := fun v => (M.range₀ _).1 (hsT _ (M.θ₀_mem v))
  choose f hf using hex
  have hfadd : ∀ v w, f (v + w) = f v + f w := by
    intro v w
    apply hθ.injective
    rw [hf, hθ.map_add, hθ.map_add, hf, hf]
    group
  have hf0 : ∀ r : K, f ![r, 0] = ![r, 0] := by
    intro r
    apply hθ.injective
    rw [hf, (hsa _ (M.axis_a r)).eq, mul_inv_cancel_right]
  have hfX : ∀ (g : ↥(rootGroup D x ⊔ rootGroup D y)) v,
      f ((φ g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        (φ ⟨s * g * s⁻¹, hsX g g.2⟩ : Matrix (Fin 2) (Fin 2) K) *ᵥ f v := by
    intro g v
    apply hθ.injective
    rw [hf, hθ.map_mulVec, hθ.map_mulVec, hf]
    group
  have hupper : ∀ r : K, ∃ σ : K, ∀ v,
      f ((RankOne.upperElt K r : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        (RankOne.upperElt K σ : Matrix (Fin 2) (Fin 2) K) *ᵥ f v := by
    intro r
    have hgx : ((φ.symm (RankOne.upperElt K r) : ↥(rootGroup D x ⊔ rootGroup D y)) : G) ∈
        rootGroup D x := by
      refine (ARS.NaturalModule.coe_mem_iff M.map_x _).2 ?_
      rw [MulEquiv.apply_symm_apply]
      exact (RankOne.mem_upperUnipotent_iff K).2 ⟨r, rfl⟩
    set g := φ.symm (RankOne.upperElt K r) with hg
    have hsg : s * g * s⁻¹ ∈ rootGroup D x := by
      refine M.mem_rootGroup_x_of_commute (hsX g g.2) fun t ht => ?_
      have h1 := (Commute.conj_iff s).2
        (commute_of_mem_rootGroup_of_commute' C.ha hgx ht C.hax.symm)
      rwa [(hsa t ht).eq, mul_inv_cancel_right] at h1
    obtain ⟨σ, hσ⟩ := (RankOne.mem_upperUnipotent_iff K).1
      ((ARS.NaturalModule.coe_mem_iff M.map_x ⟨_, hsX g g.2⟩).1 hsg)
    refine ⟨σ, fun v => ?_⟩
    have h1 := hfX g v
    rwa [hσ, hg, MulEquiv.apply_symm_apply] at h1
  have hf01 : ∀ w : K, f ![0, w] = ![f ![0, w] 0, f ![0, w] 1] := fun w => Higman.eq_vec _
  have hup : ∀ r : K, ∃ σ : K, ∀ w : K, r * w = σ * f ![0, w] 1 := by
    intro r
    obtain ⟨σ, hσ⟩ := hupper r
    refine ⟨σ, fun w => ?_⟩
    have h1 := hσ ![0, w]
    rw [Higman.upperElt_mulVec, Higman.upperElt_mulVec] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] at h1
    rw [Higman.vec_eq_add, hfadd, hf0] at h1
    have h2 := congrFun h1 0
    simp only [Pi.add_apply, Matrix.cons_val_zero] at h2
    linear_combination h2
  set β := f ![0, 1] 1 with hβ
  set c := f ![0, 1] 0 with hc
  have hβ0 : β ≠ 0 := by
    obtain ⟨σ, hσ⟩ := hup 1
    intro h0
    have := hσ 1
    rw [← hβ, h0, mul_zero, one_mul] at this
    exact one_ne_zero this
  have hδ : ∀ w : K, f ![0, w] 1 = β * w := by
    obtain ⟨σ, hσ⟩ := hup β
    have hσ1 : σ = 1 := by
      have := hσ 1
      rw [← hβ, mul_one] at this
      have := mul_right_cancel₀ hβ0 (this.symm.trans (one_mul β).symm)
      exact this
    intro w
    rw [hσ w, hσ1, one_mul]
  set g := φ.symm (RankOne.lowerElt K 1) with hg
  set A := (φ ⟨s * g * s⁻¹, hsX g g.2⟩ : Matrix (Fin 2) (Fin 2) K) with hA
  have hlow : ∀ v, f ((RankOne.lowerElt K 1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = A *ᵥ f v := by
    intro v
    have h1 := hfX g v
    rwa [hg, MulEquiv.apply_symm_apply] at h1
  have hA10 : A 1 0 = β := by
    have h1 := hlow ![1, 0]
    rw [Higman.lowerElt_mulVec, hf0] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, add_zero] at h1
    rw [Higman.vec_eq_add, hfadd, hf0] at h1
    have h2 := congrFun h1 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2
    rw [← h2]
  have hγ : ∀ w : K, f ![0, w] 0 = c * w := by
    have key : ∀ w : K, f ![0, w] 0 = (1 - A 1 1) * w := by
      intro w
      have h1 := hlow ![0, w]
      rw [Higman.lowerElt_mulVec] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add] at h1
      have h2 := congrFun h1 1
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2
      rw [hδ, hA10] at h2
      have h3 : β * (f ![0, w] 0 - (1 - A 1 1) * w) = 0 := by linear_combination -h2
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hβ0
      · linear_combination h
    intro w
    rw [key w, hc, key 1, mul_one]
  refine ⟨c, β, hβ0, fun v => ?_⟩
  rw [← hf]
  congr 1
  rw [Higman.eq_vec v, Higman.vec_eq_add, hfadd, hf0, hf01, hγ, hδ]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end ModConf
end RootOne
end CFSG.Timmesfeld.Bridge
end
