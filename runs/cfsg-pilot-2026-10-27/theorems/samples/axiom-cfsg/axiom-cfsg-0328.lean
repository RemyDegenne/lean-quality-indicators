public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups LinearAlgebra.Projectivization

open CFSG.GorensteinWalter Projectivization

section BorelFixed

variable {k : Type*} [Field k] [Fintype k]

theorem borel_fixed_vector (hk : Fintype.card k = 4)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, k) W) [Fact ρ.IsIrreducible] {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type*} [Field E] [Finite E] [CharP E 2]
    (ιF : k →+* E) (ιD : EndRing ρ →+* E)
    (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor k E ({0, 1} : Finset ℕ)))) :
    ∃ w₀ : W, w₀ ≠ 0 ∧ ∀ g : SL(2, k), (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 → ρ g w₀ = w₀ := by
  classical
  let _ := ιF.toAlgebra
  have hF : Fintype.card k = 2 ^ 2 := by rw [hk]; norm_num
  have hJn : ∀ i ∈ ({0, 1} : Finset ℕ), i < 2 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega
  have hD : Finite (EndRing ρ) := finite_endRing ρ
  have hcard := natCard_fixW_rootGroup ρ hF b ιF ιD ({0, 1} : Finset ℕ) hJn Φ
  obtain ⟨w₁, hw₁fix, hw₁ne⟩ : ∃ w : W, (∀ t : k, ρ (uElt t) w = w) ∧ w ≠ 0 := by
    have h1 : 1 < Nat.card {w : W // ∀ t : k, ρ (uElt t) w = w} := by
      rw [hcard]
      exact Finite.one_lt_card
    obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩, hne⟩ := Finite.one_lt_card_iff_nontrivial.mp h1
    by_cases ha0 : a = 0
    · refine ⟨a', ha', fun h => hne (Subtype.ext (by simp [ha0, h]))⟩
    · exact ⟨a, ha, ha0⟩
  let ξ : W → ((↥({0, 1} : Finset ℕ) → Fin 2) → E) := fun w => Φ (fun i => ιD (b.equivFun w i))
  have hξinj : Function.Injective ξ := by
    intro w w' h
    have h1 := Φ.toLinearEquiv.injective h
    apply b.equivFun.injective
    funext i
    exact ιD.injective (congrFun h1 i)
  have hξ : ∀ (g : SL(2, k)) (w : W), ξ (ρ g w) = frobTensor k E ({0, 1} : Finset ℕ) g (ξ w) := by
    intro g w
    have hcoord : b.equivFun (ρ g w) = (matRep b g).mulVec (b.equivFun w) := by
      have := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
      rw [repD_apply] at this
      exact this.symm
    have h1 : (fun i => ιD (b.equivFun (ρ g w) i)) =
        matRepE b ιD g (fun i => ιD (b.equivFun w i)) := by
      rw [matRepE_apply, hcoord]
      funext i
      exact RingHom.map_mulVec ιD (matRep b g) (b.equivFun w) i
    show Φ (fun i => ιD (b.equivFun (ρ g w) i)) = _
    rw [h1]
    exact equiv_apply Φ g _
  have htorus : ∀ z : kˣ, ρ (dElt z) w₁ = w₁ := by
    intro z
    have hy : ∀ t : k, tensorRep k E (fun i : ↥({0, 1} : Finset ℕ) => (i : ℕ)) (uElt t) (ξ w₁) =
        ξ w₁ := fun t => by
      have := hξ (uElt t) w₁
      rw [hw₁fix t] at this
      exact this.symm
    obtain ⟨c, hc⟩ := (tensorRep_fixed_iff hF (fun i : ↥({0, 1} : Finset ℕ) => (i : ℕ))
      Subtype.val_injective (fun i => hJn i i.2) (ξ w₁)).mp hy
    have hz3 : (z : k) ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one (z : k) z.ne_zero
      rwa [hk] at this
    have hw : frobTensor k E ({0, 1} : Finset ℕ) (dElt z) (ξ w₁) = ξ w₁ := by
      rw [hc, map_smul, frobTensor_dElt_baseVec]
      have h3 : ∑ i ∈ ({0, 1} : Finset ℕ), 2 ^ i = 3 := by decide
      rw [h3, ← map_pow, hz3, map_one, one_smul]
    apply hξinj
    rw [hξ, hw]
  refine ⟨w₁, hw₁ne, fun g hg => ?_⟩
  have ha := borel_a_ne_zero g hg
  rw [borel_eq_mul g hg ha, map_mul, Module.End.mul_apply, htorus, hw₁fix]

end BorelFixed
end CFSG.QuasithinUnique.Setup.SL2Modules
end
