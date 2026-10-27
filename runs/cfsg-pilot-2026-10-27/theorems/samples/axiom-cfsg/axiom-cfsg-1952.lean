public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem eq_of_ker_le_of_actsTv {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    [FiniteDimensional (ZMod 2) N] {f g : N →ₗ[ZMod 2] N}
    (hk : LinearMap.ker f ≤ LinearMap.ker g) {A B F : Submodule (ZMod 2) N}
    (hfA : A.map f = F) (hgA : A.map g = F) (h2 : 2 ≤ finrank (ZMod 2) F)
    (htv : ∀ (c : F) (μ : Dual (ZMod 2) F), μ c = 0 → ∃ ρ : N →ₗ[ZMod 2] N,
      (∀ x, f (ρ x) = ρ (f x)) ∧ (∀ x, g (ρ x) = ρ (g x)) ∧
        ∀ w : F, ρ w = (w : N) + μ w • (c : N))
    {ρB : N →ₗ[ZMod 2] N} (hfB : ∀ x, f (ρB x) = ρB (f x)) (hgB : ∀ x, g (ρB x) = ρB (g x))
    (hB : B ≤ A.map ρB) (hAB : A ⊔ B = ⊤) : g = f := by
  obtain ⟨θ, hθ⟩ := exists_range_lift f g hk
  have hθ' : ∀ (v : N) (hv : v ∈ LinearMap.range f) (α : N), f α = v → θ ⟨v, hv⟩ = g α := by
    rintro v hv α rfl
    exact hθ α hv
  have hFr : F ≤ LinearMap.range f := hfA ▸ LinearMap.map_le_range
  have hθF : ∀ w : F, θ ⟨w, hFr w.2⟩ ∈ F := by
    intro w
    obtain ⟨α, hα, hαw⟩ : (w : N) ∈ A.map f := hfA.symm ▸ w.2
    rw [hθ' _ _ α hαw, ← hgA]
    exact Submodule.mem_map_of_mem hα
  let θF : F →ₗ[ZMod 2] F := LinearMap.codRestrict F (θ ∘ₗ Submodule.inclusion hFr) hθF
  have hθFv : ∀ w : F, ((θF w : F) : N) = θ ⟨w, hFr w.2⟩ := fun _ => rfl
  have hcomm : ∀ (c : F) (μ : Dual (ZMod 2) F), μ c = 0 →
      ∀ w, θF (w + μ w • c) = θF w + μ (θF w) • c := by
    intro c μ hμ w
    obtain ⟨ρ, hρf, hρg, hρF⟩ := htv c μ hμ
    obtain ⟨y, hy⟩ := hFr w.2
    apply Subtype.ext
    calc ((θF (w + μ w • c) : F) : N)
        = θ ⟨((w + μ w • c : F) : N), hFr (w + μ w • c).2⟩ := rfl
      _ = g (ρ y) := hθ' _ _ (ρ y) (by rw [hρf, hy, hρF w]; rfl)
      _ = ρ (g y) := hρg y
      _ = ρ ((θF w : F) : N) := by rw [hθFv, hθ' _ (hFr w.2) y hy]
      _ = ((θF w : F) : N) + μ (θF w) • (c : N) := hρF (θF w)
      _ = ((θF w + μ (θF w) • c : F) : N) := rfl
  obtain ⟨a, ha⟩ := eq_smul_of_commute_actsTv h2 θF hcomm
  have hgf : ∀ α ∈ A, g α = a • f α := by
    intro α hα
    have hw : f α ∈ F := hfA ▸ Submodule.mem_map_of_mem hα
    have h1 := congrArg (fun φ : F →ₗ[ZMod 2] F => ((φ ⟨f α, hw⟩ : F) : N)) ha
    exact ((hθFv ⟨f α, hw⟩).trans (hθ' _ _ α rfl)).symm.trans h1
  have hA1 : ∀ α ∈ A, g α = f α := by
    refine (zmod2_eq_zero_or_eq_one a).elim (fun h0 => ?_) (fun h1 => ?_)
    · exfalso
      have hF0 : F = ⊥ := by
        rw [← hgA, eq_bot_iff]
        rintro _ ⟨α, hα, rfl⟩
        rw [Submodule.mem_bot, hgf α hα, h0, zero_smul]
      rw [hF0, finrank_bot] at h2
      omega
    · intro α hα
      rw [hgf α hα, h1, one_smul]
  have hB1 : ∀ β ∈ B, g β = f β := by
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := hB hβ
    rw [hgB, hfB, hA1 α hα]
  refine LinearMap.ext fun y => ?_
  have hy : y ∈ A ⊔ B := hAB ▸ Submodule.mem_top
  obtain ⟨α, hα, β, hβ, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, map_add, hA1 α hα, hB1 β hβ]

end CFSG.LargeExtraspecial.S8
end
