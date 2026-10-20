namespace P2MW.S_Module_quasiIso_baseChange_of_quasiIso_of_flat

set_option autoImplicit false

universe u

open TensorProduct

namespace QisoBC

variable {S : Type u} [CommRing S]

variable (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module S (K i)]

variable (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module S (C i)]

scoped instance instACG : ∀ i, AddCommGroup (Cone K C i)
  | 0 => inferInstanceAs (AddCommGroup (K 0))
  | i + 1 => inferInstanceAs (AddCommGroup (K (i + 1) × C i))

scoped instance instMod : ∀ i, Module S (Cone K C i)
  | 0 => inferInstanceAs (Module S (K 0))
  | i + 1 => inferInstanceAs (Module S (K (i + 1) × C i))

variable (δ : ∀ i, K i →ₗ[S] K (i + 1)) (d : ∀ i, C i →ₗ[S] C (i + 1)) (φ : ∀ i, K i →ₗ[S] C i)

theorem D_comp_D (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i) : ∀ i, D K C δ d φ (i + 1) ∘ₗ D K C δ d φ i = 0
  | 0 => by
      refine LinearMap.ext fun x => ?_
      show ((δ 1 (δ 0 x), φ 1 (δ 0 x) - d 0 (φ 0 x)) : K 2 × C 1) = 0
      have h1 := congrArg (fun f => f x) (hδδ 0)
      have h2 := congrArg (fun f => f x) (hφ 0)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 h2
      rw [h1, h2, sub_self]; rfl
  | i + 1 => by
      refine LinearMap.ext fun z => ?_
      show ((δ (i + 2) (δ (i + 1) z.1), φ (i + 2) (δ (i + 1) z.1) - d (i + 1) (φ (i + 1) z.1 - d i z.2)) :
        K (i + 3) × C (i + 2)) = 0
      have h1 := congrArg (fun f => f z.1) (hδδ (i + 1))
      have h2 := congrArg (fun f => f z.1) (hφ (i + 1))
      have h3 := congrArg (fun f => f z.2) (hdd i)
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h1 h2 h3
      rw [h1, map_sub, h3, h2, sub_zero, sub_self]; rfl

end QisoBC
end P2MW.S_Module_quasiIso_baseChange_of_quasiIso_of_flat
