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

namespace Bad3

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad3 D τ)

include B

theorem tauBil_apply_apply {r : S.O} (hr : r ∈ Rbar S g t) {x y : S.Qt}
    (hx : x ∈ Wt S g t) (hy : y ∈ Wt S g t) :
    tauBil S τ ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) y) =
      tauBil S τ x y := by
  obtain ⟨ν, hνdef⟩ : ∃ ν : S.O, ν = r⁻¹ * τ * r⁻¹⁻¹ * τ⁻¹ := ⟨_, rfl⟩
  have hν : ν ∈ Nbar S g t := by
    rw [hνdef]
    exact comm_mem_Nbar_of_fix H B.τM B.τt B.fix_Vt (inv_mem hr)
  have hτx : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ Wt S g t :=
    apply_mem_Wt_of_commute H C ht ht1 hVQ B.τt hx
  have hc := D.hN ν hν _ hτx
  have h1 : τ * r = r * (ν * τ) := by rw [hνdef]; group
  have e : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) x = (r : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) + ((ν : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) - (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x)) := by
    rw [← coe_mul_apply τ r, h1, coe_mul_apply, coe_mul_apply, map_add, map_sub, map_sub]
    abel
  rw [tauBil_apply, tauBil_apply, e,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup r.2, polar_add_left,
    mem_Wt.mp hy _ hc, add_zero]

end Bad3
end CFSG.LargeExtraspecial.S8
end
