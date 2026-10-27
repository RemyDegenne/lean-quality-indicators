public section

namespace CFSG.Quasithin.H13.A6

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

section Lines

variable {ρ : ↥S.G1 →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (Fin 4 → ZMod 2)}

theorem Phi_w1_injective [IsMulCommutative ↥(conjClosure V S.G1)] (D : S.LineData ρ β) {g : G}
    (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (S.V2 : Set G)) (hgH : g ∉ S.G1)
    {x x' : Fin 4 → ZMod 2} (hx : pl (S.w1 β) x ≠ 0) (hx' : pl (S.w1 β) x' ≠ 0)
    (hxx : pl (S.w1 β) x ≠ pl (S.w1 β) x') :
    S.Phi ρ β (pl (S.w1 β) x) ≠ S.Phi ρ β (pl (S.w1 β) x') := by
  intro heq
  obtain ⟨k, hkC, hk⟩ := S.exists_nonconst D hgL hgN hgH
  apply hk
  have h12 := S.pl_w1_w2_ne_zero D.hβk
  have e1 : S.cls (S.cV 1 S.v0H) = S.cls S.v0H := by
    congr 1
    apply Subtype.ext
    simp [cV_coe]
  rw [← e1, ← S.Phi_spec D.hF D.hβk D.hβe, ← S.Phi_spec D.hF D.hβk D.hβe,
    S.rv_w1_of_C2 D hkC]
  have hr1 : S.rv ρ 1 (S.w1 β) = S.w1 β := by simp [rv]
  have hr2 : S.rv ρ 1 (S.w2 β) = S.w2 β := by simp [rv]
  rw [hr1, hr2]
  set y := S.rv ρ k (S.w2 β) with hy
  have hy0 : pl (S.w1 β) y ≠ 0 := by
    rw [hy, ← S.rv_w1_of_C2 D hkC, pl_rv]
    intro h0
    apply h12
    have := congrArg (fun z => (wedge2 ((ρ k⁻¹ : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec z) h0
    simp only [Matrix.mulVec_zero] at this
    rwa [← pl_rv, ← pl_rv, rv_inv_rv, rv_inv_rv] at this
  by_cases hyw : pl (S.w1 β) y = pl (S.w1 β) (S.w2 β)
  · rw [hyw]
  obtain ⟨d, hd⟩ := exists_basis_of_triple (fun s₀ s₁ s₂ hs => indep3_of_pl hx hx' hxx hs)
  obtain ⟨d', hd'⟩ := exists_basis_of_triple (fun s₀ s₁ s₂ hs => indep3_of_pl hy0 h12 hyw hs)
  obtain ⟨g'', e1', e2', e3', -⟩ := exists_GL_map4 hd hd'
  obtain ⟨k'', hk''⟩ := D.hρs g''
  have hrv : ∀ z, S.rv ρ k'' z = (g'' : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec z := fun z => by
    rw [rv, hk'']
  have h1 := S.Phi_equiv D.hF D.hρs D.hβk D.hβe k'' (S.w1 β) x
  have h2 := S.Phi_equiv D.hF D.hρs D.hβk D.hβe k'' (S.w1 β) x'
  rw [hrv, hrv, e1', e2'] at h1
  rw [hrv, hrv, e1', e3'] at h2
  rw [h1, h2, heq]

end Lines
end Setting4
end CFSG.Quasithin.H13.A6
end
