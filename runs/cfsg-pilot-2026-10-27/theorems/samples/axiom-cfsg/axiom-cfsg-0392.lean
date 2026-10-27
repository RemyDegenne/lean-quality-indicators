public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.LocalAnalysis.ComponentInitial

open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore)

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_map_oddCore_of_conj_eq_mul_of_transvection (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hn : 5 ≤ n) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype) {g : G} {y : L}
    (hyD : e y ∈ blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))
    (hy : IsInvolutionClass 1 (e y)) (hg : g⁻¹ * t * g = t * y) (hgy : g * y * g⁻¹ ∈ L)
    (hy' : IsInvolutionClass 1 (e ⟨g * y * g⁻¹, hgy⟩)) (htX : t ∈ centralizer (X : Set G))
    (hDX : ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (X : Set G))
    (hDq : CFSG.Open.IsQuasisimple
      (((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype))
    (hZD : Odd (Nat.card (center
      (((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype))))
    (hOutD : Group.IsSolvable (Outer
      ((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) ⧸
        center (((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
          L.subtype))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer (((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map
          e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ (((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
        L.subtype).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hDt : ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
      L.subtype ≤ centralizer ({t} : Set G) :=
    (map_subtype_le _).trans (le_centralizer_of_mem_centralizer htK.1)
  obtain ⟨-, y₁, hy₁D, hy₁, -, P, hP, hPD⟩ :=
    exists_le_centralizer_mulEquiv_of_conj_eq_mul_of_transvection hset hOut hn e ht hKt hab hXodd
      hXJ hyD hy hg hgy hy'
  exact not_normal_map_oddCore_centralizer_of_mulEquiv_of_odd_center htX ht hDX hDq hZD hOutD hDt
    hsyl hy₁D hy₁ (Or.inr rfl) hP hPD

end Setting
end CFSG.SeitzReduction.LinearPilot
end
