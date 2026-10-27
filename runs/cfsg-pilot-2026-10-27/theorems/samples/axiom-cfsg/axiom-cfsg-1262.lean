public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3

open CFSG.GH74.Uniqueness.SU.K.R4.L82 CFSG.OrderReductions.FrattiniAutomorphisms

open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem Cfg.rdata {T : Sylow 2 H} {x : H} (h : Cfg H T x) {A : Subgroup H} (hAn : A.Normal)
    (hAel : Open.IsElemAbelian 2 A) (hAne : A ≠ ⊥) :
    ∃ y : H, RData T x A ((T : Subgroup H) ⊓ centralizer (A : Set H)) y := by
  have := hAn
  obtain ⟨hcard, hxA⟩ := h.normal_elemAb hAel hAne
  have hxx := h.mul_self_x
  have hA2 : IsPGroup 2 A := by
    have := isElementaryAbelian_of_isElemAbelian hAel
    exact IsElementaryAbelian.isPGroup 2 A
  have hAT : A ≤ (T : Subgroup H) := hA2.le_sylow_of_normal T
  set R : Subgroup H := (T : Subgroup H) ⊓ centralizer (A : Set H) with hRdef
  have hR2 : IsPGroup 2 R := T.isPGroup'.to_le inf_le_left
  have hAC : A ≤ centralizer (A : Set H) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (SU1.isElemAbelian_iff.mp hAel).1 b hb a ha
  have hAR : A ≤ R := le_inf hAT hAC
  have hxN : x ∈ normalizer (R : Set H) := mem_normalizer_inf h.xT
  have hxnR : ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp hxN r).mp hr
  have hxR : x ∉ R := by
    intro hx
    obtain ⟨a, haA, hxa⟩ := hxA
    apply hxa
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 a haA
    calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [← this]
      _ = a := by group
  have hTeq := sylow_eq_sup hcard T.isPGroup' h.xT hxA
  obtain ⟨y, hyN, hy3, hxy, hyA⟩ := exists_y h.cen hcard T hxx h.xT hxA
  have hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp hyN r).mp hr
  have hCy : ∀ r ∈ R, y * r * y⁻¹ = r → r = 1 := by
    intro r hr hyr
    by_contra hr1
    set X : Subgroup H := centralizer ({y} : Set H) ⊓ R with hX
    have hrX : r ∈ X := by
      refine Subgroup.mem_inf.mpr ⟨?_, hr⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      symm
      calc y * r = y * r * y⁻¹ * y := by group
        _ = r * y := by rw [hyr]
    have hXne : X ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hrX
      exact hr1 hrX
    have hX2 : IsPGroup 2 X := hR2.to_le inf_le_right
    have hxy' : x⁻¹ * y * x = y⁻¹ := by
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      rw [hxi]
      calc x * y * x = x * y * x⁻¹ := by rw [hxi]
        _ = y⁻¹ := hxy
    have hxX : ∀ s ∈ X, x * s * x⁻¹ ∈ X := by
      intro s hs
      refine Subgroup.mem_inf.mpr ⟨?_, hxnR s (Subgroup.mem_inf.mp hs).2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      symm
      have hs' := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hs).1
      calc y * (x * s * x⁻¹) = x * (x⁻¹ * y * x) * s * x⁻¹ := by group
        _ = x * y⁻¹ * s * x⁻¹ := by rw [hxy']
        _ = x * (y⁻¹ * s * y) * y⁻¹ * x⁻¹ := by group
        _ = x * s * y⁻¹ * x⁻¹ := by
          have : y⁻¹ * s * y = s := by
            calc y⁻¹ * s * y = y⁻¹ * (s * y) := by group
              _ = y⁻¹ * (y * s) := by rw [hs']
              _ = s := by group
          rw [this]
        _ = x * s * x⁻¹ * (x * y⁻¹ * x⁻¹) := by group
        _ = x * s * x⁻¹ * y := by
          have : x * y⁻¹ * x⁻¹ = y := by
            calc x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
              _ = y := by rw [hxy]; group
          rw [this]
    obtain ⟨u, huX, hu1, hu2, hxu⟩ := exists_fixed_involution hX2 hXne hxx hxX
    obtain ⟨a₀, ha₀A, ha₀1, hxa₀⟩ := exists_fixed_nonidentity A hcard x hxx
    have ha₀2 : a₀ * a₀ = 1 := by
      have := (SU1.isElemAbelian_iff.mp hAel).2 a₀ ha₀A
      rwa [pow_two] at this
    have huR : u ∈ R := (Subgroup.mem_inf.mp huX).2
    have hyu : y * u * y⁻¹ = u := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp huX).1
      calc y * u * y⁻¹ = u * y * y⁻¹ := by rw [this]
        _ = u := by group
    have hcomm : a₀ * u = u * a₀ :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp huR).2 a₀ ha₀A
    have hnot : a₀ ∉ zpowers u := by
      intro hmem
      rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers hu2 hmem with h1 | h1
      · exact ha₀1 h1
      · exact hyA a₀ ha₀A ha₀1 (by rw [h1]; exact hyu)
    obtain ⟨hVel, hVcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two
      (a := u) (y := a₀) (by rw [pow_two]; exact hu2) (by rw [pow_two]; exact ha₀2) hu1 hnot
      hcomm.symm
    have hVR : zpowers u ⊔ zpowers a₀ ≤ R :=
      sup_le (Subgroup.zpowers_le.mpr huR) (Subgroup.zpowers_le.mpr (hAR ha₀A))
    have hVx : ∀ v ∈ zpowers u ⊔ zpowers a₀, v * x = x * v := by
      have : zpowers u ⊔ zpowers a₀ ≤ centralizer ({x} : Set H) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          symm
          calc x * u = x * u * x⁻¹ * x := by group
            _ = u * x := by rw [hxu]
        · rw [Subgroup.mem_centralizer_singleton_iff]
          symm
          calc x * a₀ = x * a₀ * x⁻¹ * x := by group
            _ = a₀ * x := by rw [hxa₀]
      intro v hv
      exact (Subgroup.mem_centralizer_singleton_iff.mp (this hv))
    have hxV : x ∉ zpowers u ⊔ zpowers a₀ := fun hx => hxR (hVR hx)
    obtain ⟨hel, hc8⟩ := sup_zpowers_ge_eight hVel (by rw [hVcard]; norm_num) hxx hVx hxV
    exact h.no_E8 hel hc8 1 (by simpa using Subgroup.mem_sup_right (mem_zpowers x))
  have hrk := h.pRank_centralizer_inf_le_one hxR
  have hy3' := r3pow R hR2 y x hxx hxnR hyR hy3 hxy hCy hrk
  exact ⟨y, ⟨hAn, hAel, hcard, hAR, rfl, hR2, hxx, hxR, hxnR, hTeq, hxA, hyR, hy3, hxy, hyA, hCy,
    hrk, hy3'⟩⟩

end CFSG.GH74.Uniqueness.SU.K.R4
end
