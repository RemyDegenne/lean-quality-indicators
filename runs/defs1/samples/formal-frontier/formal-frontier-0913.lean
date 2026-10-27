set_option autoImplicit false

set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

namespace CorestrictionTransversal

variable (X : TopRep.{max v w} k G)

attribute [local instance] jointlyContinuous_mackeyStabilizer

/-- Double-coset representatives followed by stabilizer transversals assemble
to a right transversal of `H` in the ambient group. Its carrier computes as
the range of assembled representatives. -/
@[expose]
noncomputable def mackeyAssembledRightTransversal (H K : OpenSubgroup G)
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal) :
    H.toSubgroup.RightTransversal := by
  let S : Set G := Set.range (mackeyAssembledRepresentative H K T)
  refine ⟨S, Subgroup.isComplement_iff_existsUnique.mpr ?_⟩
  intro g
  let q := DoubleCoset.mk H.toSubgroup K.toSubgroup g
  obtain ⟨h₀, hh₀, b₀, hb₀, hout⟩ :=
    DoubleCoset.mk_out_eq_mul H.toSubgroup K.toSubgroup g
  let p := (T q).2.equiv (⟨b₀⁻¹, K.inv_mem hb₀⟩ : K)
  let l := p.1
  let t := p.2
  have hlH : q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹ ∈ H :=
    l.2
  let h : H := ⟨h₀⁻¹ *
    (q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹),
      H.mul_mem (H.inv_mem hh₀) hlH⟩
  let s : Subtype S :=
    ⟨q.out * (t.1 : G), ⟨⟨q, t⟩, rfl⟩⟩
  have hdecomp : (h : G) * s.1 = g := by
    change
      (h₀⁻¹ *
          (q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹)) *
          (q.out * (t.1 : G)) = g
    have hp := (T q).2.equiv_fst_mul_equiv_snd (⟨b₀⁻¹, K.inv_mem hb₀⟩ : K)
    change ((l : mackeyOpenStabilizer H K q.out) : K) * t.1 =
      (⟨b₀⁻¹, K.inv_mem hb₀⟩ : K) at hp
    have hpG : (((l : mackeyOpenStabilizer H K q.out) : K) : G) *
        (t.1 : G) = (b₀ : G)⁻¹ := by
      have hpG' := congrArg (fun z : K => (z : G)) hp
      change (((l : mackeyOpenStabilizer H K q.out) : K) : G) *
        (t.1 : G) = (b₀ : G)⁻¹ at hpG'
      exact hpG'
    calc
      _ = h₀⁻¹ * q.out *
          ((((l : mackeyOpenStabilizer H K q.out) : K) : G) * (t.1 : G)) := by
        group
      _ = h₀⁻¹ * q.out * (b₀ : G)⁻¹ := by rw [hpG]
      _ = h₀⁻¹ * (h₀ * g * b₀) * (b₀ : G)⁻¹ := by rw [hout]
      _ = g := by group
  refine ⟨(h, s), hdecomp, ?_⟩
  rintro ⟨h₁, s₁⟩ hs₁
  obtain ⟨⟨q₁, t₁⟩, ht₁⟩ := s₁.2
  have heq : (h₁ : G) *
      (q₁.out * (t₁.1 : G)) = g := by
    change (h₁ : G) *
      mackeyAssembledRepresentative H K T ⟨q₁, t₁⟩ = g
    rw [ht₁]
    exact hs₁
  have hq : q₁ = q := by
    calc
      q₁ = DoubleCoset.mk H.toSubgroup K.toSubgroup q₁.out :=
        (DoubleCoset.out_eq' q₁).symm
      _ = DoubleCoset.mk H.toSubgroup K.toSubgroup
          (q₁.out * (t₁.1 : G)) := by
        symm
        exact DoubleCoset.mk_mul_mem t₁.1 q₁.out
      _ = DoubleCoset.mk H.toSubgroup K.toSubgroup
          ((h₁ : G) * (q₁.out * (t₁.1 : G))) := by
        symm
        exact DoubleCoset.mk_mem_mul h₁ _
      _ = DoubleCoset.mk H.toSubgroup K.toSubgroup g := congrArg _ heq
      _ = q := rfl
  subst q₁
  let lK : K := t.1 * t₁.1⁻¹
  have hlH₁ : q.out * ((lK : K) : G) * q.out⁻¹ ∈ H := by
    have hrel : q.out * ((lK : K) : G) * q.out⁻¹ =
        (h : G)⁻¹ * (h₁ : G) := by
      dsimp [lK]
      change q.out * ((t.1 : G) * (t₁.1 : G)⁻¹) * q.out⁻¹ =
        (h : G)⁻¹ * (h₁ : G)
      have hmain : (h₁ : G) * (q.out * (t₁.1 : G)) =
          (h : G) * (q.out * (t.1 : G)) := by
        rw [heq]
        exact hdecomp.symm
      calc
        _ = (h : G)⁻¹ * ((h : G) * (q.out * (t.1 : G))) *
            (t₁.1 : G)⁻¹ * q.out⁻¹ := by group
        _ = (h : G)⁻¹ * ((h₁ : G) * (q.out * (t₁.1 : G))) *
            (t₁.1 : G)⁻¹ * q.out⁻¹ := by rw [hmain]
        _ = (h : G)⁻¹ * (h₁ : G) := by group
    rw [hrel]
    exact H.mul_mem (H.inv_mem h.2) h₁.2
  let l₁ : mackeyOpenStabilizer H K q.out := ⟨lK, hlH₁⟩
  have hpair :
      (l₁, t₁) =
        (1, t) := by
    apply (T q).2.1
    change lK * t₁.1 = (1 : K) * t.1
    simp only [lK, one_mul]
    group
  have htt : t₁ = t := congrArg Prod.snd hpair
  have hss : s₁ = s := by
    apply Subtype.ext
    change s₁.1 = q.out * (t.1 : G)
    calc
      s₁.1 = mackeyAssembledRepresentative H K T ⟨q, t₁⟩ := ht₁.symm
      _ = mackeyAssembledRepresentative H K T ⟨q, t⟩ := by rw [htt]
      _ = q.out * (t.1 : G) := rfl
  have hhh : h₁ = h := by
    apply Subtype.ext
    apply mul_right_cancel (b := s₁.1)
    rw [hs₁, hss]
    exact hdecomp.symm
  exact Prod.ext hhh hss

end CorestrictionTransversal
end ContinuousCohomology
end
end
