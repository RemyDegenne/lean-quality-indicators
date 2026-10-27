open CFSG

open scoped Pointwise TensorProduct commutatorElement IsMulCommutative

universe u37

universe u38

universe u

section Theorem310

universe u310G u310M

variable {G : Type u310G} [Group G] [Finite G] (K R : Subgroup G)

variable {M : Type u310M} [Group M] [Finite M] [MulDistribMulAction G M] [Nontrivial M]

public theorem CFSG.minimalInvariantNormal_solvable_exists_isElementaryAbelian
    {G A : Type*} [Group G] [Finite G] [Group A] [MulDistribMulAction A G]
    (M : Subgroup G) [M.Normal] [IsInvariant A G M] [Group.IsSolvable (↥M)]
    (hM_ne_bot : M ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → IsInvariant A G K → K ≠ ⊥ → K ≤ M → K = M) :
    ∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p (↥M) := by
  classical
  have : Nontrivial (↥M) := (Subgroup.nontrivial_iff_ne_bot M).2 hM_ne_bot
  have hcomm_lt : ⁅M, M⁆ < M := by
    have hlt : commutator (↥M) < (⊤ : Subgroup (↥M)) :=
      Group.IsSolvable.commutator_lt_top_of_nontrivial (G := (↥M))
    have hlt' : (commutator (↥M)).map M.subtype <
        (⊤ : Subgroup (↥M)).map M.subtype :=
      (Subgroup.map_subtype_lt_map_subtype (G' := M) (H := commutator (↥M))
        (K := (⊤ : Subgroup (↥M)))).mpr hlt
    have htop_map : (⊤ : Subgroup (↥M)).map M.subtype = M := by
      simpa [MonoidHom.range_eq_map] using (M.range_subtype : M.subtype.range = M)
    simpa [Subgroup.map_subtype_commutator, htop_map] using hlt'
  have hcomm_inv : IsInvariant A G ⁅M, M⁆ :=
    isInvariant_commutator (A := A) (G := G) M M
  have hcomm_eq_bot : ⁅M, M⁆ = ⊥ := by
    by_contra hne
    have hcomm_eq : ⁅M, M⁆ = M :=
      hmin ⁅M, M⁆ (inferInstance : (⁅M, M⁆).Normal) hcomm_inv hne
        (Subgroup.commutator_le_left (H₁ := M) (H₂ := M))
    exact (ne_of_lt hcomm_lt) hcomm_eq
  have hM_le_centralizer : M ≤ Subgroup.centralizer (M : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := M) (H₂ := M)).mp
      hcomm_eq_bot
  have : IsMulCommutative (↥M) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := M)).mp hM_le_centralizer
  have hcard_ne_one : Nat.card (↥M) ≠ 1 := by
    have : 1 < Nat.card (↥M) :=
      (Subgroup.one_lt_card_iff_ne_bot (H := M)).2 hM_ne_bot
    exact ne_of_gt this
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (↥M)) hcard_ne_one
  have : Fact p.Prime := ⟨hp_prime⟩
  let P : Sylow p (↥M) := default
  have hP_ne_bot : (P : Subgroup (↥M)) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := (↥M)) (p := p) P hp_dvd
  have hP_normal : (P : Subgroup (↥M)).Normal := by infer_instance
  have : (P : Subgroup (↥M)).Characteristic :=
    Sylow.characteristic_of_normal (G := (↥M)) (p := p) P hP_normal
  have : ((P : Subgroup (↥M)).map M.subtype).Normal := by infer_instance
  have : IsInvariant A (↥M) (P : Subgroup (↥M)) :=
    isInvariant_of_characteristic (A := A) (G := ↥M) (P : Subgroup (↥M))
  have hPmap_inv : IsInvariant A G ((P : Subgroup (↥M)).map M.subtype) :=
    isInvariant_map_subtype (A := A) (G := G) M (P : Subgroup (↥M))
  have hPmap_ne_bot : (P : Subgroup (↥M)).map M.subtype ≠ ⊥ := by
    intro hbot
    have : (P : Subgroup (↥M)) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := (P : Subgroup (↥M))) (f := M.subtype)
        M.subtype_injective).1 hbot
    exact hP_ne_bot this
  have hPmap_eq_M : (P : Subgroup (↥M)).map M.subtype = M :=
    hmin ((P : Subgroup (↥M)).map M.subtype)
      (inferInstance : ((P : Subgroup (↥M)).map M.subtype).Normal)
      hPmap_inv hPmap_ne_bot (Subgroup.map_subtype_le (H := M) (K := (P : Subgroup (↥M))))
  have hMpgroup : IsPGroup p (↥M) := by
    have h : IsPGroup p (↥((P : Subgroup (↥M)).map M.subtype)) :=
      P.isPGroup'.map M.subtype
    simpa using (hPmap_eq_M ▸ h)
  have : Fact (IsPGroup p (↥M)) := ⟨hMpgroup⟩
  let Ω : Subgroup (↥M) := omega₁ (G := (↥M)) (p := p)
  have hΩ_char : Ω.Characteristic := by
    simpa [Ω] using (omega₁_characteristic (G := (↥M)) (p := p))
  have : Ω.Characteristic := hΩ_char
  have : (Ω.map M.subtype).Normal := by infer_instance
  have : IsInvariant A (↥M) Ω :=
    isInvariant_of_characteristic (A := A) (G := ↥M) Ω
  have hΩmap_inv : IsInvariant A G (Ω.map M.subtype) :=
    isInvariant_map_subtype (A := A) (G := G) M Ω
  have hΩmap_ne_bot : Ω.map M.subtype ≠ ⊥ := by
    simpa [Ω] using omega₁_map_subtype_ne_bot (M := M) (p := p) hp_dvd
  have hΩmap_eq_M : Ω.map M.subtype = M :=
    hmin (Ω.map M.subtype) (inferInstance : (Ω.map M.subtype).Normal)
      hΩmap_inv hΩmap_ne_bot (Subgroup.map_subtype_le (H := M) (K := Ω))
  have hΩ_top : Ω = ⊤ := by
    have hinj : Function.Injective (Subgroup.map M.subtype) :=
      Subgroup.map_injective (f := M.subtype) M.subtype_injective
    have htop_map : (⊤ : Subgroup (↥M)).map M.subtype = M := by
      simpa [MonoidHom.range_eq_map] using (M.range_subtype : M.subtype.range = M)
    apply hinj
    simpa [htop_map] using hΩmap_eq_M
  have hpow : ∀ x : ↥M, x ^ p = 1 := by
    intro x
    have hxΩ : x ∈ Ω := by simp [hΩ_top]
    have hx' : x ∈ Subgroup.closure {y : ↥M | y ^ (p ^ 1) = 1} := by
      simpa [Ω, omega₁, omega] using hxΩ
    refine
      Subgroup.closure_induction (k := {y : ↥M | y ^ (p ^ 1) = 1})
        (p := fun z _hz => z ^ p = 1) (x := x) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simpa [pow_one] using hy
    · simp
    · intro a b _ha _hb ha hb
      calc
        (a * b) ^ p = a ^ p * b ^ p := by simpa using mul_pow a b p
        _ = 1 := by simp [ha, hb]
    · intro a _ha ha
      simp [ha]
  have hExp : Monoid.exponent (↥M) ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hpow
  exact ⟨p, hp_prime, ⟨hExp⟩⟩

end Theorem310
