public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.BorelTits

open HeisP

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem eq_top_of_heis_core_prime [Finite K] [Fact ℓ.Prime] [CharP K ℓ] [NeZero p]
    (h : UnitaryFieldData ℓ f K) (hT : TorusFourierGenU h p) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) {X Y : Matrix (Fin p) (Fin p) K} {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hX3 : X ^ p = (1 : K) • 1) (hY3 : Y ^ p = 1) (hYX : Y * X = ζ • (X * Y))
    (hXu : ∀ u v, herm (unitaryInvolution K ℓ f) (X *ᵥ u) (X *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    (hYu : ∀ u v, herm (unitaryInvolution K ℓ f) (Y *ᵥ u) (Y *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) p)}
    (hCY : HeisTensor.Cent H Y) (hCX : HeisTensor.Cent H X) : H = ⊤ := by
  classical
  obtain ⟨P, hPu, hXP, hYP⟩ := heis_frame_unitary h hp hp2 hpq hζ hX3 hY3 hYX hXu hYu
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin p) (Fin p) K, Q = Matrix.of fun a i => h.bar (P i a) :=
    ⟨_, rfl⟩
  have hQP : Q * P = 1 := by
    ext a b
    rw [hQdef, Matrix.mul_apply, Matrix.one_apply]
    simpa using hPu a b
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hPT : (P.map h.bar)ᵀ = Q := by
    rw [hQdef]
    ext a i
    simp
  obtain ⟨Pu, hPu1, hPu2⟩ : ∃ Pu : GL (Fin p) K,
      (Pu : Matrix (Fin p) (Fin p) K) = P ∧
        ((Pu⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = Q :=
    ⟨⟨P, Q, hPQ, hQP⟩, rfl, rfl⟩
  have hPmem : Pu ∈ primeFormUnitary h (idGram K p) := by
    rw [mem_primeFormUnitary, hPu1]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [hPT, hQP]
  let Pe : primeFormUnitary h (idGram K p) := ⟨Pu, hPmem⟩
  let ψ : unitarySU ℓ f K p ≃* unitarySU ℓ f K p := CFSG.RankThree.PartOne.KFU.conjSU h Pe
  let ε : SUid (unitaryInvolution K ℓ f) p ≃* unitarySU ℓ f K p :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq p)
  let K₁ : Subgroup (unitarySU ℓ f K p) := (H.comap ε.symm.toMonoidHom).comap ψ.toMonoidHom
  let H₁ : Subgroup (GL (Fin p) K) := K₁.map (unitarySU ℓ f K p).subtype
  have hcoe : ∀ x : unitarySU ℓ f K p,
      (((ψ x : unitarySU ℓ f K p) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
        P * ((x : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * Q := by
    intro x
    show (((CFSG.RankThree.PartOne.KFU.conjSU h Pe x : unitarySU ℓ f K p) :
        GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = _
    rw [CFSG.RankThree.PartOne.KFU.coe_conjSU, Units.val_mul, Units.val_mul]
    show (Pu : Matrix (Fin p) (Fin p) K) * ((x : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
      ((Pu⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = _
    rw [hPu1, hPu2]
  have hε : ∀ x : unitarySU ℓ f K p,
      ((ε.symm x : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) = (x : GL (Fin p) K) :=
    fun x => rfl
  have hYPQ : Y = P * HeisP.Zm ζ * Q := by
    calc Y = Y * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (Y * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * HeisP.Zm ζ * Q := by rw [hYP]
  have hXPQ : X = P * HeisP.Gj ζ 1 0 * Q := by
    calc X = X * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (X * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * HeisP.Gj ζ 1 0 * Q := by rw [hXP]
  have hle : H₁ ≤ unitarySU ℓ f K p := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hdiag : ∀ g ∈ unitarySU ℓ f K p,
      (∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) = Matrix.diagonal t) → g ∈ H₁ := by
    rintro g hg ⟨t, ht⟩
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩, ?_, rfl⟩
    show ε.symm (ψ ⟨g, hg⟩) ∈ H
    refine hCY _ ?_
    show (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) * Y = Y *
      (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K)
    rw [hε, hcoe, hYPQ]
    refine conj_mul_comm_aux hQP ?_
    show (g : Matrix (Fin p) (Fin p) K) * HeisP.Zm ζ = HeisP.Zm ζ * (g : Matrix (Fin p) (Fin p) K)
    rw [ht]
    exact diagonal_mul_Zm_comm t ζ
  have hfour : ∀ g ∈ unitarySU ℓ f K p,
      (∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) * heisFourierMat ζ =
        heisFourierMat ζ * Matrix.diagonal t) → g ∈ H₁ := by
    intro g hg ht
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩, ?_, rfl⟩
    show ε.symm (ψ ⟨g, hg⟩) ∈ H
    refine hCX _ ?_
    show (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) * X = X *
      (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K)
    rw [hε, hcoe, hXPQ]
    exact conj_mul_comm_aux hQP (gj_comm_of_fourier hζ ht)
  have hH₁ : H₁ = unitarySU ℓ f K p := hT ζ hζ H₁ hle hdiag hfour
  have hK₁ : ∀ x : unitarySU ℓ f K p, x ∈ K₁ := by
    intro x
    have hx : (x : GL (Fin p) K) ∈ H₁ := by
      rw [hH₁]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  rw [eq_top_iff]
  intro z _
  have h2 : ε.symm (ψ (ψ.symm (ε z))) ∈ H := hK₁ (ψ.symm (ε z))
  simpa using h2

end CFSG.LieType.SeitzGeneration
end
