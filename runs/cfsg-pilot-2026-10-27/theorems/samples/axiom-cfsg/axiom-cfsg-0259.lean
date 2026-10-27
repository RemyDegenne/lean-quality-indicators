public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.RigidL2

open Subgroup CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.SuzB0
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Co1Patterson
  CFSG.LargeExtraspecial CFSG.Open

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Model

theorem chartTransfer_wq {G : Type} [Group G] [Finite G]
    (S : Setting G) (hw : S.width = 3) (hΩ : S.Mbar.map S.O.subtype = timmesfeldOmega S.q)
    (hNWC : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) (σ : S.M ≃* invE 1) :
    ∃ ζ : centM (qVec 1) →* G, ∀ x (hx : x ∈ invE 1) (hxw : x ∈ centM (qVec 1)),
      ζ ⟨x, hxw⟩ = (σ.symm ⟨x, hx⟩ : G) := by
  set e : ↥(C[t1'] : Subgroup ↥suzM) ≃* ↥(C[S.z] : Subgroup G) := centT1Equiv.trans σ.symm
  set A : ↥suzM → G := extFun e with hAdef
  have hA : IsoOn A C[t1'] C[S.z] := isoOn_extFun e
  have hAval : ∀ x (hx : x ∈ C[t1']), A x = (σ.symm (centT1Equiv ⟨x, hx⟩) : G) :=
    fun x hx => extFun_of_mem e hx
  have htC : t1' ∈ C[t1'] := mem_centralizer_singleton_iff.2 rfl
  have hzc : t1C ∈ center ↥(invE 1) := mem_center_iff.2 fun g => (t1C_comm g).symm
  have hz1 : t1C ≠ 1 := fun h => suzInv_ne_one (i := 1) (by norm_num) (congrArg Subtype.val h)
  have hσz : σ.symm t1C = S.zM := by
    rw [← map_zM_eq S σ hzc hz1, MulEquiv.symm_apply_apply]
  have hAa : A t1' = S.z := by
    rw [hAval _ htC]
    have e1 : centT1Equiv ⟨t1', htC⟩ = t1C := rfl
    rw [e1, hσz]
    rfl
  have hW : A wq = (σ.symm w0C : G) := by
    rw [hAval _ wq_mem_cent]
    rfl
  have hWQ : A wq ∈ S.QG := by
    let q1C : Subgroup ↥(invE 1) := coord_qVec.Q.comap (invE 1).subtype
    have hN : q1C.Normal := ⟨fun n hn c => by
      have hN := (mem_inf.1 (invE_le c.2)).1
      exact (mem_normalizer_iff.1 hN _).1 hn⟩
    have hP : IsPGroup 2 q1C :=
      coord_qVec.isPGroup_Q.comap_of_injective (invE 1).subtype (invE 1).subtype_injective
    have hle := S.le_of_normal (q1C.map σ.symm.toMonoidHom) (hN.map _ σ.symm.surjective)
      (hP.map _)
    rw [hW]
    exact ⟨σ.symm w0C, hle ⟨w0C, w0P_mem, rfl⟩, rfl⟩
  have hw01 : w0C ≠ 1 := fun h => by
    have := coord_qVec.inj 1 (by norm_num) 0 (by norm_num) 0 (by norm_num) 0 (by norm_num) (by
      simp only [pow_zero, mul_one, coord_qVec.q_zero]
      exact congrArg Subtype.val h)
    omega
  have hw0t : w0C ≠ t1C := fun h => by
    have := coord_qVec.inj 1 (by norm_num) 0 (by norm_num) 0 (by norm_num) 1 (by norm_num) (by
      simp only [pow_zero, mul_one, pow_one, coord_qVec.q_zero, one_mul]
      exact congrArg Subtype.val h)
    omega
  have hW2 : orderOf (A wq) = 2 := by
    rw [hW, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact w0C_mul_self) hw01
  have hWz : A wq ≠ S.z := by
    rw [hW]
    intro h
    apply hw0t
    apply σ.symm.injective
    rw [hσz]
    exact Subtype.ext h
  obtain ⟨s, hs1, hs2, hsO⟩ := exists_model_swap
  obtain ⟨g, hg1, hg2, hgO⟩ := exists_setting_swap S hw hΩ hNWC hWQ hW2 hWz
  obtain ⟨Z, hZ, hagree, -⟩ :=
    exists_isoOn_agree hA hAa wq_mem_cent rfl hs1 hs2 hg1 hg2 hsO hgO autInnerModAt_t1_wq
  have hmem : ∀ x : centM (qVec 1), (⟨x, x.2.2⟩ : ↥suzM) ∈ C[wq] := fun x =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 x.2.1))
  let ζ : centM (qVec 1) →* G :=
    { toFun := fun x => Z ⟨x, x.2.2⟩
      map_one' := hZ.map_one
      map_mul' := fun x y => hZ.map_mul _ (hmem x) _ (hmem y) }
  refine ⟨ζ, fun x hx hxw => ?_⟩
  have hxt : (⟨x, hxw.2⟩ : ↥suzM) ∈ C[t1'] := mem_centralizer_singleton_iff.2 (comm_t1' hx)
  change Z ⟨x, hxw.2⟩ = _
  rw [hagree _ (mem_inf.2 ⟨hxt, hmem ⟨x, hxw⟩⟩), hAval _ hxt]
  rfl

end Model
end CFSG.Sporadic.SuzRecog.RigidL2
end
