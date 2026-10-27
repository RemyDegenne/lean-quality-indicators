public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open

open scoped Pointwise

set_option maxRecDepth 100000 in
theorem w16l_alt6_witness (V : Subgroup (alternatingGroup (Fin 6))) (hV : IsElemAbelian 2 V)
    (hcard : Nat.card V = 4) :
    ∃ γ : alternatingGroup (Fin 6),
      (∃ a ∈ V, ∃ b ∈ CFSG.Quasithin.conjSubgroup V γ, a * b ≠ b * a) ∧
        ∃ v ∈ V, v ≠ 1 ∧ v ∈ Subgroup.normalizer
          ((CFSG.Quasithin.conjSubgroup V γ : Subgroup (alternatingGroup (Fin 6))) :
            Set (alternatingGroup (Fin 6))) := by
  obtain ⟨p, hpV, -, -, hpo, -, -⟩ :=
    CFSG.ComponentClassification.AS76b.exists_two_involutions hV hcard
  have hp2 : p * p = 1 := by
    have h := pow_orderOf_eq_one p
    simpa [hpo, pow_two] using h
  have hp1 : p ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hpo
    norm_num at hpo
  obtain ⟨ρ, hρA, hρ⟩ := CFSG.Quasithin.S143.alt6_invol_conj
    (p : Equiv.Perm (Fin 6)) CFSG.Quasithin.R3c13.a6x0 p.2
    CFSG.Quasithin.R3c13.a6x0_mem
    (by intro h; exact hp1 (Subtype.ext h))
    (by intro h; exact w16l_s_ne_one (Subtype.ext h))
    (by simpa using congrArg Subtype.val hp2)
    (by simpa [w16l_s] using congrArg Subtype.val w16l_s_sq)
  let ρA : alternatingGroup (Fin 6) := ⟨ρ, hρA⟩
  let δ : alternatingGroup (Fin 6) := ρA⁻¹
  have hρG : ρA * p * ρA⁻¹ = w16l_s := Subtype.ext hρ
  have hp_eq : p = δ * w16l_s * δ⁻¹ := by
    have h := congrArg (fun x => ρA⁻¹ * x * ρA) hρG
    simpa [δ, mul_assoc] using h
  let W : Subgroup (alternatingGroup (Fin 6)) := CFSG.Quasithin.conjSubgroup V δ
  have hWconj : W = CFSG.Quasithin.conjSubgroup V δ := rfl
  have hsW : w16l_s ∈ W := by
    rw [hWconj, CFSG.Quasithin.mem_conjSubgroup_iff, ← hp_eq]
    exact hpV
  have hW4 : Nat.card W = 4 := by
    rw [hWconj, CFSG.Quasithin.conjSubgroup]
    rw [Subgroup.card_map_of_injective (MulAut.conj δ⁻¹).injective, hcard]
  have hWcomm : IsMulCommutative W := by
    haveI : IsMulCommutative V := hV.1
    rw [hWconj, CFSG.Quasithin.conjSubgroup]
    exact Subgroup.map_isMulCommutative V (MulAut.conj δ⁻¹).toMonoidHom
  have hWexp : ∀ x ∈ W, x * x = 1 := by
    intro x hx
    rw [hWconj, CFSG.Quasithin.conjSubgroup] at hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul, show v * v = 1 by simpa [pow_two] using hV.2 v hv, map_one]
  have hWcase := w16l_klein_eq_K1_or_K2 hW4 hsW hWcomm hWexp
  rcases hWcase with hWK1 | hWK2
  · have hw := w16l_K1_witness
    rw [← hWK1] at hw
    obtain ⟨γ, hγ⟩ := hw
    exact w16l_witness_of_conj hWconj (γ := γ) hγ
  · have hw := w16l_K2_witness
    rw [← hWK2] at hw
    obtain ⟨γ, hγ⟩ := hw
    exact w16l_witness_of_conj hWconj (γ := γ) hγ

end CFSG.LocalAnalysis.WeakClosure81
end
