public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L34Amalgam MulAction

open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

namespace S6Model

variable (M : S6Model z s)

include M in
theorem exists_j_of_i [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g : G}
    (hg : g ∈ Subgroup.normalizer (M.V2 : Set G)) (hgNN : g ∉ M.NN) {x : G}
    (hx3 : orderOf x = 3) (hx'N : g⁻¹ * x * g ∈ hsNB z s)
    (hπx' : M.π ⟨g⁻¹ * x * g, hx'N⟩ = σS0) {i : G} (hi2 : i * i = 1)
    (hix : i * x * i⁻¹ = x⁻¹) (hyN : g⁻¹ * i * g ∈ hsNB z s)
    (hyst : M.π ⟨g⁻¹ * i * g, hyN⟩ ∈ stabS)
    (hyalt : M.π ⟨g⁻¹ * i * g, hyN⟩ ∈ alternatingGroup (Fin 6)) :
    ∃ j : G, j ∈ M.L1.map (MulAut.conj g).toMonoidHom ∧ j ∉ M.L1 ∧ j * j = 1 ∧
      (i * j) ^ 3 = 1 := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (M.V2 : Set G) := (Subgroup.normalizer _).inv_mem hg
  set x' : ↥(hsNB z s) := ⟨g⁻¹ * x * g, hx'N⟩ with hx'
  have hx'3 : orderOf (x' : G) = 3 := by
    show orderOf (g⁻¹ * x * g) = 3
    rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq, hx3]
  obtain ⟨t, htt, htx, htl, htl0, -⟩ := M.exists_t1 h hsmemH hsnotK hss hg₀ hx'3 hπx'
  obtain ⟨-, -, -, -, -, -, -, hinf, -⟩ := M.parabolics_of_g h hsmemH hsnotK hss hg₀ hg hgNN
  have htL1 : (t : G) ∈ M.L1 := M.mem_pre.mpr ⟨t.2, htl⟩
  have htRX : (t : G) ∉ M.RX := fun hm => htl0 (M.π_mem_of_mem_pre hm t.2)
  have hjt : g⁻¹ * (g * t * g⁻¹) * g = (t : G) := by group
  refine ⟨g * t * g⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [mem_map_conj_iff, hjt]
    exact htL1
  · intro hm
    have hjRX : g * t * g⁻¹ ∈ M.RX := by
      rw [← hinf]
      exact ⟨hm, mem_map_conj_iff.mpr (by rw [hjt]; exact htL1)⟩
    have := M.conj_mem_RX h hsmemH hsnotK hss hg₀ hg' hjRX
    rw [inv_inv, hjt] at this
    exact htRX this
  · rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * ((t : G) * t) * g⁻¹ by group, htt]
    group
  · set y : ↥(hsNB z s) := ⟨g⁻¹ * i * g, hyN⟩ with hy
    have hyy : (y : G) * y = 1 := by
      show g⁻¹ * i * g * (g⁻¹ * i * g) = 1
      rw [show g⁻¹ * i * g * (g⁻¹ * i * g) = g⁻¹ * (i * i) * g by group, hi2]
      group
    have hyx' : (y : G) * x' * (y : G)⁻¹ = (x' : G)⁻¹ := by
      show g⁻¹ * i * g * (g⁻¹ * x * g) * (g⁻¹ * i * g)⁻¹ = (g⁻¹ * x * g)⁻¹
      calc g⁻¹ * i * g * (g⁻¹ * x * g) * (g⁻¹ * i * g)⁻¹ = g⁻¹ * (i * x * i⁻¹) * g := by group
        _ = (g⁻¹ * x * g)⁻¹ := by rw [hix]; group
    have hπinv : ∀ u : ↥(hsNB z s), (u : G) * x' * (u : G)⁻¹ = (x' : G)⁻¹ →
        M.π u * σS0 * (M.π u)⁻¹ = σS0⁻¹ := by
      intro u hu
      have e : u * x' * u⁻¹ = x'⁻¹ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
        exact hu)
      have e' := congrArg M.π e
      rw [map_mul, map_mul, map_inv, map_inv, hπx'] at e'
      exact e'
    have hρ : M.π y ∈ evenInv := mem_evenInv hyst hyalt
      (by rw [← map_mul, show y * y = 1 from Subtype.ext hyy, map_one]) (hπinv y hyx')
    have hψ : M.π t ∈ jInv := mem_jInv _ htl htl0
      (by rw [← map_mul, show t * t = 1 from Subtype.ext htt, map_one]) (hπinv t htx)
    have h3 := evenInv_mul_jInv_pow_three _ hρ _ hψ
    have hwB : (((y * t) ^ 3 : ↥(hsNB z s)) : G) ∈ hsB z s :=
      (M.ker _).mp (by rw [map_pow, map_mul, h3])
    have hcomm : (y : G) * t * x' = x' * ((y : G) * t) := by
      calc (y : G) * t * x' = y * (t * x' * (t : G)⁻¹) * t := by group
        _ = y * (x' : G)⁻¹ * t := by rw [htx]
        _ = ((y : G) * (x' : G)⁻¹ * (y : G)⁻¹) * (y * t) := by group
        _ = x' * ((y : G) * t) := by
          rw [show (y : G) * (x' : G)⁻¹ * (y : G)⁻¹ = ((y : G) * x' * (y : G)⁻¹)⁻¹ by group,
            hyx', inv_inv]
    have hw1 := M.eq_one_of_mem_hsB_comm hπx' hwB (by
      rw [Subgroup.coe_pow, Subgroup.coe_mul]
      exact (Commute.pow_left (show Commute ((y : G) * t) x' from hcomm) 3).eq)
    rw [Subgroup.coe_pow, Subgroup.coe_mul] at hw1
    rw [show i * (g * t * g⁻¹) = g * ((y : G) * t) * g⁻¹ by rw [hy]; group, conj_pow, hw1]
    group

end S6Model
end HSSetting
end CFSG.Quasithin.HSType
end
