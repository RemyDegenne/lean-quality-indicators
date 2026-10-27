public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X

open CFSG.Quasithin.F7 CFSG.Quasithin.FA5

open CFSG.Quasithin.F53

open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section Local

variable (F : Frame L1 L2 S D X)

include F

variable (hT1 : ConfigT1 L1 L2 S)

include hT1

theorem five_centralizes_Zv_T1 {d : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hd : vtype d = false) :
    ∀ c ∈ stab d, c ^ 5 = 1 → c ∈ Subgroup.centralizer (Zv d : Set G) := by
  have hA := Amal.of_frame F
  obtain ⟨x, hx⟩ : ∃ x, x ∈ nbrs d := by
    by_contra hcon
    push Not at hcon
    have hcard := hA.card_nbrs d
    have : nbrs d = ∅ := Set.eq_empty_iff_forall_notMem.mpr hcon
    rw [this] at hcard
    simp at hcard
  have hxd : d ∈ nbrs x := mem_nbrs_symm hx
  have hxt : vtype x = true := by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj d x from hx)
    rw [hd] at this
    cases h : vtype x <;> simp_all
  obtain ⟨hT, -, -⟩ := sylow_sup_Qv F hxt hxd
  have hZT : Zv d = quasithinOmegaOneCenter (Qv x ⊔ Qv d) := (hT1 d).mpr hd _ hT
  obtain ⟨t, htx, htd⟩ : ∃ t ∈ Qv x, t ∉ Qv d := by
    by_contra h; push Not at h; exact not_Qv_le_Qv_of_nbr F hxt hxd fun t ht => h t ht
  have htT : t ∈ Qv x ⊔ Qv d := le_sup_left (a := Qv x) htx
  have htC : t ∈ Subgroup.centralizer (Zv d : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hZT] at hz
    have hle : quasithinOmegaOneCenter (Qv x ⊔ Qv d) ≤
        (Qv x ⊔ Qv d) ⊓ Subgroup.centralizer ((Qv x ⊔ Qv d : Subgroup G) : Set G) :=
      (Subgroup.closure_le _).mpr fun _ hx => hx.1
    exact (Subgroup.mem_centralizer_iff.mp (hle hz).2 t htT).symm
  have htd' : t ∈ stab d := hA.Qv_le_stab_of_mem_nbrs hxd htx
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (stab x)) ⟨t, htx⟩
  have htn : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact five_centralizes_Zv_of_two F hd htd' htn htC htd

end Local
end CFSG.Quasithin.Kleidman.F204
end
