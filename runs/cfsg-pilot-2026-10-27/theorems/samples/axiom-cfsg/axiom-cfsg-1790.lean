public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}

variable (s : Set714 G T L V t z)

include s

namespace N3

variable {s} {h1222 : Stmt12_2_2} (hn : s.N3 h1222)

include hn

theorem inf_centralizer_eq {v : G}
    (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) :
    s.Qz h1222 ⊓ Subgroup.centralizer ({v} : Set G) = V ⊓ s.Qz h1222 ⊔ U714 T L V z := by
  have hvV : v ∈ V := (inf_le_left : V1 T L V ≤ V) hv
  have hvU : v ∈ U714 T L V z := le_conjClosure _ _ hv
  have hle : V ⊓ s.Qz h1222 ⊔ U714 T L V z ≤ s.Qz h1222 ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine sup_le (fun x hx => ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩)
      (fun x hx => ⟨s.U_le_Qz hn hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩)
    · exact s.comm_V h1222 hx.1 hvV
    · exact s.comm_U hn hx hvU
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hn.card_C0]
  have hlt : s.Qz h1222 ⊓ Subgroup.centralizer ({v} : Set G) < s.Qz h1222 :=
    lt_of_le_of_ne inf_le_left fun heq =>
      hn.not_le_centralizer hvU hvz (heq ▸ inf_le_right)
  have hQ : Nat.card ↥(s.Qz h1222) = 128 := by rw [hn.card_Q]; norm_num
  have h1 := Subgroup.card_dvd_of_le hlt.le
  have h2 := Subgroup.card_lt_of_lt hlt
  rw [hQ] at h1 h2
  obtain ⟨k, hk⟩ := h1
  rcases k with _ | _ | k
  · simp at hk
  · omega
  · have : 128 ≥ Nat.card ↥(s.Qz h1222 ⊓ Subgroup.centralizer ({v} : Set G)) * 2 := by
      rw [hk]
      exact Nat.mul_le_mul_left _ (by omega)
    omega

end N3
end CFSG.Quasithin.H13.S127.L715.Set714
end
