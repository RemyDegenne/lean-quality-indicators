public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.Quasithin.H13.A6

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem a6CentralQuotient_of_isA6On {L V : Subgroup G} (hLV : L ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ centralizer (V : Set G)) (h5 : QT13Five (↥L ⧸ CFSG.pCore 2 ↥L))
    (hA6 : IsA6On L V) : A6CentralQuotient L := by
  obtain ⟨e⟩ := hA6
  let φ : ↥L →* ↥(alternatingGroup (Fin 6)) := e.toMonoidHom.comp (autOnHom hLV)
  have hφ : Function.Surjective φ := e.surjective.comp (autOnHom_surjective hLV)
  have hO2 : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxC : (x : G) ∈ centralizer (V : Set G) := hO (coe_mem_pCoreOf_iff.2 hx)
    have h1 : autOnHom hLV x = 1 := Subtype.ext (by
      rw [autOnHom_apply]
      exact A1b.conjAct_eq_one_iff.2 hxC)
    simp only [φ, MonoidHom.comp_apply, h1, map_one]
  let φ₁ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(alternatingGroup (Fin 6)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO2
  have hφ₁ : Function.Surjective φ₁ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨(x : ↥L ⧸ CFSG.pCore 2 ↥L), rfl⟩
  have hle : 360 ≤ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [← card_alt6]
    exact Nat.card_le_card_of_surjective φ₁ hφ₁
  rcases h5 with he5 | h32 | he6 | hhat | hu
  · obtain ⟨e5⟩ := he5
    rw [Nat.card_congr e5.toEquiv, card_alt5] at hle
    omega
  · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
    rw [Nat.card_congr e3.toEquiv, HSType.card_SL_three_two] at hle
    omega
  · obtain ⟨e6⟩ := he6
    have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hsQ : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr e6).2 hs
    have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := alt6_nonabelian
      exact ⟨e6.symm a, e6.symm b, fun h => hab (by simpa using congrArg e6 h)⟩
    have hcen := center_eq_bot_of_isSimpleGroup hna
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans (QuotientGroup.quotientBot.trans e6)⟩
  · exact hhat.2.2
  · have hc := card_of_lieModel_PSU_three_three hu
    have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := isSimpleGroup_of_lieModel_PSU hu
    rcases hs.eq_bot_or_eq_top_of_normal φ₁.ker with h | h
    · have := Nat.card_le_card_of_injective φ₁ ((MonoidHom.ker_eq_bot_iff φ₁).1 h)
      rw [hc, card_alt6] at this
      omega
    · exfalso
      have hall : ∀ y : ↥(alternatingGroup (Fin 6)), y = 1 := by
        intro y
        obtain ⟨x, rfl⟩ := hφ₁ y
        exact (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top x)
      obtain ⟨a, b, hab⟩ := alt6_nonabelian
      exact hab (by rw [hall a, hall b])

end CFSG.Quasithin.H13.U3
end
