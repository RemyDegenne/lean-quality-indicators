public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique Matrix CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Setup.X6

open CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4 (fam fuel comm_famL₂ fam_zero fam_mem_U
  fam_mem_V0 fam_mem_V1 sylowV_zero_split sylowV_one_split center_V0_forced center_V1_forced
  testsV0 testsV1 rad_le_parabolic parabolic_le_normalizer_rad isPGroup_rad perfectCore_parabolic
  levi_hom generation_zero generation_one sylowV_zero_zero weylTwo_conj_fam)

open scoped commutatorElement

section F4

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem coordFH_eq
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (w : Fin 2 → K) :
    coordFH a (sylowF a K 0 (largeReeRhoHom K a (w 1)) *
      sylowH a K 0 (largeReeRhoHom K a (w 0))) = w := by
  have h : ∃ w' : Fin 2 → K, sylowF a K 0 (largeReeRhoHom K a (w 1)) *
      sylowH a K 0 (largeReeRhoHom K a (w 0)) = sylowF a K 0 (largeReeRhoHom K a (w' 1)) *
        sylowH a K 0 (largeReeRhoHom K a (w' 0)) := ⟨w, rfl⟩
  rw [coordFH, dite_eq_left h]
  obtain ⟨h1, h0⟩ := f4_FH_inj hK h.choose_spec
  have hinj := (largeReeRhoHom K a).injective
  ext i
  fin_cases i
  · exact (hinj h0).symm
  · exact (hinj h1).symm

end F4
end CFSG.Quasithin.C35Pf
end
