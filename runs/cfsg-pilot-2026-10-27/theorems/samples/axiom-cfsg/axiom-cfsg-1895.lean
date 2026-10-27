public noncomputable section

namespace CFSG.GH74.GLS.NT44.PermutationInputs

open CFSG.Monster.B.Co2

open CFSG.Monster.B.Co2.Native

open PermutationNative

open CFSG.Certificates

open CFSG.Certificates.Native

theorem presentation_relators
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ r ∈ {r : FreeGroup (Fin 2) |
        r ∈ CFSG.LieType.Multipliers.L34.coverWs.map FreeGroup.mk},
      (FreeGroup.lift presentationGenerator) r = (1 : Khat) := by
  intro r hr
  change r ∈ CFSG.LieType.Multipliers.L34.coverWs.map FreeGroup.mk at hr
  rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
  let D := PermutationNative.inputs ()
  let KI := D.ks.map (invCand 2688)
  let V := D.fwd.map fun w => wordA 2688 D.ks KI w
  let VI := V.map (invCand 2688)
  let I := idA 2688
  obtain ⟨-, -, hcover, -⟩ := bridgeCheck_facts hcheck
  obtain ⟨-, hrel, -, -⟩ := coverCheck_facts hcover
  have hrelw : (lettersOK 2 (w.map CFSG.Certificates.schreierLetterCode) &&
      eqA 2688 (wordA 2688 V VI (w.map CFSG.Certificates.schreierLetterCode)) I) = true :=
    (List.all_eq_true.mp hrel) _ (List.mem_map_of_mem hw)
  have hrelParts := hrelw
  rw [Bool.and_eq_true] at hrelParts
  have hlettersCode : lettersOK 2 (w.map CFSG.Certificates.schreierLetterCode) = true :=
    hrelParts.1
  have heqCode :
      eqA 2688 (wordA 2688 V VI (w.map CFSG.Certificates.schreierLetterCode)) I = true :=
    hrelParts.2
  have hword := presentation_word_rep hcheck
    (w.map CFSG.Certificates.schreierLetterCode) hlettersCode
  rw [toLetters_map_schreierLetterCode w] at hword
  have heq : Quiver.SchreierGraph.evalWord
      (fun k : Fin 2 => (presentationGenerator k : Equiv.Perm (Fin 2688))) w = 1 :=
    (eqA_iff hword (rep_idA (n := 2688))).1 heqCode
  apply Subtype.ext
  rw [coe_lift_presentationGenerator]
  exact heq

end CFSG.GH74.GLS.NT44.PermutationInputs
end
