public section

namespace CFSG.ClassicalInvolution

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.ClassicalInvolution.McLData

namespace McLProof

theorem words_check :
    (∀ w ∈ kWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧ (∀ w ∈ sWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧
      (∀ w ∈ conjWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧
      (∀ p ∈ repData, (∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 2) ∧ ∀ cw ∈ p.2, ∀ l ∈ cw, 1 ≤ l ∧ l ≤ 2) ∧
      sgens.all (permOK 275) = true ∧ repTbls.all (permOK 275) = true ∧
      (conjWords.map (wordTbl 275 abT)).all (fun c => permOK 275 c && invOK 275 c (invT 275 c)) =
        true ∧
      (repData.all fun p => p.2.all fun cw => permOK 275 (wordTbl 275 kgens cw) &&
        invOK 275 (wordTbl 275 kgens cw) (invT 275 (wordTbl 275 kgens cw))) = true ∧
      (repGens.all fun gs => gs.all (permOK 275)) = true := by
  exact Certificates.certificate9314.2.2.1

end McLProof
end CFSG.ClassicalInvolution
end
