namespace OAI

noncomputable section

namespace ContinuumCoulomb

open scoped Classical

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaXZSubdivisionWord_envelope (a b : ι → Fin 4) (e : κ) {S : Finset ι}
    (ha : qmaPauliSupport a ⊆ S) (hb : qmaPauliSupport b ⊆ S) (k : Fin 4) :
    qmaPauliSupport (qmaXZSubdivisionWord a b e k) ⊆ qmaMediatorSupport S e := by
  fin_cases k
  · simp [qmaXZSubdivisionWord,qmaPauliSupport]
  · exact qmaJoinedWord_envelope (fun _ => 0) e 3 (by simp [qmaPauliSupport])
  · exact qmaJoinedWord_envelope a e 1 ha
  · exact qmaJoinedWord_envelope b e 1 hb

end ContinuumCoulomb
end
end OAI
