namespace OAI

namespace MatchingFPRAS.OnlineSample

open PhysicalStream

lemma mean_scans (k N r : ℕ) (h : List (List Bool×NumericLadder.Bits) → ℚ) :
    (scans ((k,N),r)).mean h=qaverage (fun bs : Fin r→ScanRandom N k=>h (List.ofFn (fun i=>scanRep (bs i)))) := by
  unfold scans
  rw [show List.replicate r (k,N)=List.ofFn (fun _ : Fin r=>(k,N)) by simp]
  exact mean_traverse_ofFn scan r (fun _=>(k,N)) (fun _ b=>scanRep b) (fun _=>mean_scan k N) h

end MatchingFPRAS.OnlineSample
end OAI
