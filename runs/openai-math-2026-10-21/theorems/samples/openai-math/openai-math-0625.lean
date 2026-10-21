namespace OAI

namespace TwoPointCorrelations

open Finset

open scoped Classical

lemma halasz_residue_quotient_recover {M p : ℕ} (hp : 0<p) (b : Fin p)
    (x : Fin M) (hx : halaszResidueIndex hp x=b) :
    p*((halaszResidueQuotient p x).val+1)-(p-1-b.val)=x.val+1 := by
  have hm : x.val%p=b.val := congrArg Fin.val hx
  have hd := Nat.mod_add_div x.val p
  dsimp [halaszResidueQuotient]
  rw [Nat.mul_add,Nat.mul_one]
  omega

end TwoPointCorrelations
end OAI
