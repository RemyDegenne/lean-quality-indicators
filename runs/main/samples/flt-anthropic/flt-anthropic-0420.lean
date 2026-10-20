namespace P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open PDivisibleGroup Filter Topology

open scoped TensorProduct

namespace PDivStep2R

variable (p : ℕ) [Fact p.Prime]

section Values

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]

variable {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')

theorem cvu_add_right (Y : G.CPoints (O p R)) (y y' : TateModule p (G'.Points (K p))) (i : ℕ) :
    cvu p D Y (y + y') i = cvu p D Y y i * cvu p D Y y' i := by
  have h1 : yq p G' i (y + y') = yq p G' i y + yq p G' i y' := map_add (yqLin p G' i) y y'
  have h2 := map_add (αq p D i (G.cpointsProj (O p R) i Y)) (yq p G' i y) (yq p G' i y')
  rw [← h1] at h2
  have h3 := congrArg (fun t : PrimaryTorsion p (Additive (Oq p R i)ˣ) => Additive.toMul (t : Additive (Oq p R i)ˣ)) h2
  exact h3

end Values
end PDivStep2R
end
end P2MW.S_PDivisibleGroup_CartierDuality_nsmul_mem_and_eq_zero_and_exists_nsmul_eq_of_forall_pair_eq_one_of_isIntegral_iff
