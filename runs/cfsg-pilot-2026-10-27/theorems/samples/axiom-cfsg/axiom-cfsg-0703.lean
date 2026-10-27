public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native Matrix

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

theorem lineSmul_mul (g h : J) (w : LineRep) :
    lineSmul (g * h) w = lineSmul g (lineSmul h w) := by
  apply Subtype.ext
  rw [lineSmul_val', lineSmul_val', lineSmul_val']
  have hne := mulVec_ne_zero_of_injective (mat_mulVec_injective h) w.2.1
  obtain ⟨c, hc, he⟩ := (normalize_spec hne).1
  rw [he, Matrix.mulVec_smul, (normalize_spec (mulVec_ne_zero_of_injective
    (mat_mulVec_injective g) hne)).2.2 c hc, mat_mul, Matrix.mulVec_mulVec]

end CFSG.ONSchreier
end
