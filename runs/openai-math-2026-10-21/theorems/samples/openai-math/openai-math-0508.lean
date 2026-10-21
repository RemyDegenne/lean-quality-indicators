namespace OAI

section

noncomputable section

open scoped CStarAlgebra ComplexOrder

namespace DimensionDropModel

open ConcreteMatrixUnits StarTerms CompletelyPositiveOperations

variable {I : Type*} [Fintype I] [DecidableEq I]
 def algebraicFibre (p : I) (t : ℝ) : StarSubalgebra ℂ (Mat I) := evalRange (values p t)

lemma amplify_unit_mem_fibre (p : I) {t : ℝ} (ht : t<1) (a b : Option I) :
    amplify (J := I) (unit a b)∈algebraicFibre p t := by
  have hs (i : I) := bridge_mem_fibre p ht i
  have hst (i : I) : amplify (J := I) (unit none (some i))∈algebraicFibre p t := by
    simpa only [←map_star,unit_star] using star_mem (hs i)
  cases a with
  | none =>
    cases b with
    | none => simpa only [←map_mul,unit_mul,ite_true] using mul_mem (hst p) (hs p)
    | some j => exact hst j
  | some i =>
    cases b with
    | none => exact hs i
    | some j => simpa only [←map_mul,unit_mul,ite_true] using mul_mem (hs i) (hst j)

end DimensionDropModel
end
end
end OAI
