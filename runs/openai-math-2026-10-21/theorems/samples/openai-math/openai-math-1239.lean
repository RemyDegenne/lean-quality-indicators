namespace OAI

namespace PolynomialVacuumCylinder

open Classical

variable {M H : ℕ} [NeZero M]

namespace ArcSystem

theorem code_of_parts (R : ArcSystem (bandSites M H)) (s : Bool × ZMod M → ArcChoice M)
    (hf : (R.part false).code=cutCode false s) (ht : (R.part true).code=cutCode true s) : R.code=s := by
  funext p
  have h0:=congrFun hf p
  have h1:=congrFun ht p
  simp only [part_code,cutCode] at h0 h1
  cases hp:p.1 <;> simp [hp] at h0 h1 <;> assumption

end ArcSystem
end PolynomialVacuumCylinder
end OAI
