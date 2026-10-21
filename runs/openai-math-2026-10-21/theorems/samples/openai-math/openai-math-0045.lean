namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphPresentation.Path

open PortSubdivision

variable {V D : Type} {Γ : PortGraph V D} {a b c : V}

lemma last_origin (p : Path Γ a b) (hn : p.darts≠[]) :
    Γ.origin (Γ.reverse (p.darts.getLast hn))=b := by
  induction p with
  | nil=>exact False.elim (hn rfl)
  | cons d p ih=>
    by_cases he : p.darts=[]
    · simpa only [darts_cons,he,List.getLast_singleton] using p.empty_ends he
    · simpa only [darts_cons,List.getLast_cons he] using ih he

end TorsionFreeZeroDivisors.GraphPresentation.Path
end
end OAI
