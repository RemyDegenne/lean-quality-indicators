namespace OAI

namespace CriticalStrip.Diagram

noncomputable section

open scoped Classical

namespace TriplePosition

variable {n : ℕ} (s : TriplePosition n)

lemma ab : s.a≠s.b := by intro he; have:=congrArg Fin.val he; have:=s.hab; omega

end TriplePosition
end
end CriticalStrip.Diagram
end OAI
