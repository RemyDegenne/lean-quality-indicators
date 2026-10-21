namespace OAI

namespace CriticalStrip.Diagram

noncomputable section

open scoped Classical LaurentPolynomial

lemma fullPeel_injective {n:ℕ} (i:Fin (n+1)) : Function.Injective (fullPeel i) :=
  (AddMonoidAlgebra.map_injective _ (insertSpectral i).injective).comp (peelLaurent_injective i)

end
end CriticalStrip.Diagram
end OAI
