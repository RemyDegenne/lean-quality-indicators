@[expose] public section

open ENNReal NNReal

noncomputable section

namespace EReal

protected theorem le_neg_of_le_neg {a b : EReal} (h : a ≤ -b) : b ≤ -a := EReal.le_neg.mp h

end EReal
end
end
