universe u v

public noncomputable section

namespace HahnSeries

variable {R : Type v} {G : Type u}

section Zero

variable [PartialOrder G] [Zero R]

@[simp]
protected theorem coeff_truncGT [DecidableLT G] (c : G) (x : R⟦G⟧) (i : G) :
    (truncGT c x).coeff i = if c < i then x.coeff i else 0 :=
  (rfl)

end Zero
end HahnSeries
end
