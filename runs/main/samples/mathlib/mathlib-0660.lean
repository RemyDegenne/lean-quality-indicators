@[expose] public section

noncomputable section

universe u v

open Function Order

namespace Ordinal

section

variable {ι : Type*} {f : ι → Ordinal.{u} → Ordinal.{u}}

theorem derivFamily_eq_enumOrd [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    derivFamily f = enumOrd (⋂ i, Function.fixedPoints (f i)) := by
  rw [eq_comm, eq_enumOrd _ (not_bddAbove_fp_family H)]
  use (isNormal_derivFamily f).strictMono
  rw [Set.range_eq_iff]
  refine ⟨?_, fun a ha => ?_⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact derivFamily_fp (H i) a
  rw [Set.mem_iInter] at ha
  rwa [← fp_iff_derivFamily H]

end
end Ordinal
end
end
