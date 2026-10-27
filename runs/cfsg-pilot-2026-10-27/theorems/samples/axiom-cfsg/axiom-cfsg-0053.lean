public section

namespace CFSG.Quasithin.KGC31

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native Matrix

variable {n : ℕ}

theorem fixSetIs_iff {k : ℕ} {bs : List Table} {v : Fin k → Equiv.Perm (Fin n)}
    (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) {pts : List ℕ}
    (h : fixSetIs n bs pts = true) (i : Fin n) : (∀ j, v j i = i) ↔ i.val ∈ pts := by
  unfold fixSetIs at h
  rw [List.all_eq_true] at h
  have h1 := h i.val (List.mem_range.mpr i.isLt)
  rw [beq_iff_eq] at h1
  have h2 : (bs.all fun b => ap b i.val == i.val) = true ↔ ∀ j, v j i = i :=
    all_iff_of_forall₂ hbs (f := fun b => ap b i.val == i.val) (Q := fun g => g i = i)
      fun b g hb => by
        rw [beq_iff_eq, rep_apply hb i]
        exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
  rw [← h2, h1, List.contains_iff_mem]

end CFSG.Quasithin.KGC31
end
