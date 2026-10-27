@[expose] public section

open MeasurableSpace Set

open scoped MeasureTheory

variable {α β : Type*}

namespace MeasurableSpace

open scoped Function

variable {α : Type*}

namespace DynkinSystem

variable (d : DynkinSystem α)

/-- If `s` is in a Dynkin system `d`, we can form the new Dynkin system `{s ∩ t | t ∈ d}`. -/
def restrictOn {s : Set α} (h : d.Has s) : DynkinSystem α where
  Has t := d.Has (t ∩ s)
  has_empty := by simp [d.has_empty]
  has_compl {t} hts := by
    have : tᶜ ∩ s = (t ∩ s)ᶜ \ sᶜ := Set.ext fun x => by by_cases h : x ∈ s <;> simp [h]
    simp_rw [this]
    exact
      d.has_sdiff (d.has_compl hts) (d.has_compl h)
        (compl_subset_compl.mpr inter_subset_right)
  has_iUnion_nat {f} hd hf := by
    rw [iUnion_inter]
    refine d.has_iUnion_nat ?_ hf
    exact hd.mono fun i j => Disjoint.mono inter_subset_left inter_subset_left

end DynkinSystem
end MeasurableSpace
end
