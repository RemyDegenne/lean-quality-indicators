@[expose] public section

open Function Set Topology

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace PartialHomeomorph

variable (e : PartialHomeomorph X Y)

/-- If a `PartialEquiv` is a homeomorphism when restricted to source and target, then it is a
`PartialHomeomorph`. -/
def ofIsHomeomorphToEquiv (f : PartialEquiv X Y) (h : IsHomeomorph (f.toEquiv)) :
    PartialHomeomorph X Y where
  toPartialEquiv := f
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict,
      ← continuous_codRestrict_iff (s := f.target) (by simp)]
    exact h.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict,
      ← continuous_codRestrict_iff (s := f.source) (by simp)]
    exact ((Equiv.isHomeomorph_iff _).1 h).2

end PartialHomeomorph
end
