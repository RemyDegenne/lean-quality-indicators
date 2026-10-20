public section

namespace TauCeti

universe u v w x

variable {C : FiniteGroupClass.{u}} {G : Type v} {H : Type w} [Group G] [TopologicalSpace G]

variable [Group H] [TopologicalSpace H]

section UniversalProperty

variable {P : Type w} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

@[simp]
theorem proCCompletion.lift_mk (hP : IsProC C P) (f : G →* P) (hf : Continuous f) (x : G) :
    proCCompletion.lift hP f hf (x : proCCompletion C G) = f x := by
  rfl

end UniversalProperty
end TauCeti
end
