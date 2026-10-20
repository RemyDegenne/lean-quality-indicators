@[expose] public section

noncomputable section

open Finset Function NNReal Set

namespace BoxIntegral

variable {ι : Type*}

namespace TaggedPrepartition

variable {I J : Box ι} {π π₁ π₂ : TaggedPrepartition I} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
@[simps -fullyApplied tag]
def biUnionPrepartition (π : TaggedPrepartition I) (πi : ∀ J : Box ι, Prepartition J) :
    TaggedPrepartition I where
  toPrepartition := π.toPrepartition.biUnion πi
  tag J := π.tag (π.toPrepartition.biUnionIndex πi J)
  tag_mem_Icc _ := π.tag_mem_Icc _

end TaggedPrepartition
end BoxIntegral
end
end
