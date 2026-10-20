@[expose] public section

variable {𝕜 E F G ι : Type*} {M : ι → Type*}

open Function Module Set

open scoped Pointwise Convex

open scoped Convex

section OrderedRing

variable (𝕜) [Ring 𝕜] [PartialOrder 𝕜] [AddRightMono 𝕜]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [Module 𝕜 E] [Module 𝕜 F]

theorem openSegment_translate_preimage (a b c : E) :
    (fun x => a + x) ⁻¹' openSegment 𝕜 (a + b) (a + c) = openSegment 𝕜 b c :=
  Set.ext fun _ => mem_openSegment_translate 𝕜 a

end OrderedRing
end
