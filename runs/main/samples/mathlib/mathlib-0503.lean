@[expose] public section

open Set

open scoped Pointwise Topology

variable {𝕜 𝕝 E F : Type*} {ι : Sort*} {κ : ι → Sort*}

section SeminormedRing

variable [SeminormedRing 𝕜]

section Module

variable [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

theorem Balanced.neg_eq [NormOneClass 𝕜] (h : Balanced 𝕜 s) : -s = s :=
  Set.ext fun _ ↦ h.neg_mem_iff

end Module
end SeminormedRing
end
