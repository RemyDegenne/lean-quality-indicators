public section

noncomputable section

open scoped Uniformity Topology

open Filter UniformSpace Function Set

universe u

variable {ι ι' β : Type*} (α : ι → Type u) [U : ∀ i, UniformSpace (α i)] [UniformSpace β]

variable {α}

variable (α)

theorem Pi.uniformContinuous_postcomp' {β : ι → Type*} [∀ i, UniformSpace (β i)]
    {g : ∀ i, α i → β i} (hg : ∀ i, UniformContinuous (g i)) :
    UniformContinuous (fun (f : (∀ i, α i)) (i : ι) ↦ g i (f i)) :=
  uniformContinuous_pi.mpr fun i ↦ (hg i).comp <| uniformContinuous_proj α i

end
end
