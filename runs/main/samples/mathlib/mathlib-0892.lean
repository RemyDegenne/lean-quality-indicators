public section

universe u v w

open scoped Topology Filter ENNReal

open Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f g : 𝕜 → F}

variable {f' g' : F}

variable {x : 𝕜} {s : Set 𝕜} {L : Filter (𝕜 × 𝕜)}

section Sub

@[simp]
theorem deriv_const_sub' (c : F) : deriv (c - f ·) = (-deriv f ·) :=
  funext fun _ => deriv_const_sub c

end Sub
end
