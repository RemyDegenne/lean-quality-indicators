open Equiv

public section

namespace TauCeti

namespace PermutationTriple

variable {n : ℕ}

variable (t : PermutationTriple n)

variable {t}

variable (t)

variable {t}

section mapMonodromy

variable {m : ℕ} (t : PermutationTriple n) (f : t.monodromyGroup →* Perm (Fin m))

theorem monodromyGroup_mapMonodromy : (t.mapMonodromy f).monodromyGroup = f.range := by
  have hgen : Subgroup.closure ({⟨t.σ0, t.σ0_mem_monodromyGroup⟩,
      ⟨t.σ1, t.σ1_mem_monodromyGroup⟩} : Set t.monodromyGroup) = ⊤ := by
    rw [← Subgroup.map_subtype_inj, MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype]
    rw [closure_pair_eq_monodromyGroup, ← MonoidHom.range_eq_map]
    simp
  rw [monodromyGroup, mapMonodromy_σ0, mapMonodromy_σ1, ← Set.image_singleton,
    ← Set.image_insert_eq, ← MonoidHom.map_closure, hgen, MonoidHom.range_eq_map]

end mapMonodromy
end PermutationTriple
end TauCeti
end
