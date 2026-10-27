public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] {C : ι → Type} [∀ i, Group (C i)]
  [∀ i, Finite (C i)] {f : ℕ}

variable [Fact f.Prime]

theorem exists_pi_sylow (F : Subgroup (∀ i, C i)) (hFp : IsPGroup f F)
    (hFmax : ∀ Q : Subgroup (∀ i, C i), IsPGroup f Q → F ≤ Q → Q = F) :
    (∀ i, IsPGroup f (F.map (Pi.evalMonoidHom C i))) ∧
    (F = Subgroup.pi Set.univ fun i => F.map (Pi.evalMonoidHom C i)) ∧
    ∀ i, ∀ Q : Subgroup (C i), IsPGroup f Q → F.map (Pi.evalMonoidHom C i) ≤ Q →
      Q = F.map (Pi.evalMonoidHom C i) := by
  have hFi : ∀ i, IsPGroup f (F.map (Pi.evalMonoidHom C i)) := fun i => hFp.map _
  have hFle : F ≤ Subgroup.pi Set.univ fun i => F.map (Pi.evalMonoidHom C i) := fun x hx =>
    (Subgroup.mem_pi Set.univ).mpr fun i _ => ⟨x, hx, rfl⟩
  have hpi : IsPGroup f (Subgroup.pi Set.univ fun i => F.map (Pi.evalMonoidHom C i)) := by
    apply isPGroup_of_map_eval
    intro i
    refine (hFi i).to_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_pi Set.univ).mp hx i (Set.mem_univ i)
  have hFeq : F = Subgroup.pi Set.univ fun i => F.map (Pi.evalMonoidHom C i) :=
    (hFmax _ hpi hFle).symm
  refine ⟨hFi, hFeq, fun i Q hQ hFQ => ?_⟩
  let U' : Subgroup (∀ j, C j) :=
    Subgroup.pi {j | j ≠ i} (fun j => F.map (Pi.evalMonoidHom C j)) ⊓
      Q.comap (Pi.evalMonoidHom C i)
  have hU'p : IsPGroup f U' := by
    apply isPGroup_of_map_eval
    intro j
    by_cases h : j = i
    · subst h
      refine hQ.to_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · refine (hFi j).to_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_pi _).mp hx.1 j h
  have hFle' : F ≤ U' := fun x hx =>
    ⟨(Subgroup.mem_pi _).mpr fun j _ => ⟨x, hx, rfl⟩, hFQ ⟨x, hx, rfl⟩⟩
  have hU'F : U' = F := hFmax _ hU'p hFle'
  apply le_antisymm
  · intro q hq
    have hmem : (Pi.mulSingle i q : ∀ j, C j) ∈ U' := by
      refine ⟨(Subgroup.mem_pi _).mpr fun j hj => ?_, ?_⟩
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact Subgroup.one_mem _
      · show (Pi.mulSingle i q : ∀ j, C j) i ∈ Q
        rw [Pi.mulSingle_eq_same]
        exact hq
    rw [hU'F] at hmem
    exact ⟨_, hmem, by simp⟩
  · exact hFQ

end Pi
end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
end
