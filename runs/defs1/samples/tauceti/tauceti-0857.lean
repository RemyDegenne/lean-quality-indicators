public section

namespace TauCeti

namespace Sym

variable {α : Type*} {n : ℕ} {A B : Fin n → Set α}

/-- **The unordered tuples with one point in each member of a pairwise disjoint family are the
product of its members.** For the attaching curves of a Heegaard diagram this identifies `T_α`
with `α₁ × ⋯ × α_g`. -/
noncomputable def piEquiv (h : Pairwise (Function.onFun Disjoint A)) :
    (∀ i, ↥(A i)) ≃ ↥(pi A) :=
  Equiv.ofBijective (fun x => ⟨ofFn fun i => (x i : α), ofFn_mem_pi fun i => (x i).2⟩)
    ⟨fun _ _ hxy => ofFn_subtypeVal_injective h (congrArg Subtype.val hxy), by
      rintro ⟨s, hs⟩
      obtain ⟨x, hx, rfl⟩ := mem_pi_iff.1 hs
      exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩⟩

end Sym
end TauCeti
end
