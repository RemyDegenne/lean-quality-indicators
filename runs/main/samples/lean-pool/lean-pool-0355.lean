@[expose] public section

namespace PDL

open Typ

open QuasiTab

namespace QuasiTab

lemma mem_addresses_of_atOpt (q : QuasiTab) (x : List Nat) (h : (q.atOpt x).isSome) :
    x ∈ q.addresses := by
  induction x generalizing q with
  | nil => cases q with | QNode k Δ next => simp [addresses]
  | cons i rest ih =>
    cases q with
    | QNode k Δ next =>
      simp only [atOpt] at h
      cases hc : next[i]? with
      | none => rw [show (QNode k Δ next).children = next from rfl, hc] at h; simp at h
      | some c =>
        rw [show (QNode k Δ next).children = next from rfl, hc] at h
        simp only [addresses, List.mem_cons, List.mem_flatMap, List.mem_map]
        refine Or.inr ⟨(c.addresses, i), ?_, rest, ih c h, rfl⟩
        rw [List.mem_zipIdx_iff_getElem?]
        simp [hc]

end QuasiTab
end PDL
end
