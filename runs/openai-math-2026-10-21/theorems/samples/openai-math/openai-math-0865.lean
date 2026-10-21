namespace OAI

namespace TuringRigidity.GuardedStage

open Encodable CodingForcing EncodedForcing FiniteInjury

noncomputable section

attribute [local instance] Classical.propDecidable

theorem scan_spec {A : Oracle} {p : Condition} {done : Finset ℕ} {t n i : ℕ}
    (h : scan A p done t n = some i) :
    t ≤ i ∧ i < t+n ∧ i ∉ done ∧ Changes A i p := by
  induction n generalizing t with
  | zero => simp [scan] at h
  | succ n ih =>
    simp only [scan] at h
    split at h
    · rename_i ht
      have he := Option.some.inj h
      subst i
      exact ⟨le_rfl,by omega,ht⟩
    · obtain ⟨hlo,hhi,hd,hc⟩ := ih h
      exact ⟨by omega,by omega,hd,hc⟩

end
end TuringRigidity.GuardedStage
end OAI
