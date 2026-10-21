namespace OAI

namespace UniqueGamesTheorem.Integration.TableReduction

open BinaryLinear NoiseTables UniqueGamesTheorem.Reduction.ActualSource

open UniqueGamesTheorem.Reduction.ActualGame UniqueGamesTheorem.Foundations.Target

variable {s d : Nat}

theorem completeAt_ofEnumeration_iff (error : RationalError)
    (S : Source) (k : Nat) (g : SplitGadget s d) (en : NoiseEnumeration g) :
    CompleteAt error (output S k (Table.ofEnumeration g en)) ↔
      CompleteAt error (outputInstance S k g) := by
  rw [completeAt_output_iff error S k _ g.f g.equivariant]
  rw [GapSemantics.completeAt_iff, GapSemantics.completeAt_iff]
  constructor
  · rintro ⟨label, h⟩
    exact ⟨label, h.trans_eq (rate_ofEnumeration S k g en label)⟩
  · rintro ⟨label, h⟩
    exact ⟨label, h.trans_eq (rate_ofEnumeration S k g en label).symm⟩

end UniqueGamesTheorem.Integration.TableReduction
end OAI
