@[expose] public section

namespace Champernowne

theorem countOccurrences_append_le (w a b : List ℕ) :
    countOccurrences w (a ++ b)
      ≤ countOccurrences w a + countOccurrences w b + w.length :=
  (countOccurrences_append_le_min w a b).trans
    (Nat.add_le_add_left (Nat.min_le_left _ _) _)

end Champernowne
end
