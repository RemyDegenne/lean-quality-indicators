@[expose] public section

namespace Complexity

@[simp]
theorem takeFirstBlock_delimit_append (P Q : List Bool) :
    takeFirstBlock (delimit P ++ Q) = delimit P := by
  induction P with
  | nil => rfl
  | cons b P ih => cases b <;> simp [takeFirstBlock, ih]

end Complexity
end
