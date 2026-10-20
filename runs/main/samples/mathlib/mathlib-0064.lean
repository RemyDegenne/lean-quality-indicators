@[expose] public section

universe u v w

namespace Stream'.WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

@[inherit_doc] infixl:50 " ~ʷ " => Equiv

open Computation

@[simp]
theorem join_join (SS : WSeq (WSeq (WSeq α))) : join (join SS) ~ʷ join (map join SS) := by
  refine
    ⟨fun s1 s2 =>
      ∃ s S SS,
        s1 = append s (join (append S (join SS))) ∧
          s2 = append s (append (join S) (join (map join SS))),
      ⟨nil, nil, SS, by simp, by simp⟩, ?_⟩
  intro s1 s2 h
  apply
    liftRel_rec
      (fun c1 c2 =>
        ∃ s S SS,
          c1 = destruct (append s (join (append S (join SS)))) ∧
            c2 = destruct (append s (append (join S) (join (map join SS)))))
      _ (destruct s1) (destruct s2)
      (let ⟨s, S, SS, h1, h2⟩ := h
      ⟨s, S, SS, by simp [h1], by simp [h2]⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | _, _, ⟨s, S, SS, rfl, rfl⟩ => by
      clear h
      induction s using WSeq.recOn with
      | nil =>
        induction S using WSeq.recOn with
        | nil =>
          simp only [nil_append, join_nil]
          induction SS using WSeq.recOn with
          | nil => simp
          | cons S SS => refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
          | think SS => refine ⟨nil, nil, SS, ?_, ?_⟩ <;> simp
        | cons s S => simpa using ⟨s, S, SS, rfl, rfl⟩
        | think S => refine ⟨nil, S, SS, ?_, ?_⟩ <;> simp
      | cons a s => simpa using ⟨s, S, SS, rfl, rfl⟩
      | think s => simpa using ⟨s, S, SS, rfl, rfl⟩

end Stream'.WSeq
end
