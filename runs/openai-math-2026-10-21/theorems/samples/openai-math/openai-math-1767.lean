namespace OAI

noncomputable section

open scoped ComplexOrder

open Filter Topology

namespace HochschildCatalanWords

noncomputable section

open List BinaryTree

variable {α : Type*}

theorem word_injective_on_nodup {t u : BinaryTree α}
    (ht : (labels t).Nodup) (hu : (labels u).Nodup) (he : word t = word u) : t=u := by
  induction t generalizing u with
  | nil =>
    cases u with
    | nil => rfl
    | node b l r => simp [word] at he
  | node a l r ihl ihr =>
    cases u with
    | nil => simp [word] at he
    | node b l' r' =>
      simp only [word, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      have ht' := List.nodup_cons.mp ht
      have hu' := List.nodup_cons.mp hu
      have htl := List.nodup_append.mp ht'.2
      have hul := List.nodup_append.mp hu'.2
      obtain ⟨hel, her⟩ := delimiter_split
        (fun h => ht'.1 (List.mem_append_left _ ((mem_word_iff _ _).mp h)))
        (fun h => hu'.1 (List.mem_append_left _ ((mem_word_iff _ _).mp h))) he
      rw [ihl htl.1 hul.1 hel, ihr htl.2.1 hul.2.1 her]

end
end HochschildCatalanWords
end
end OAI
