@[expose] public section

open Function Set

open Monoid.Coprod

noncomputable section

namespace MarshallHall

variable {G H : Type*} [Group G] [Group H]

namespace GeneralGrushko

theorem rank_add_le_of_separated_generators {n : ℕ} (s : Fin n → Sum G H)
    [Group.FG G] [Group.FG H]
    (hs : Subgroup.closure (Set.range (separatedMap ∘ s)) = ⊤) :
    Group.rank G + Group.rank H ≤ n := by
  classical
  let A : Finset G := leftGenerators s
  let B : Finset H := rightGenerators s
  have hA : Subgroup.closure (A : Set G) = ⊤ := by
    simpa [A] using separated_left_closure s hs
  have hB : Subgroup.closure (B : Set H) = ⊤ := by
    simpa [B] using separated_right_closure s hs
  have hrank : Group.rank G + Group.rank H ≤ A.card + B.card :=
    Nat.add_le_add (Group.rank_le hA) (Group.rank_le hB)
  have hcardA : A.card ≤ Fintype.card (leftIndex s) := by
    dsimp [A]
    exact Finset.card_image_le
  have hcardB : B.card ≤ Fintype.card (rightIndex s) := by
    dsimp [B]
    exact Finset.card_image_le
  have hindices : Fintype.card (leftIndex s) + Fintype.card (rightIndex s) = n := by
    let p : Fin n → Prop := fun i => ∃ g : G, s i = Sum.inl g
    have hcomp := @Fintype.card_subtype_compl (Fin n) inferInstance p
      (leftIndexFintype s) (rightIndexFintype s)
    have hle := @Fintype.card_subtype_le (Fin n) inferInstance p (leftIndexFintype s)
    have hcomp' : Fintype.card (rightIndex s) = Fintype.card (Fin n) -
        Fintype.card (leftIndex s) := by
      simpa [leftIndex, rightIndex, p] using hcomp
    have hle' : Fintype.card (leftIndex s) ≤ Fintype.card (Fin n) := by
      simpa [leftIndex, p] using hle
    calc
      Fintype.card (leftIndex s) + Fintype.card (rightIndex s) =
          Fintype.card (leftIndex s) +
            (Fintype.card (Fin n) - Fintype.card (leftIndex s)) := by rw [hcomp']
      _ = Fintype.card (Fin n) := Nat.add_sub_of_le hle'
      _ = n := Fintype.card_fin n
  exact hrank.trans ((Nat.add_le_add hcardA hcardB).trans_eq hindices)

end GeneralGrushko
end MarshallHall
end
end
