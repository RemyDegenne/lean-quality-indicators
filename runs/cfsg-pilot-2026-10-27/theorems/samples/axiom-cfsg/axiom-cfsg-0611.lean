public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.Open
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Group

theorem exists_elemAbelian_of_commute_disjoint {G : Type*} [Group G] {A B S : Subgroup G}
    (hAS : A ≤ S) (hBS : B ≤ S) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : Disjoint A B)
    (hA : IsElemAbelian 5 A) (hB : IsElemAbelian 5 B) :
    ∃ E : Subgroup G, A ≤ E ∧ B ≤ E ∧ E ≤ S ∧ IsElemAbelian 5 E ∧
      Nat.card E = Nat.card A * Nat.card B := by
  have hcomm : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n => hc m m.2 n n.2
  set φ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm with hφ
  have hinj : Function.Injective φ := by
    rw [hφ, MonoidHom.noncommCoprod_injective]
    exact ⟨A.subtype_injective, B.subtype_injective, by simpa using hd⟩
  refine ⟨φ.range, ?_, ?_, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · intro a ha
    exact ⟨(⟨a, ha⟩, 1), by simp [hφ]⟩
  · intro b hb
    exact ⟨(1, ⟨b, hb⟩), by simp [hφ]⟩
  · rintro _ ⟨⟨m, n⟩, rfl⟩
    exact mul_mem (hAS m.2) (hBS n.2)
  · obtain ⟨_, ⟨m, n⟩, rfl⟩ := a
    obtain ⟨_, ⟨m', n'⟩, rfl⟩ := b
    apply Subtype.ext
    show φ (m, n) * φ (m', n') = φ (m', n') * φ (m, n)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (hA.1.1.comm m m') (hB.1.1.comm n n')
  · rintro _ ⟨⟨m, n⟩, rfl⟩
    rw [← map_pow]
    have h1 : m ^ 5 = 1 := Subtype.ext (hA.2 m m.2)
    have h2 : n ^ 5 = 1 := Subtype.ext (hB.2 n n.2)
    rw [Prod.pow_mk, h1, h2]
    exact map_one φ
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod]

end Group
end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
end
