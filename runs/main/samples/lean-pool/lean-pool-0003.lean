@[expose] public section

namespace Turan3

variable {α : Type*} (G : SimpleGraph α)

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj]

local notation "V" => @Finset.univ α _

local notation "E" => G.edgeFinset

local notation "n" => Fintype.card α

open Finset SimpleGraph

lemma Enhance_loose_sum (W : FunToMax G) (loose gain : α) (h_lt : W.w gain < W.w loose)
  (ε : NNReal) (epos : 0 < ε) (elt : ε < W.w loose - W.w gain) :
  ∑ e∈((supIncidenceFinset G W loose) \ {s(loose,gain)}), vp
      (Enhance G W loose gain h_lt ε epos elt).w e =
  ∑ e∈((supIncidenceFinset G W loose) \ {s(loose,gain)}), vp W.w e -
  ε * ∑ e∈((supIncidenceFinset G W loose) \ {s(loose,gain)}).attach, W.w
      (Sym2.Mem.other (helper_gain_mem G e.val (small_helpI G (in_sdiff_left e.prop)))) := by
  rw [mul_sum]
  have h_tec : ε ≤ W.w loose := by
    replace elt := add_le_of_le_tsub_left_of_le (le_of_lt h_lt) (le_of_lt elt)
    apply le_trans (le_add_of_nonneg_left (W.w gain).prop) elt
  nth_rewrite 2 [← sum_attach]
  rw [← sum_tsub_distrib _ (epsilon_weight_bound G W loose gain h_lt ε epos elt)]
  rw [← sum_attach]
  apply Finset.sum_congr rfl
  intro x hx
  have dummy := x.prop
  revert dummy
  have tec : (↑x ∈ supIncidenceFinset G W loose \ {s(loose, gain)} →
    vp (Enhance G W loose gain h_lt ε epos elt).w ↑x = vp W.w ↑x - ε * W.w
        (Sym2.Mem.other (helper_gain_mem G (↑x) (small_helpI G (in_sdiff_left (Subtype.prop x))))))
    = (fun X => ((HX : X ∈ supIncidenceFinset G W loose \ {s(loose, gain)}) →
    vp (Enhance G W loose gain h_lt ε epos elt).w X = vp W.w X - ε * W.w
        (Sym2.Mem.other (helper_gain_mem G (X) (small_helpI G (in_sdiff_left (HX)))))))
      ↑x := by
    dsimp
  rw [tec]
  clear tec
  dsimp
  apply @Sym2.inductionOn α (fun X => ∀ (HX : X ∈ supIncidenceFinset G W loose \ {s(loose, gain)}),
    vp (Enhance G W loose gain h_lt ε epos elt).w X =
    vp W.w X - ε * W.w
        (Sym2.Mem.other (helper_gain_mem G (X) (small_helpI G (in_sdiff_left HX))))) ↑x
  intro a b hab
  dsimp [vp]
  rw [mem_sdiff, notMem_singleton, mem_supIncidenceFinset, mem_incidenceFinset,
      mk'_mem_incidenceSet_iff] at hab
  obtain ⟨⟨⟨abAdj, Q⟩, abSupp⟩, abnot⟩ := hab
  rcases Q with Q1 | Q2
  · have nb : b ≠ loose := by
      intro h; subst h; subst Q1; exact (G.ne_of_adj abAdj) rfl
    have ng : b ≠ gain := by
      simp_all
    dsimp [Enhance] at *
    subst Q1
    dsimp only [Quot.liftOn]
    simp only [↓reduceIte, nb, ng, Sym2.other_eq_other']
    have tec : Sym2.Mem.other' (helper_gain_mem G s(loose, b) (small_helpI G (in_sdiff_left hab))) =
        b := by
      have := Sym2.other_spec' (helper_gain_mem G s(loose, b) (small_helpI G (in_sdiff_left hab)))
      rw [Sym2.eq_iff] at this
      rcases this with q | q
      · exact q.2
      · simp_all
    rw [tec]; rw [@tsub_mul]
  · have na : a ≠ loose := by
      intro h; subst h; subst Q2; exact (G.ne_of_adj abAdj) rfl
    have ng : a ≠ gain := by
      simp_all
    dsimp [Enhance] at *
    subst Q2
    dsimp only [Quot.liftOn]
    simp only [na, ↓reduceIte, ng, Sym2.other_eq_other']
    have tec : Sym2.Mem.other' (helper_gain_mem G s(a, loose) (small_helpI G (in_sdiff_left hab))) =
        a := by
      have := Sym2.other_spec' (helper_gain_mem G s(a, loose) (small_helpI G (in_sdiff_left hab)))
      rw [Sym2.eq_iff] at this
      rcases this with q | q
      · simp_all
      · simp_all
    rw [tec]; rw [@mul_tsub]; rw[mul_comm ε  (W.w a)]

end Turan3
end
