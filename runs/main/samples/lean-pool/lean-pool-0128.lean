@[expose] public section

namespace PDL

open HasSat

theorem localInterpolantStep_oneSidedR (L R : Finset Formula) (o : Olf) (Rcond : Finset
  Formula)
  (ress_1 C : Finset Sequent) {ress : Finset (Finset Formula)} (orule : OneSidedLocalRule Rcond
    ress)
  (rule : LocalRule (∅, Rcond, none) ress_1) (hC : C = applyLocalRule rule (L, R, o))
  (precondProof : ∅ ⊆ L ∧ Rcond ⊆ R ∧ none ⊆ o)
  (subθs : ∀ c ∈ C, PartInterpolant c)
  (YS_def : ress_1 = Finset.image (fun res ↦ (∅, res, none)) ress)
  (def_rule : rule = LocalRule.oneSidedR orule YS_def) :
  let interSet := Finset.image (fun c ↦ (subθs c.1 c.2).1) C.attach;
  isPartInterpolant
    ({ L := L, R := R, O := o, Rcond := Rcond, ress := ress_1,
        lr := LocalRule.oneSidedR orule YS_def, C := C, hC := hC,
        preconditionProof := precondProof } : LocalRuleApp).X
    (con interSet.pdlSort) := by
  intro interSet
  refine ⟨?_, ?_, ?_⟩
  · intro n n_in_inter
    rw [in_voc_con] at n_in_inter
    rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
    exact childInterpolant_voc subθs (localRuleApp_does_not_increase_jvoc
      ({ L := L, R := R, O := o, Rcond := Rcond, ress := ress_1,
          lr := LocalRule.oneSidedR orule YS_def, C := C, hC := hC,
          preconditionProof := precondProof } : LocalRuleApp)) φ_in n_in_voc_φ
  · rintro ⟨W, M, w, w_⟩
    have w_ncon : ¬ evaluate M w (con interSet.pdlSort) :=
      w_ (~ con interSet.pdlSort) (by simp)
    rw [conEval] at w_ncon
    push Not at w_ncon
    rcases w_ncon with ⟨θi, θi_in, w_nθi⟩
    rw [Formula.mem_pdlSort] at θi_in
    simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and,
      Subtype.exists] at θi_in
    rcases θi_in with ⟨c, c_in, def_θi⟩
    have same_L : c.left = Sequent.left (L,R,o) :=
      @oneSidedR_preserves_left (L,R,o) _ precondProof.2.1 _ orule _ YS_def c (hC ▸ c_in)
    refine (subθs c (hC ▸ c_in)).2.2.1 ⟨W, M, w, ?_⟩
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      rw [def_θi]
      exact w_nθi
    · rw [same_L] at h
      exact w_ φ (Finset.mem_union_right _ h)
  · rintro inter_R_sat
    have RI_sat := satisfiable_con_union inter_R_sat
    have := oneSidedR_sat_down ⟨L,R,o⟩ precondProof.2.1 orule YS_def RI_sat
    rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
    have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in
    refine (subθs ⟨L', R', o'⟩ c_in').2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
    intro φ φ_in
    rcases Finset.mem_union.mp φ_in with h | h
    · rw [Finset.mem_singleton] at h
      subst h
      refine w_ _ (Finset.mem_union_right _ ?_)
      simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨(L', R', o'), c_in', rfl⟩
    · exact w_ φ (Finset.mem_union_left _ h)

end PDL
end
