@[expose] public section

namespace RS

namespace Fragment

variable {α : Type}

/-- Configuration (2), variant {il}: one cross-edge `W.pairing(bFi) = bFl`.
Both glues are open in both orders; circles = `W.circles`. -/
def oneCrossIlEquiv
    (W : Fragment α) {i j k l : α}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hopen_ij : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (hopen_kl : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag l)
    (hcross : W.pairing (W.boundaryFlag i) = W.boundaryFlag l)
    (hfar_jk : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag k) :
    ((W.gluePairOpen i j hij hopen_ij).gluePairOpen
      ⟨k, hik.symm, hjk.symm⟩ ⟨l, hil.symm, hjl.symm⟩
      (fun h => hkl (congrArg Subtype.val h))
      (by exact (oneCross_il_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_jk))).Equiv
    (((W.gluePairOpen k l hkl hopen_kl).gluePairOpen
      ⟨i, hik, hil⟩ ⟨j, hjk, hjl⟩
      (fun h => hij (congrArg Subtype.val h))
      (by exact (oneCross_il_second_open_ij W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_jk))).relabel
        (swapLabelEquiv hik hil hjk hjl).symm) where
  flagEquiv := by exact doubleSurvivingSwap W hik hil hjk hjl
  vertexEquiv := _root_.Equiv.refl W.Vertex
  attach_comm f := by
    exact doubleGlueAttach_comm W hik hil hjk hjl f
  pairing_comm f := by
    apply Subtype.ext; apply Subtype.ext
    -- ═══════ THE ATTACHMENT AND FLAG SIDES ARE SHARED ═══════
    -- Only the pairing distinguishes this configuration, so what
    -- follows is the five-way case analysis on the partner of the
    -- flag, at the cross-edge this configuration carries.
    -- Name the two single glues; every transport below is
    -- read at one of them.
    let Wij := W.gluePairOpen i j hij hopen_ij
    let Wkl := W.gluePairOpen k l hkl hopen_kl
    let g := doubleSurvivingSwap W hik hil hjk hjl f
    change (rewire (oneCross_il_second_open_kl W hij hkl hik hil hjk hjl
            hopen_ij hopen_kl hcross hfar_jk) f).val.val =
         (rewire (oneCross_il_second_open_ij W hij hkl hik hil hjk hjl
            hopen_ij hopen_kl hcross hfar_jk) g).val.val
    have hli : W.pairing (W.boundaryFlag l) = W.boundaryFlag i :=
      W.pairing_boundaryFlag_comm hcross
    have hfar_kj : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag j := fun h =>
      hfar_jk (W.pairing_boundaryFlag_comm h)
    have hfar_ki : W.pairing (W.boundaryFlag k) ≠ W.boundaryFlag i := fun h =>
      hkl (W.boundaryFlag_injective ((W.pairing_boundaryFlag_comm h).symm.trans
        hcross))
    have hfar_jl : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag l := fun h =>
      hij (W.boundaryFlag_injective (hli.symm.trans (W.pairing_boundaryFlag_comm
        h)))
    let hopen_ij_kl := oneCross_il_second_open_kl W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_jk
    let hopen_kl_ij := oneCross_il_second_open_ij W hij hkl hik hil hjk hjl
        hopen_ij hopen_kl hcross hfar_jk
    rcases partner_cases W f.val.val i l j k with
        hpi | ⟨hpi, hpl⟩ | ⟨hpi, hpl, hpj⟩ | ⟨hpi, hpl, hpj, hpk⟩ |
        ⟨hpi, hpl, hpj, hpk⟩
    · -- Impossible: f.val.val = bFl
      have hfl : f.val.val = W.boundaryFlag l := by
        have h := congrArg W.pairing hpi
        rw [W.pairing_invol] at h
        exact h.trans hcross
      exact absurd (Subtype.ext hfl) f.prop.2
    · -- Impossible: f.val.val = bFi
      have hfi : f.val.val = W.boundaryFlag i := by
        have h := congrArg W.pairing hpl
        rw [W.pairing_invol] at h
        exact h.trans hli
      exact absurd hfi f.val.prop.1
    · -- Case: partner = bFj → both give W.pairing(bFk)
      have lhs_inner : (rewire hopen_ij f.val).val =
          W.pairing (W.boundaryFlag i) :=
        rewire_val_right' hpi hpj
      have lhs_inner_eq_l : (rewire hopen_ij f.val).val = W.boundaryFlag l := by
        rw [lhs_inner, hcross]
      have lhs_outer_ne_k : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
        (fun h' => hkl.symm (W.boundaryFlag_injective h'))
          (lhs_inner_eq_l ▸ congrArg Subtype.val h)
      have lhs_outer_eq_l : Wij.pairing f.val =
          Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ :=
        Subtype.ext lhs_inner_eq_l
      have lhs_k_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
          ⟨k, hik.symm, hjk.symm⟩)).val = W.pairing (W.boundaryFlag k) :=
        rewire_val_ne' hfar_ki hfar_kj
      have lhs_val : (rewire hopen_ij_kl f).val.val =
          W.pairing (W.boundaryFlag k) := by
        have h := rewire_val_right' (hopen := hopen_ij_kl) lhs_outer_ne_k
          lhs_outer_eq_l
        exact congrArg Subtype.val h ▸ lhs_k_rewire
      have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
        change W.pairing f.val.val ≠ _; rw [hpj]
        exact fun h => hjk (W.boundaryFlag_injective h)
      have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
        change W.pairing f.val.val ≠ _; rw [hpj]
        exact fun h => hjl (W.boundaryFlag_injective h)
      have rhs_inner : (rewire hopen_kl g.val).val = W.boundaryFlag j := by
        have h := @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
        rw [h]; exact hpj
      have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
        rw [rhs_inner]; exact fun h => hij.symm (W.boundaryFlag_injective h)
      have rhs_outer_ne_i : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
        rhs_ne_i (congrArg Subtype.val h)
      have rhs_outer_eq_j : Wkl.pairing g.val =
          Wkl.boundaryFlag ⟨j, hjk, hjl⟩ :=
        Subtype.ext rhs_inner
      have rhs_i_ne_k : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag k := fun h
        =>
        hkl (W.boundaryFlag_injective (h.symm.trans hcross))
      have rhs_i_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
          ⟨i, hik, hil⟩)).val = W.pairing (W.boundaryFlag k) :=
        rewire_val_right' rhs_i_ne_k hcross
      have rhs_val : (rewire hopen_kl_ij g).val.val =
          W.pairing (W.boundaryFlag k) := by
        have h := rewire_val_right' (hopen := hopen_kl_ij) rhs_outer_ne_i
          rhs_outer_eq_j
        exact congrArg Subtype.val h ▸ rhs_i_rewire
      rw [lhs_val, rhs_val]
    · -- Case: partner = bFk → both give W.pairing(bFj)
      have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
        rewire_val_ne' hpi hpj
      have lhs_inner_eq_k : (rewire hopen_ij f.val).val = W.boundaryFlag k := by
        rw [lhs_inner, hpk]
      have lhs_outer_eq_k : Wij.pairing f.val =
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ :=
        Subtype.ext lhs_inner_eq_k
      have lhs_l_rewire : (rewire hopen_ij (glueBoundaryFlag W i j
          ⟨l, hil.symm, hjl.symm⟩)).val = W.pairing (W.boundaryFlag j) :=
        rewire_val_left' hli
      have lhs_val : (rewire hopen_ij_kl f).val.val =
          W.pairing (W.boundaryFlag j) := by
        have h := rewire_val_left' (hopen := hopen_ij_kl) lhs_outer_eq_k
        exact congrArg Subtype.val h ▸ lhs_l_rewire
      have rhs_eq_k : W.pairing g.val.val = W.boundaryFlag k := by
        change W.pairing f.val.val = _; exact hpk
      have rhs_inner : (rewire hopen_kl g.val).val =
          W.pairing (W.boundaryFlag l) :=
        @rewire_val_left' _ W k l hopen_kl g.val rhs_eq_k
      have rhs_inner_eq_i : (rewire hopen_kl g.val).val = W.boundaryFlag i := by
        rw [rhs_inner, hli]
      have rhs_outer_eq_i : Wkl.pairing g.val =
          Wkl.boundaryFlag ⟨i, hik, hil⟩ :=
        Subtype.ext rhs_inner_eq_i
      have rhs_j_rewire : (rewire hopen_kl (glueBoundaryFlag W k l
          ⟨j, hjk, hjl⟩)).val = W.pairing (W.boundaryFlag j) :=
        rewire_val_ne' hfar_jk hfar_jl
      have rhs_val : (rewire hopen_kl_ij g).val.val =
          W.pairing (W.boundaryFlag j) := by
        have h := rewire_val_left' (hopen := hopen_kl_ij) rhs_outer_eq_i
        exact congrArg Subtype.val h ▸ rhs_j_rewire
      rw [lhs_val, rhs_val]
    · -- Case: none → both give W.pairing(f.val.val)
      have lhs_inner : (rewire hopen_ij f.val).val = W.pairing f.val.val :=
        rewire_val_ne' hpi hpj
      have lhs_ne_k : (rewire hopen_ij f.val).val ≠ W.boundaryFlag k := by
        rw [lhs_inner]; exact hpk
      have lhs_ne_l : (rewire hopen_ij f.val).val ≠ W.boundaryFlag l := by
        rw [lhs_inner]; exact hpl
      have lhs_outer_ne_k : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨k, hik.symm, hjk.symm⟩ := fun h =>
        lhs_ne_k (congrArg Subtype.val h)
      have lhs_outer_ne_l : Wij.pairing f.val ≠
          Wij.boundaryFlag ⟨l, hil.symm, hjl.symm⟩ := fun h =>
        lhs_ne_l (congrArg Subtype.val h)
      have lhs_val : (rewire hopen_ij_kl f).val.val = W.pairing f.val.val := by
        have h := rewire_val_ne' (hopen := hopen_ij_kl) lhs_outer_ne_k
          lhs_outer_ne_l
        exact congrArg Subtype.val h ▸ lhs_inner
      have rhs_ne_k : W.pairing g.val.val ≠ W.boundaryFlag k := by
        change W.pairing f.val.val ≠ _; exact hpk
      have rhs_ne_l : W.pairing g.val.val ≠ W.boundaryFlag l := by
        change W.pairing f.val.val ≠ _; exact hpl
      have rhs_inner : (rewire hopen_kl g.val).val = W.pairing f.val.val := by
        exact @rewire_val_ne' _ W k l hopen_kl g.val rhs_ne_k rhs_ne_l
      have rhs_ne_i : (rewire hopen_kl g.val).val ≠ W.boundaryFlag i := by
        rw [rhs_inner]; exact hpi
      have rhs_ne_j : (rewire hopen_kl g.val).val ≠ W.boundaryFlag j := by
        rw [rhs_inner]; exact hpj
      have rhs_outer_ne_i : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨i, hik, hil⟩ := fun h =>
        rhs_ne_i (congrArg Subtype.val h)
      have rhs_outer_ne_j : Wkl.pairing g.val ≠
          Wkl.boundaryFlag ⟨j, hjk, hjl⟩ := fun h =>
        rhs_ne_j (congrArg Subtype.val h)
      have rhs_val : (rewire hopen_kl_ij g).val.val = W.pairing f.val.val := by
        have h := rewire_val_ne' (hopen := hopen_kl_ij) rhs_outer_ne_i
          rhs_outer_ne_j
        exact congrArg Subtype.val h ▸ rhs_inner
      rw [lhs_val, rhs_val]
  circles_eq := rfl

end Fragment
end RS
end
