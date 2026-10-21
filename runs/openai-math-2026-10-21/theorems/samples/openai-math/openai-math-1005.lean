namespace OAI

section

namespace ElementaryPositivity.LinearDetection

open scoped TensorProduct

variable {K A B C D : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]

lemma middleInsert_mem_filtration
    (P : ℤ → Submodule K A) (Q : ℤ → Submodule K B)
    (R : ℤ → Submodule K C) (S : ℤ → Submodule K D)
    (u z W : ℤ) (a : A) (d : D) (ha : a∈P u) (hd : d∈S z)
    (x : C⊗[K]B) (hx : x∈additiveTensorFiltration R Q W) :
    middleInsert a d x∈
      additiveTensorFiltration (additiveTensorFiltration P R)
        (additiveTensorFiltration Q S) (u+W+z) := by
  let J:=additiveTensorFiltration (additiveTensorFiltration P R)
    (additiveTensorFiltration Q S) (u+W+z)
  change middleInsert a d x∈J
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,w,c,b,hw,hc,hb,rfl⟩:=hx
    rw [middleInsert_tmul]
    exact tmul_mem_additiveTensorFiltration _ _ (show u+W+z≤(u+v)+(w+z) by omega)
      (tmul_mem_additiveTensorFiltration P R (le_refl _) ha hc)
      (tmul_mem_additiveTensorFiltration Q S (le_refl _) hb hd)
  | zero => rw [map_zero]; exact J.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact J.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact J.smul_mem r hx

end ElementaryPositivity.LinearDetection
end
end OAI
