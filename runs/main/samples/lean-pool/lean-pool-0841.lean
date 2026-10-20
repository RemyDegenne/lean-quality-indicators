@[expose] public section

namespace LeanPool.DemazureProduct

namespace AspPerm

variable (τ : AspPerm)

lemma inset_eq_nw (v : ℤ) : τ.inset v = northwestSet τ (τ v) v := by
  ext u
  constructor
  · intro uv_inv
    obtain ⟨u_lt_v, τv_lt_τu⟩ := uv_inv
    exact ⟨u_lt_v, le_of_lt τv_lt_τu⟩
  · intro uv_se
    obtain ⟨u_lt_v, τv_le_τu⟩ := uv_se
    exact (τ.inv_iff_le u_lt_v).mpr τv_le_τu

end AspPerm
end LeanPool.DemazureProduct
end
