public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Quasithin

open scoped Matrix

theorem decode_vecCode {v : Array ℕ} (i j : Fin 6) :
    decode (vecCode v) i j = if j.val = 0 then GF8.ofNat' v[i.val]! else 0 := by
  have ht : 6 * i.val + j.val < 36 := by have := i.2; have := j.2; omega
  have e1 : (6 * i.val + j.val) / 6 = i.val := by omega
  have e2 : (6 * i.val + j.val) % 6 = j.val := by omega
  simp only [decode, Matrix.of_apply]
  rw [vecCode, getElem!_ofFn_nat' _ ht]
  simp only [e1, e2]
  split_ifs
  · rfl
  · rfl

end CFSG.RankThree.PartTwo.Sec4.Item434G28
end
