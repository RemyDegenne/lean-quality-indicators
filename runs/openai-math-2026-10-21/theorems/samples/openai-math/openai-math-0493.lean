namespace OAI

noncomputable section

namespace KKLocalPatching.Colored

noncomputable section

variable {A : Type*}

theorem expansion [Ring A] (u v : ℤ → A) (s : List (A × ℤ)) :
    (s.map (fun z => z.1*(u z.2+v z.2))).prod=
      (s.map (fun z => z.1*u z.2)).prod+((changes s).map (value u v)).sum := by
  induction s with
  | nil => simp [changes]
  | cons z s ih =>
    simp only [changes,List.map_cons,List.prod_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,value_cons,Bool.false_eq_true,ite_false,ite_true,
      List.sum_cons,value_old,ih]
    simp only [List.sum_map_mul_left]
    noncomm_ring

end
end KKLocalPatching.Colored
end
end OAI
