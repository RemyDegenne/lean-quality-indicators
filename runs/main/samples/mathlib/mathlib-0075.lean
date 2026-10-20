public section

variable {α β : Type*}

namespace List

namespace Palindrome

variable {l : List α}

theorem of_reverse_eq {l : List α} : reverse l = l → Palindrome l := by
  refine bidirectionalRecOn l (fun _ => Palindrome.nil) (fun a _ => Palindrome.singleton a) ?_
  intro x l y hp hr
  rw [reverse_cons, reverse_append] at hr
  rw [head_eq_of_cons_eq hr]
  have : Palindrome l := hp (append_inj_left' (tail_eq_of_cons_eq hr) rfl)
  exact Palindrome.cons_concat x this

end Palindrome
end List
end
