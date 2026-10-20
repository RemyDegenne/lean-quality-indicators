@[expose] public section

@[inherit_doc]
notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

namespace Int

variable {m n a b c d : ℤ}

theorem _root_.Dvd.dvd.modEq_zero_int (h : n ∣ a) : a ≡ 0 [ZMOD n] :=
  modEq_zero_iff_dvd.2 h

end Int
end
