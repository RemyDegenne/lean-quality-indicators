public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

open CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

theorem val_sub_mul (a b c d : ZMod 3) :
    (a * b - c * d).val = (a.val * b.val + 2 * (c.val * d.val)) % 3 := by
  revert a b c d
  decide +kernel

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
end
