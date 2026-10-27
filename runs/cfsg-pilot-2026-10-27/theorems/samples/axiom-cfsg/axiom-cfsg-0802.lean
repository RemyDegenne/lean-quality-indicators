public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag)

section LabelEval

theorem componentLabel_twoD (r N n : ℕ) :
    componentLabel r N .twoD n = ⟨LargeEvenLieTag.twD, r, n⟩ := rfl

end LabelEval
end CFSG.StandardType.TableCRes
end
