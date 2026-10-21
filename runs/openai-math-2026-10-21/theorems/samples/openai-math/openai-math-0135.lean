namespace OAI

section

section

section

section

noncomputable section

namespace CannonQM

open Metric

open scoped NNReal

lemma Distinct.map {X Y : Type*} {f : X → Y} (hf : Function.Injective f)
    {x y z w : X} (h : Distinct x y z w) : Distinct (f x) (f y) (f z) (f w) := by
  rcases h with ⟨hxy,hxz,hxw,hyz,hyw,hzw⟩
  exact ⟨fun h => hxy (hf h),fun h => hxz (hf h),fun h => hxw (hf h),
    fun h => hyz (hf h),fun h => hyw (hf h),fun h => hzw (hf h)⟩

end CannonQM
end
end
end
end
end
end OAI
