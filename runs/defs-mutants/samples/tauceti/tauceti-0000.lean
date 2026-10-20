public noncomputable section

universe u

open CategoryTheory Limits

namespace Rep

variable (k G : Type u) [CommRing k] [Group G]

/-- The inclusion of the augmentation ideal into the left regular representation. -/
def augmentationι : augmentationIdeal k G ⟶ leftRegular k G := kernel.ι (augmentation k G)

end Rep
end
