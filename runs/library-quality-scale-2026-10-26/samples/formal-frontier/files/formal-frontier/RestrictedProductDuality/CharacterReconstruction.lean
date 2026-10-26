/-
Released under Apache 2.0 license as described in LICENSE.
Authors: Formal Frontier Agents
-/
module

public import RestrictedProductDuality.CompactStage
public import RestrictedProductDuality.SmallArc
public import RestrictedProductDuality.TopologicalPairing

/-!
# Character reconstruction for restricted products

This file reconstructs a character of a cofinite restricted product from its local coordinate
characters.  Continuity forces finite coordinate dependence on the open distinguished product;
local perfectness then supplies the coordinates of the representing element, and an exact
annihilator equality makes that element restricted.
-/

public section

set_option warningAsError true

open Filter Function Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X Y : ι → Type*}
variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]
variable (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))
variable (e : ∀ i, X i →* Y i →* Circle)

/-- The character of `X` represented by `y` through a multiplicative bicharacter. -/
@[expose] noncomputable def rightCharacter {X Y : Type*} [CommGroup X] [CommGroup Y]
    (e : X →* Y →* Circle) : Y →* (X →* Circle) where
  toFun y :=
    { toFun := fun x ↦ e x y
      map_one' := by simp
      map_mul' := fun x x' ↦ by simp }
  map_one' := MonoidHom.ext fun x ↦ by simp
  map_mul' y y' := MonoidHom.ext fun x ↦ by simp

@[simp]
theorem rightCharacter_apply {X Y : Type*} [CommGroup X] [CommGroup Y]
    (e : X →* Y →* Circle) (y : Y) (x : X) :
    rightCharacter e y x = e x y :=
  rfl

/-- The right annihilator of a subgroup under a multiplicative bicharacter. -/
@[expose] def rightAnnihilator {X Y : Type*} [CommGroup X] [CommGroup Y]
    (U : Subgroup X) (e : X →* Y →* Circle) : Subgroup Y where
  carrier := {y | ∀ x, x ∈ U → e x y = 1}
  one_mem' := by simp
  mul_mem' hy hy' x hx := by simp [hy x hx, hy' x hx]
  inv_mem' hy x hx := by simp [hy x hx]

@[simp]
theorem mem_rightAnnihilator {X Y : Type*} [CommGroup X] [CommGroup Y]
    {U : Subgroup X} {e : X →* Y →* Circle} {y : Y} :
    y ∈ rightAnnihilator U e ↔ ∀ x, x ∈ U → e x y = 1 :=
  Iff.rfl

/-- The distinguished product, bundled as a homomorphism into the cofinite restricted product. -/
@[expose] def structureMapMonoidHom : (∀ i, U i) →* (Πʳ i, [X i, U i]) where
  toFun := structureMap X (fun i ↦ (U i : Set (X i))) cofinite
  map_one' := RestrictedProduct.ext X (fun i ↦ (U i : Set (X i))) fun _ ↦ rfl
  map_mul' _ _ := RestrictedProduct.ext X (fun i ↦ (U i : Set (X i))) fun _ ↦ rfl

@[simp]
theorem structureMapMonoidHom_apply (u : ∀ i, U i) (i : ι) :
    structureMapMonoidHom U u i = u i :=
  rfl

/-- Elements of the distinguished product which are `1` on `s`. -/
def productTail (s : Finset ι) : Subgroup (∀ i, U i) :=
  Subgroup.pi (s : Set ι) fun _ ↦ ⊥

/-- The product tail, embedded as a subgroup of the cofinite restricted product. -/
def restrictedProductTail (s : Finset ι) : Subgroup (Πʳ i, [X i, U i]) :=
  (productTail U s).map (structureMapMonoidHom U)

@[simp]
theorem mem_productTail {s : Finset ι} {u : ∀ i, U i} :
    u ∈ productTail U s ↔ ∀ i ∈ s, u i = 1 := by
  simp [productTail, Subgroup.mem_pi]

open scoped Classical in
@[simp]
theorem structureMapMonoidHom_pi_mulSingle (i : ι) (u : U i) :
    structureMapMonoidHom U (Pi.mulSingle i u) = mulSingle U i u := by
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Pi.mulSingle, hji]

variable [∀ i, TopologicalSpace (X i)]

/-- Continuity of a character forces its restriction to the distinguished product to annihilate
all coordinates outside one finite set.

The index type is arbitrary.  The proof pulls a centered small arc back to the product, chooses a
finite cylinder contained in that preimage, and applies `Subgroup.le_ker_of_mapsTo_centeredArc` to
the corresponding product tail. -/
theorem exists_productTail_le_ker
    (hUopen : ∀ i, IsOpen (U i : Set (X i)))
    (χ : PontryaginDual (Πʳ i, [X i, U i])) :
    ∃ s : Finset ι,
      productTail U s ≤ (χ.toMonoidHom.comp (structureMapMonoidHom U)).ker := by
  classical
  let f : (∀ i, U i) →* Circle := χ.toMonoidHom.comp (structureMapMonoidHom U)
  have hf : Continuous f := χ.continuous.comp
    (isOpenEmbedding_structureMap (R := X) (A := fun i ↦ (U i : Set (X i))) hUopen).continuous
  have harc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) :=
    (Circle.isOpen_centeredArc _).mem_nhds (by
      rw [Circle.mem_centeredArc (by nlinarith [Real.pi_pos])]
      simp
      positivity)
  have hpre : f ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : ∀ i, U i) :=
    hf.continuousAt (by
      rw [map_one]
      exact harc)
  rw [nhds_pi, Filter.mem_pi'] at hpre
  rcases hpre with ⟨s, t, ht, hst⟩
  refine ⟨s, Subgroup.le_ker_of_mapsTo_centeredArc (productTail U s) f ?_⟩
  intro u hu
  apply hst
  intro i hi
  have hui : u i = 1 := (mem_productTail (U := U)).mp hu i hi
  rw [hui]
  exact mem_of_mem_nhds (ht i)

/-- Every identity neighborhood in a cofinite restricted product with open distinguished
subgroups contains an embedded product tail. -/
theorem exists_restrictedProductTail_subset_of_mem_nhds
    (hUopen : ∀ i, IsOpen (U i : Set (X i)))
    {N : Set (Πʳ i, [X i, U i])} (hN : N ∈ nhds (1 : Πʳ i, [X i, U i])) :
    ∃ s : Finset ι, (restrictedProductTail U s : Set (Πʳ i, [X i, U i])) ⊆ N := by
  classical
  have hpre : (structureMapMonoidHom U) ⁻¹' N ∈ nhds (1 : ∀ i, U i) := by
    have hone : (1 : Πʳ i, [X i, U i]) =
        structureMap X (fun i ↦ (U i : Set (X i))) cofinite (1 : ∀ i, U i) := rfl
    rw [hone, nhds_eq_map_structureMap
      (R := X) (A := fun i ↦ (U i : Set (X i))) hUopen] at hN
    exact hN
  rw [nhds_pi, Filter.mem_pi'] at hpre
  rcases hpre with ⟨s, t, ht, hst⟩
  refine ⟨s, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  apply hst
  intro i hi
  rw [(mem_productTail (U := U)).mp hu i hi]
  exact mem_of_mem_nhds (ht i)

/-- A compact-open test set: the whole distinguished product together with the full
single-coordinate copies indexed by `s`. -/
def characterTestSet (s : Finset ι) : Set (Πʳ i, [X i, U i]) :=
  by
    classical
    exact Set.range (structureMapMonoidHom U) ∪
      ⋃ i ∈ s, Set.range (mulSingle U i)

/-- For finite discrete coordinates, `characterTestSet` is compact. -/
theorem isCompact_characterTestSet
    [∀ i, Finite (X i)] [∀ i, DiscreteTopology (X i)]
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (s : Finset ι) :
    IsCompact (characterTestSet U s) := by
  classical
  apply IsCompact.union
  · exact isCompact_range
      (isOpenEmbedding_structureMap (R := X) (A := fun i ↦ (U i : Set (X i)))
        hUopen).continuous
  · exact s.isCompact_biUnion fun i _ ↦
      isCompact_range (continuous_of_discreteTopology : Continuous (mulSingle U i))

/-- The local coordinate character obtained by restricting a global character to a
single-coordinate copy. -/
@[expose] noncomputable def coordinateCharacter
    (χ : PontryaginDual (Πʳ i, [X i, U i])) (i : ι) : X i →* Circle := by
  classical
  exact χ.toMonoidHom.comp (mulSingleMonoidHom U i)

open scoped Classical in
@[simp]
theorem coordinateCharacter_apply (χ : PontryaginDual (Πʳ i, [X i, U i]))
    (i : ι) (x : X i) : coordinateCharacter U χ i x = χ (mulSingle U i x) :=
  rfl

/-- The coordinate recovered from a global character through an explicitly bijective local
character map. -/
noncomputable def reconstructedCoordinate
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (χ : PontryaginDual (Πʳ i, [X i, U i])) (i : ι) : Y i :=
  (MulEquiv.ofBijective (rightCharacter (e i)) (hperfect i)).symm (coordinateCharacter U χ i)

open scoped Classical in
@[simp]
theorem reconstructedCoordinate_spec
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (χ : PontryaginDual (Πʳ i, [X i, U i])) (i : ι) (x : X i) :
    e i x (reconstructedCoordinate U e hperfect χ i) = χ (mulSingle U i x) := by
  change rightCharacter (e i) (reconstructedCoordinate U e hperfect χ i) x = _
  rw [reconstructedCoordinate, MulEquiv.ofBijective_apply_symm_apply]
  rfl

omit [∀ i, TopologicalSpace (X i)] in
open scoped Classical in
@[simp]
theorem finset_prod_mulSingle_apply (s : Finset ι) (x : ∀ i, X i) (i : ι) :
    (∏ j ∈ s, mulSingle U j (x j)) i = if i ∈ s then x i else 1 := by
  change evalMonoidHom X i (∏ j ∈ s, mulSingle U j (x j)) = _
  rw [map_prod]
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    calc
      ∏ j ∈ s, evalMonoidHom X i (mulSingle U j (x j)) =
          evalMonoidHom X i (mulSingle U i (x i)) :=
        Finset.prod_eq_single_of_mem i hi fun j _ hji ↦ by
          simp [mulSingle_eq_of_ne U (x j) hji.symm]
      _ = x i := by simp
  · simp only [hi, ↓reduceIte]
    apply Finset.prod_eq_one
    intro j hj
    have hji : i ≠ j := fun hij ↦ hi (hij ▸ hj)
    simp [mulSingle_eq_of_ne U (x j) hji]

variable [∀ i, TopologicalSpace (Y i)]

/-- Exact local perfectness and exact right-annihilator subgroups make the canonical map from the
second restricted product onto the Pontryagin dual of the first restricted product.

This proof works for arbitrary index types.  Local perfectness is the actual bijectivity of the
map `Y i →* (X i →* Circle)` defined by the bicharacter; no nondegeneracy or cardinality shortcut
is used. -/
theorem toPontryaginDual_surjective
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (hV : ∀ i, V i = rightAnnihilator (U i) (e i)) :
    Function.Surjective (toPontryaginDual U V e horth hUopen hVopen he) := by
  classical
  intro χ
  obtain ⟨s, hs⟩ := exists_productTail_le_ker U hUopen χ
  have hy_mem : ∀ i, i ∉ s → reconstructedCoordinate U e hperfect χ i ∈ V i := by
    intro i hi
    rw [hV i, mem_rightAnnihilator]
    intro x hx
    rw [reconstructedCoordinate_spec]
    have hsingle : Pi.mulSingle i (⟨x, hx⟩ : U i) ∈ productTail U s := by
      rw [mem_productTail]
      intro j hj
      have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
      simp [Pi.mulSingle, hji]
    have hker := hs hsingle
    rw [MonoidHom.mem_ker] at hker
    change χ.toMonoidHom (mulSingle U i x) = 1
    simpa [structureMapMonoidHom_pi_mulSingle] using hker
  let y : Πʳ i, [Y i, V i] :=
    ⟨fun i ↦ reconstructedCoordinate U e hperfect χ i,
      Filter.eventually_cofinite.mpr <| s.finite_toSet.subset fun i hi ↦ by
        by_contra his
        exact hi (hy_mem i his)⟩
  refine ⟨y, ?_⟩
  apply PontryaginDual.ext
  intro x
  let t : Finset ι := s ∪ exceptionalFinset x
  let z : Πʳ i, [X i, U i] := ∏ i ∈ t, mulSingle U i (x i)
  let u : ∀ i, U i := fun i ↦ if hi : i ∈ t then 1 else
    ⟨x i, mem_cofiniteStage_exceptionalFinset x i fun hit ↦ hi (Finset.mem_union_right s hit)⟩
  have hu_tail : u ∈ productTail U s := by
    rw [mem_productTail]
    intro i hi
    simp [u, t, hi]
  have hdecomp : z * structureMapMonoidHom U u = x := by
    ext i
    by_cases hi : i ∈ t
    · simp [z, u, hi, finset_prod_mulSingle_apply]
    · simp [z, u, hi, finset_prod_mulSingle_apply]
  have hz : toPontryaginDual U V e horth hUopen hVopen he y z = χ z := by
    simp only [z, map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    change pairing U V e (mulSingle U i (x i)) y = χ (mulSingle U i (x i))
    rw [pairing_mulSingle_left]
    change e i (x i) (reconstructedCoordinate U e hperfect χ i) = _
    exact reconstructedCoordinate_spec U e hperfect χ i (x i)
  have hχu : χ (structureMapMonoidHom U u) = 1 := by
    exact hs hu_tail
  have hpairu :
      toPontryaginDual U V e horth hUopen hVopen he y (structureMapMonoidHom U u) = 1 := by
    rw [toPontryaginDual_apply, pairing_eq_prod (s := t)]
    · apply Finset.prod_eq_one
      intro i hi
      simp [u, hi]
    · intro i hi
      have hxi : x i ∈ U i := mem_cofiniteStage_exceptionalFinset x i fun hit ↦
        hi (Finset.mem_union_right s hit)
      have hyi : y i ∈ V i := hy_mem i fun his ↦ hi (Finset.mem_union_left _ his)
      simpa [u, hi] using horth i (x i) hxi (y i) hyi
  rw [← hdecomp, map_mul, map_mul, hz, hpairu, hχu]

/-- Under explicit local perfectness and exact right-annihilator hypotheses, the canonical map is
bijective. -/
theorem toPontryaginDual_bijective
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (hV : ∀ i, V i = rightAnnihilator (U i) (e i)) :
    Function.Bijective (toPontryaginDual U V e horth hUopen hVopen he) := by
  refine ⟨toPontryaginDual_injective U V e horth hUopen hVopen he ?_,
    toPontryaginDual_surjective U V e horth hUopen hVopen he hperfect hV⟩
  intro i y y' hyy'
  apply (hperfect i).injective
  exact MonoidHom.ext hyy'

/-- The algebraic equivalence underlying restricted-product character reconstruction. -/
@[expose] noncomputable def toPontryaginDualMulEquiv
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (hV : ∀ i, V i = rightAnnihilator (U i) (e i)) :
    (Πʳ i, [Y i, V i]) ≃* PontryaginDual (Πʳ i, [X i, U i]) :=
  MulEquiv.ofBijective (toPontryaginDual U V e horth hUopen hVopen he).toMonoidHom
    (toPontryaginDual_bijective U V e horth hUopen hVopen he hperfect hV)

@[simp]
theorem toPontryaginDualMulEquiv_apply
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (hV : ∀ i, V i = rightAnnihilator (U i) (e i)) (y : Πʳ i, [Y i, V i]) :
    toPontryaginDualMulEquiv U V e horth hUopen hVopen he hperfect hV y =
      toPontryaginDual U V e horth hUopen hVopen he y :=
  rfl

/-- For finite discrete coordinates on the character's domain, the inverse algebraic
reconstruction map is continuous.  The proof uses explicit compact-open test sets and product
tails; it does not use an open-mapping theorem. -/
theorem continuous_toPontryaginDualMulEquiv_symm
    [∀ i, Finite (X i)] [∀ i, DiscreteTopology (X i)] [∀ i, IsTopologicalGroup (Y i)]
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (hV : ∀ i, V i = rightAnnihilator (U i) (e i)) :
    Continuous (toPontryaginDualMulEquiv U V e horth hUopen hVopen he hperfect hV).symm := by
  classical
  let _ : Fact (∀ i, IsOpen (V i : Set (Y i))) := ⟨hVopen⟩
  apply continuous_of_tendsto_nhds_one
  rw [Filter.tendsto_def]
  intro N hN
  obtain ⟨s, hsN⟩ := exists_restrictedProductTail_subset_of_mem_nhds V hVopen hN
  let Ω : Set (PontryaginDual (Πʳ i, [X i, U i])) :=
    {χ | MapsTo χ (characterTestSet U s) (Circle.centeredArc (Real.pi / 2))}
  have hΩopen : IsOpen Ω := by
    exact isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo
      (isCompact_characterTestSet U hUopen s) (Circle.isOpen_centeredArc _))
  have h1Ω : (1 : PontryaginDual (Πʳ i, [X i, U i])) ∈ Ω := by
    intro x hx
    rw [Circle.mem_centeredArc (by nlinarith [Real.pi_pos])]
    simp
    positivity
  apply Filter.mem_of_superset (hΩopen.mem_nhds h1Ω)
  intro χ hχ
  let y : Πʳ i, [Y i, V i] :=
    (toPontryaginDualMulEquiv U V e horth hUopen hVopen he hperfect hV).symm χ
  have hfy : toPontryaginDual U V e horth hUopen hVopen he y = χ :=
    (toPontryaginDualMulEquiv U V e horth hUopen hVopen he hperfect hV).apply_symm_apply χ
  have hχU : ∀ u : ∀ i, U i, χ (structureMapMonoidHom U u) = 1 := by
    let g : (∀ i, U i) →* Circle := χ.toMonoidHom.comp (structureMapMonoidHom U)
    have hg : (⊤ : Subgroup (∀ i, U i)) ≤ g.ker :=
      Subgroup.le_ker_of_mapsTo_centeredArc ⊤ g fun u _ ↦ hχ (by
        exact Or.inl ⟨u, rfl⟩)
    intro u
    exact hg (by simp)
  have hχi : ∀ i ∈ s, ∀ x : X i, χ (mulSingle U i x) = 1 := by
    intro i hi
    let g : X i →* Circle := χ.toMonoidHom.comp (mulSingleMonoidHom U i)
    have hg : (⊤ : Subgroup (X i)) ≤ g.ker :=
      Subgroup.le_ker_of_mapsTo_centeredArc ⊤ g fun x _ ↦ hχ (by
        exact Or.inr (Set.mem_iUnion_of_mem i <|
          Set.mem_iUnion_of_mem hi ⟨x, rfl⟩))
    intro x
    exact hg (by simp)
  have hyV : ∀ i, y i ∈ V i := by
    intro i
    rw [hV i, mem_rightAnnihilator]
    intro x hx
    calc
      e i x (y i) = toPontryaginDual U V e horth hUopen hVopen he y
          (mulSingle U i x) := by
            rw [toPontryaginDual_apply, pairing_mulSingle_left]
      _ = χ (mulSingle U i x) := by rw [hfy]
      _ = χ (structureMapMonoidHom U (Pi.mulSingle i ⟨x, hx⟩)) := by
        rw [structureMapMonoidHom_pi_mulSingle]
      _ = 1 := hχU _
  have hyone : ∀ i ∈ s, y i = 1 := by
    intro i hi
    apply (hperfect i).injective
    apply MonoidHom.ext
    intro x
    calc
      rightCharacter (e i) (y i) x =
          toPontryaginDual U V e horth hUopen hVopen he y (mulSingle U i x) := by
            rw [rightCharacter_apply, toPontryaginDual_apply, pairing_mulSingle_left]
      _ = χ (mulSingle U i x) := by rw [hfy]
      _ = 1 := hχi i hi x
      _ = rightCharacter (e i) 1 x := by simp
  let v : ∀ i, V i := fun i ↦ ⟨y i, hyV i⟩
  have hv : v ∈ productTail V s := by
    rw [mem_productTail]
    intro i hi
    exact Subtype.ext (hyone i hi)
  apply hsN
  refine ⟨v, hv, ?_⟩
  apply RestrictedProduct.ext
  intro i
  rfl

/-- Finite discrete character-domain groups and topological representing groups, with explicit
local perfectness and exact annihilators, yield a topological multiplicative equivalence with the
compact-open Pontryagin dual. -/
@[expose] noncomputable def pontryaginDualEquiv
    [∀ i, Finite (X i)] [∀ i, DiscreteTopology (X i)] [∀ i, IsTopologicalGroup (Y i)]
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (hV : ∀ i, V i = rightAnnihilator (U i) (e i)) :
    (Πʳ i, [Y i, V i]) ≃ₜ* PontryaginDual (Πʳ i, [X i, U i]) :=
  ContinuousMulEquiv.mk
    (toPontryaginDualMulEquiv U V e horth hUopen hVopen he hperfect hV)
    (toPontryaginDual U V e horth hUopen hVopen he).continuous
    (continuous_toPontryaginDualMulEquiv_symm U V e horth hUopen hVopen he hperfect hV)

@[simp]
theorem pontryaginDualEquiv_apply
    [∀ i, Finite (X i)] [∀ i, DiscreteTopology (X i)] [∀ i, IsTopologicalGroup (Y i)]
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (hV : ∀ i, V i = rightAnnihilator (U i) (e i)) (y : Πʳ i, [Y i, V i]) :
    pontryaginDualEquiv U V e horth hUopen hVopen he hperfect hV y =
      toPontryaginDual U V e horth hUopen hVopen he y :=
  rfl

end RestrictedProduct
