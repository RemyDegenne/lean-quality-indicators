/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import SimplicialObjects.FiniteFiberTransfer

/-!
# Normalized maps for arbitrary morphisms of split simplicial objects

The normalized complex, projection and section are mathlib's existing
`SimplicialObject.Splitting.nondegComplex`, `toNondegComplex` and
`fromNondegComplex`. The construction here allows every morphism between the
underlying simplicial objects, without requiring it to preserve the chosen
nondegenerate summands.

A supplied splitting contains the coproduct data; the construction needs only
preadditivity. The projection equation characterizes descent, and its degreewise
quotient property is expressed by vanishing on elementary degeneracies.
The section is also natural, so normalization preserves degreewise monomorphisms.
For simplicial sets this applies with any coefficient object, using monicity of
coproduct maps induced by injective maps of simplices.

For additive coefficient functors preserving coproducts indexed in the simplex
universe, the normalized coefficient comparison is coherent with arbitrary
coefficient-valued simplicial morphisms, finite-fiber equifibered transfer, and
natural transformations of coefficient functors. These coherence laws follow from
the splitting retract and Mathlib's all-simplex coproduct comparison; they are not
additional exactness or homology-preservation assertions.

## References

Mathlib's Dold–Kan projector and splitting constructions, notably
`Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject`, supply the normalized
objects and strict retract identities. The map generalizes the simplicial-set
normalized-map construction to coefficient-valued simplicial morphisms. May,
*A Concise Course in Algebraic Topology*, revised edition, §16.1 motivates the
degeneracy-quotient characterization. The quasi-isomorphism result on normalized
chains is a categorical analogue of May's chain-homotopy invariance argument in
§§12.2 and 13.3, using Mathlib's simplicial homotopy constructions by Fabian
Odermatt and Joël Riou.
-/

@[expose] public section

universe v v' u u' w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X Y Z : SimplicialObject C} (s : Splitting X) (t : Splitting Y) (r : Splitting Z)

/-- The normalized chain map induced by any underlying simplicial morphism.
The section, alternating-face map, and projection are the three stock chain maps. -/
noncomputable def nondegComplexMap (f : X ⟶ Y) : s.nondegComplex ⟶ t.nondegComplex :=
  s.fromNondegComplex ≫ (alternatingFaceMapComplex C).map f ≫ t.toNondegComplex

/-- Degreewise formula for the constructed normalized map. -/
@[reassoc]
theorem nondegComplexMap_f (f : X ⟶ Y) (n : ℕ) :
    (s.nondegComplexMap t f).f n = s.fromNondegComplex.f n ≫
      f.app (op ⦋n⦌) ≫ t.toNondegComplex.f n := rfl

/-- The quotient projection is natural for every underlying simplicial morphism. -/
@[reassoc]
theorem toNondegComplex_nondegComplexMap (f : X ⟶ Y) :
    s.toNondegComplex ≫ s.nondegComplexMap t f =
      (alternatingFaceMapComplex C).map f ≫ t.toNondegComplex := by
  have h : (alternatingFaceMapComplex C).map f ≫ DoldKan.PInfty =
      DoldKan.PInfty ≫ (alternatingFaceMapComplex C).map f :=
    (DoldKan.natTransPInfty C).naturality f
  unfold nondegComplexMap
  rw [← Category.assoc, s.toNondegComplex_fromNondegComplex, ← Category.assoc,
    ← h, Category.assoc, t.PInfty_toNondegComplex]

/-- The section is natural for every underlying simplicial morphism. -/
@[reassoc]
theorem nondegComplexMap_fromNondegComplex (f : X ⟶ Y) :
    s.nondegComplexMap t f ≫ t.fromNondegComplex =
      s.fromNondegComplex ≫ (alternatingFaceMapComplex C).map f := by
  apply (cancel_epi s.toNondegComplex).mp
  rw [← Category.assoc, s.toNondegComplex_nondegComplexMap t f,
    Category.assoc, t.toNondegComplex_fromNondegComplex,
    ← Category.assoc, s.toNondegComplex_fromNondegComplex]
  exact (DoldKan.natTransPInfty C).naturality f

/-- Normalization preserves monicity in each degree. -/
theorem mono_nondegComplexMap_f (f : X ⟶ Y) (n : ℕ)
    [Mono (f.app (op ⦋n⦌))] : Mono ((s.nondegComplexMap t f).f n) := by
  have h : (s.nondegComplexMap t f).f n ≫ t.fromNondegComplex.f n =
      s.fromNondegComplex.f n ≫ f.app (op ⦋n⦌) :=
    HomologicalComplex.congr_hom (s.nondegComplexMap_fromNondegComplex t f) n
  have : Mono (s.fromNondegComplex.f n ≫ f.app (op ⦋n⦌)) := mono_comp _ _
  exact mono_of_mono_fac h

/-- The projection equation characterizes the constructed map uniquely. -/
theorem nondegComplexMap_eq_iff (f : X ⟶ Y) (g : s.nondegComplex ⟶ t.nondegComplex) :
    g = s.nondegComplexMap t f ↔
      s.toNondegComplex ≫ g = (alternatingFaceMapComplex C).map f ≫ t.toNondegComplex := by
  constructor
  · rintro rfl
    exact s.toNondegComplex_nondegComplexMap t f
  · intro h
    apply (cancel_epi s.toNondegComplex).1
    exact h.trans (s.toNondegComplex_nondegComplexMap t f).symm

/-- Normalization preserves the identity underlying simplicial morphism. -/
theorem nondegComplexMap_id : s.nondegComplexMap s (𝟙 X) = 𝟙 _ := by
  symm
  apply (s.nondegComplexMap_eq_iff s (𝟙 X) (𝟙 _)).2
  simp only [Functor.map_id, Category.comp_id, Category.id_comp]

/-- Normalization preserves composition, without compatibility of the splittings. -/
theorem nondegComplexMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    s.nondegComplexMap r (f ≫ g) = s.nondegComplexMap t f ≫ t.nondegComplexMap r g := by
  symm
  apply (s.nondegComplexMap_eq_iff r (f ≫ g)
    (s.nondegComplexMap t f ≫ t.nondegComplexMap r g)).2
  rw [← Category.assoc, s.toNondegComplex_nondegComplexMap t f, Category.assoc,
    t.toNondegComplex_nondegComplexMap r g, Functor.map_comp, Category.assoc]

/-- In every degree, the stock projection is the quotient by elementary degeneracies.
In degree zero the degeneracy condition is vacuous. -/
theorem degeneraciesVanish_iff_existsUnique (n : ℕ) {T : C} (a : X _⦋n⦌ ⟶ T) :
    DoldKan.DegeneraciesVanish a ↔
      ∃! b : s.N n ⟶ T, s.toNondegComplex.f n ≫ b = a := by
  change DoldKan.DegeneraciesVanish a ↔
    ∃! b : s.nondegComplex.X n ⟶ T, s.toNondegComplex.f n ≫ b = a
  constructor
  · intro ha
    have hQ := (DoldKan.degeneraciesVanish_iff_QInfty_f_comp a).mp ha
    have hP : (DoldKan.PInfty (X := X)).f n ≫ a = a := by
      have h := DoldKan.PInfty_f_add_QInfty_f (X := X) n =≫ a
      simpa only [Preadditive.add_comp, hQ, add_zero, Category.id_comp] using h
    have hqj : s.toNondegComplex.f n ≫ s.fromNondegComplex.f n =
        (DoldKan.PInfty (X := X)).f n := by
      simpa only [HomologicalComplex.comp_f] using
        HomologicalComplex.congr_hom s.toNondegComplex_fromNondegComplex n
    have hjq : s.fromNondegComplex.f n ≫ s.toNondegComplex.f n =
        𝟙 (s.nondegComplex.X n) := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
        HomologicalComplex.congr_hom s.fromNondegComplex_toNondegComplex n
    refine ⟨s.fromNondegComplex.f n ≫ a, ?_, ?_⟩
    · change s.toNondegComplex.f n ≫ (s.fromNondegComplex.f n ≫ a) = a
      rw [← Category.assoc, hqj]
      exact hP
    · intro b hb
      calc
        b = (s.fromNondegComplex.f n ≫ s.toNondegComplex.f n) ≫ b := by
          rw [hjq, Category.id_comp]
        _ = s.fromNondegComplex.f n ≫ a := by rw [Category.assoc, hb]
  · rintro ⟨b, hb, _⟩
    have hq : DoldKan.DegeneraciesVanish (s.toNondegComplex.f n) := by
      rw [s.toNondegComplex_f]
      exact (DoldKan.degeneraciesVanishPInfty_f X n).comp _
    rw [← hb]
    exact hq.comp b

/-- The universal factor of a map vanishing on degeneracies is given by the stock section. -/
@[reassoc]
theorem toNondegComplex_f_factor (n : ℕ) {T : C} (a : X _⦋n⦌ ⟶ T)
    (ha : DoldKan.DegeneraciesVanish a) :
    s.toNondegComplex.f n ≫ s.fromNondegComplex.f n ≫ a = a := by
  have hQ := (DoldKan.degeneraciesVanish_iff_QInfty_f_comp a).mp ha
  have hP := DoldKan.PInfty_f_add_QInfty_f (X := X) n =≫ a
  have hqj : s.toNondegComplex.f n ≫ s.fromNondegComplex.f n =
      (DoldKan.PInfty (X := X)).f n := by
    simpa only [HomologicalComplex.comp_f] using
      HomologicalComplex.congr_hom s.toNondegComplex_fromNondegComplex n
  rw [← Category.assoc, hqj]
  simpa only [Preadditive.add_comp, hQ, add_zero, Category.id_comp] using hP

end CategoryTheory.SimplicialObject.Splitting

namespace CategoryTheory.SimplicialObject.Split

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂)

/-- For a morphism compatible with the splittings, the normalized map agrees with
mathlib's functor on split simplicial objects. -/
theorem nondegComplexMap_eq_nondegComplexFunctor_map :
    S₁.s.nondegComplexMap S₂.s Φ.F = nondegComplexFunctor.map Φ := by
  symm
  apply (S₁.s.nondegComplexMap_eq_iff S₂.s Φ.F _).2
  ext n
  change S₁.s.toNondegComplex.f n ≫ Φ.f n =
    Φ.F.app (op ⦋n⦌) ≫ S₂.s.toNondegComplex.f n
  rw [S₁.s.toNondegComplex_f, S₂.s.toNondegComplex_f]
  change (DoldKan.PInfty.f n ≫
      S₁.s.πSummand (Splitting.IndexSet.id (op ⦋n⦌))) ≫ Φ.f n =
    Φ.F.app (op ⦋n⦌) ≫ DoldKan.PInfty.f n ≫
      S₂.s.πSummand (Splitting.IndexSet.id (op ⦋n⦌))
  rw [S₁.s.PInfty_comp_πSummand_id, S₂.s.PInfty_comp_πSummand_id]
  apply S₁.s.hom_ext'
  intro A
  erw [cofan_inj_naturality_symm_assoc Φ A]
  by_cases h : A.EqId
  · dsimp at h
    subst h
    change (S₁.s.cofan (op ⦋n⦌)).inj (Splitting.IndexSet.id (op ⦋n⦌)) ≫
        S₁.s.πSummand (Splitting.IndexSet.id (op ⦋n⦌)) ≫ Φ.f n =
      Φ.f n ≫ (S₂.s.cofan (op ⦋n⦌)).inj (Splitting.IndexSet.id (op ⦋n⦌)) ≫
        S₂.s.πSummand (Splitting.IndexSet.id (op ⦋n⦌))
    erw [S₁.s.cofan_inj_πSummand_eq_id_assoc, S₂.s.cofan_inj_πSummand_eq_id]
    erw [Category.comp_id]
  · erw [S₁.s.cofan_inj_πSummand_eq_zero_assoc _ _ (Ne.symm h),
      S₂.s.cofan_inj_πSummand_eq_zero _ _ (Ne.symm h), zero_comp, comp_zero]

end

end CategoryTheory.SimplicialObject.Split

namespace SSet

/-- A simplicial map with a two-sided combinatorial homotopy inverse induces a
quasi-isomorphism on normalized chains with coefficients in any object of a
preadditive category with the required coproducts and homology. This categorical
normalized-chain statement is an analogue of the chain-homotopy invariance
argument in May, *A Concise Course in Algebraic Topology*, revised edition,
§§12.2 and 13.3. -/
theorem quasiIso_normalizedChainComplexMap_of_homotopy_inverse
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    [CategoryWithHomology C]
    {S T : SSet.{w}} (f : S ⟶ T) (g : T ⟶ S)
    (Hfg : CategoryTheory.SimplicialObject.Homotopy (f ≫ g) (𝟙 S))
    (Hgf : CategoryTheory.SimplicialObject.Homotopy (g ≫ f) (𝟙 T))
    (R : C) : QuasiIso (normalizedChainComplexMap f R) := by
  -- The stock simplicial homotopies first give an equivalence on all-simplex chains.
  let e : HomotopyEquiv (S.chainComplex R) (T.chainComplex R) :=
    { hom := chainComplexMap f R
      inv := chainComplexMap g R
      homotopyHomInvId := by
        rw [← ((chainComplexFunctor C).obj R).map_comp f g,
          ← ((chainComplexFunctor C).obj R).map_id S]
        exact Hfg.sSetChainComplexMap R
      homotopyInvHomId := by
        rw [← ((chainComplexFunctor C).obj R).map_comp g f,
          ← ((chainComplexFunctor C).obj R).map_id T]
        exact Hgf.sSetChainComplexMap R }
  have : QuasiIso (chainComplexMap f R) := e.quasiIso_hom
  -- The normalization section and projection are already quasi-isomorphisms.
  unfold normalizedChainComplexMap
  infer_instance

/-- An extra degeneracy makes the augmentation a quasi-isomorphism on normalized
chains with coefficients in any object of a preadditive category with the required
coproducts and homology. The target is the constant simplicial set on the arbitrary
augmentation object `U.right`. This applies the homotopy-inverse theorem using
Mathlib's extra-degeneracy section and combinatorial homotopy. -/
theorem quasiIso_normalizedChainComplexMap_of_extraDegeneracy
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    [CategoryWithHomology C] (U : SSet.Augmented.{w})
    (ed : CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy U)
    (R : C) : QuasiIso (normalizedChainComplexMap U.hom R) := by
  exact quasiIso_normalizedChainComplexMap_of_homotopy_inverse U.hom ed.section_ ed.homotopy
    (Eq.mp
      (congrArg (fun k : (SimplicialObject.const (Type w)).obj U.right ⟶
          (SimplicialObject.const (Type w)).obj U.right ↦
        SimplicialObject.Homotopy k (𝟙 _)) ed.section_comp_hom.symm)
      (SimplicialObject.Homotopy.refl (𝟙 _))) R

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  {X Y : SSet.{w}} (f : X ⟶ Y) (R : C)

/-- The generic normalized map agrees with mathlib's existing map for simplicial sets.
The map `f` need not preserve nondegenerate simplices. -/
theorem nondegComplexMap_eq_normalizedChainComplexMap :
    (X.splitting.map (sigmaConst.obj R)).nondegComplexMap
        (Y.splitting.map (sigmaConst.obj R)) (Functor.whiskerRight f (sigmaConst.obj R)) =
      normalizedChainComplexMap f R := by
  symm
  apply ((X.splitting.map (sigmaConst.obj R)).nondegComplexMap_eq_iff
    (Y.splitting.map (sigmaConst.obj R))
    (Functor.whiskerRight f (sigmaConst.obj R)) _).2
  exact toNormalizedChainComplex_normalizedChainComplexMap f R

/-- A simplicial monomorphism induces monomorphisms on normalized chains in every
degree, for any coefficient object in a preadditive category with coproducts. -/
theorem mono_normalizedChainComplexMap_f [Mono f] (n : ℕ) :
    Mono ((normalizedChainComplexMap f R).f n) := by
  have : Mono ((Functor.whiskerRight f (sigmaConst.obj R)).app (op ⦋n⦌)) :=
    inferInstanceAs (Mono ((sigmaConst.obj R).map (f.app (op ⦋n⦌))))
  rw [← nondegComplexMap_eq_normalizedChainComplexMap f R]
  exact (X.splitting.map (sigmaConst.obj R)).mono_nondegComplexMap_f
      (Y.splitting.map (sigmaConst.obj R)) (Functor.whiskerRight f (sigmaConst.obj R)) n

/-- Changing the coefficient of a normalized simplex is coefficientwise, including
for a degenerate simplex whose normalized class is zero. -/
@[reassoc]
theorem ιNormalizedChainComplex_nondegComplexMap_coefficient
    (S : SSet.{w}) {R' : C} (a : R ⟶ R') {n : ℕ} (x : S _⦋n⦌) :
    S.ιNormalizedChainComplex x ≫
        ((S.splitting.map (sigmaConst.obj R)).nondegComplexMap
          (S.splitting.map (sigmaConst.obj R'))
          (Functor.whiskerLeft S (sigmaConst.map a))).f n =
      a ≫ S.ιNormalizedChainComplex x := by
  let N : S.normalizedChainComplex R ⟶ S.normalizedChainComplex R' :=
    (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
      (S.splitting.map (sigmaConst.obj R')) (Functor.whiskerLeft S (sigmaConst.map a))
  have hq : (S.toNormalizedChainComplex R).f n ≫ N.f n =
      (sigmaConst.map a).app (S.obj (op ⦋n⦌)) ≫
        (S.toNormalizedChainComplex R').f n :=
    HomologicalComplex.congr_hom
      ((S.splitting.map (sigmaConst.obj R)).toNondegComplex_nondegComplexMap
        (S.splitting.map (sigmaConst.obj R'))
        (Functor.whiskerLeft S (sigmaConst.map a))) n
  have hι : S.ιChainComplex (R := R) x ≫ (S.toNormalizedChainComplex R).f n =
      S.ιNormalizedChainComplex (R := R) x :=
    S.ιChainComplex_toNormalizedChainComplex_f x
  have ha : S.ιChainComplex (R := R) x ≫
      (sigmaConst.map a).app (S.obj (op ⦋n⦌)) =
        a ≫ S.ιChainComplex (R := R') x :=
    Sigma.ι_map (fun _ : S _⦋n⦌ ↦ a) x
  calc
    S.ιNormalizedChainComplex (R := R) x ≫ N.f n =
        (S.ιChainComplex (R := R) x ≫ (S.toNormalizedChainComplex R).f n) ≫ N.f n :=
      congrArg (fun k : R ⟶ (S.normalizedChainComplex R).X n ↦ k ≫ N.f n) hι.symm
    _ = S.ιChainComplex (R := R) x ≫ ((S.toNormalizedChainComplex R).f n ≫ N.f n) :=
      Category.assoc _ _ _
    _ = S.ιChainComplex (R := R) x ≫
        ((sigmaConst.map a).app (S.obj (op ⦋n⦌)) ≫
          (S.toNormalizedChainComplex R').f n) :=
      congrArg (fun k : (S.chainComplex R).X n ⟶ (S.normalizedChainComplex R').X n ↦
        S.ιChainComplex (R := R) x ≫ k) hq
    _ = (S.ιChainComplex (R := R) x ≫
        (sigmaConst.map a).app (S.obj (op ⦋n⦌))) ≫
          (S.toNormalizedChainComplex R').f n := (Category.assoc _ _ _).symm
    _ = (a ≫ S.ιChainComplex (R := R') x) ≫ (S.toNormalizedChainComplex R').f n :=
      congrArg (fun k : R ⟶ (S.chainComplex R').X n ↦
        k ≫ (S.toNormalizedChainComplex R').f n) ha
    _ = a ≫ (S.ιChainComplex (R := R') x ≫ (S.toNormalizedChainComplex R').f n) :=
      Category.assoc _ _ _
    _ = a ≫ S.ιNormalizedChainComplex (R := R') x :=
      congrArg (fun k : R' ⟶ (S.normalizedChainComplex R').X n ↦ a ≫ k)
        (S.ιChainComplex_toNormalizedChainComplex_f (R := R') x)

section CoefficientComparison

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]
  (L : C ⥤ D) [L.Additive]
  [∀ (T : Type w), PreservesColimitsOfShape (Discrete T) L]

@[reassoc]
private lemma map_PInfty_chainComplexFunctorObjCompMapIso_hom_app (S : SSet.{w}) :
    (L.mapHomologicalComplex (.down ℕ)).map
        (DoldKan.PInfty (X := S ⋙ sigmaConst.obj R)) ≫
        (chainComplexFunctorObjCompMapIso L R).hom.app S =
      (chainComplexFunctorObjCompMapIso L R).hom.app S ≫ DoldKan.PInfty := by
  ext n
  have h := DoldKan.PInfty_f_naturality n
    (X := ((SimplicialObject.whiskering C D).obj L).obj (S ⋙ sigmaConst.obj R))
    (Functor.whiskerLeft S (sigmaConstObjCompIso L R).hom)
  rw [DoldKan.map_PInfty_f L (S ⋙ sigmaConst.obj R) n] at h
  simpa [chainComplexFunctorObjCompMapIso] using h.symm

/-- Normalized chains commute with an additive functor preserving the indexed coproducts.
The components use the normalization section and projection and the all-simplex
coefficient comparison. -/
noncomputable def normalizedChainComplexFunctorObjCompMapIso :
    normalizedChainComplexFunctorObj R ⋙ L.mapHomologicalComplex (.down ℕ) ≅
      normalizedChainComplexFunctorObj (L.obj R) :=
  NatIso.ofComponents (fun S ↦
    { hom := (L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
        (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
          S.toNormalizedChainComplex (L.obj R)
      inv := S.fromNormalizedChainComplex (L.obj R) ≫
        (chainComplexFunctorObjCompMapIso L R).inv.app S ≫
          (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R)
      hom_inv_id := by
        change ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
            (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
              S.toNormalizedChainComplex (L.obj R)) ≫
            (S.fromNormalizedChainComplex (L.obj R) ≫
              (chainComplexFunctorObjCompMapIso L R).inv.app S ≫
                (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R)) =
          𝟙 ((L.mapHomologicalComplex (.down ℕ)).obj (S.normalizedChainComplex R))
        simp only [Category.assoc, toNormalizedChainComplex_fromNormalizedChainComplex_assoc]
        rw [← map_PInfty_chainComplexFunctorObjCompMapIso_hom_app_assoc R L S]
        simp only [Iso.hom_inv_id_app_assoc]
        rw [← S.toNormalizedChainComplex_fromNormalizedChainComplex R]
        simp [← Functor.map_comp]
      inv_hom_id := by
        change (S.fromNormalizedChainComplex (L.obj R) ≫
            (chainComplexFunctorObjCompMapIso L R).inv.app S ≫
              (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R)) ≫
            ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
              (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
                S.toNormalizedChainComplex (L.obj R)) =
          𝟙 (S.normalizedChainComplex (L.obj R))
        simp only [Category.assoc]
        rw [← (L.mapHomologicalComplex (.down ℕ)).map_comp_assoc
          (S.toNormalizedChainComplex R) (S.fromNormalizedChainComplex R),
          toNormalizedChainComplex_fromNormalizedChainComplex,
          map_PInfty_chainComplexFunctorObjCompMapIso_hom_app_assoc R L S]
        simp })
    (by
      intro S T g
      change (L.mapHomologicalComplex (.down ℕ)).map (normalizedChainComplexMap g R) ≫
          ((L.mapHomologicalComplex (.down ℕ)).map (T.fromNormalizedChainComplex R) ≫
            (chainComplexFunctorObjCompMapIso L R).hom.app T ≫
              T.toNormalizedChainComplex (L.obj R)) =
        ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
            (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
              S.toNormalizedChainComplex (L.obj R)) ≫
          normalizedChainComplexMap g (L.obj R)
      simp only [normalizedChainComplexMap, Functor.map_comp, Category.assoc]
      rw [← (L.mapHomologicalComplex (.down ℕ)).map_comp_assoc
        (T.toNormalizedChainComplex R) (T.fromNormalizedChainComplex R),
        toNormalizedChainComplex_fromNormalizedChainComplex,
        map_PInfty_chainComplexFunctorObjCompMapIso_hom_app_assoc R L T,
        PInfty_toNormalizedChainComplex,
        toNormalizedChainComplex_fromNormalizedChainComplex_assoc,
        ← chainComplexMap_PInfty_assoc, PInfty_toNormalizedChainComplex]
      simpa only [Functor.comp_map, Category.assoc] using
        (L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫=
          ((chainComplexFunctorObjCompMapIso L R).hom.naturality g =≫
            T.toNormalizedChainComplex (L.obj R)))

/-- The comparison respects the normalization projection. -/
@[reassoc]
theorem toNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app
    (S : SSet.{w}) :
    (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R) ≫
        (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S =
      (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
        S.toNormalizedChainComplex (L.obj R) := by
  change (L.mapHomologicalComplex (.down ℕ)).map (S.toNormalizedChainComplex R) ≫
      ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
        (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
          S.toNormalizedChainComplex (L.obj R)) = _
  rw [← Functor.map_comp_assoc, toNormalizedChainComplex_fromNormalizedChainComplex,
    map_PInfty_chainComplexFunctorObjCompMapIso_hom_app_assoc R L S,
    PInfty_toNormalizedChainComplex]

/-- The comparison respects the normalization section. -/
@[reassoc]
theorem normalizedChainComplexFunctorObjCompMapIso_hom_app_fromNormalizedChainComplex
    (S : SSet.{w}) :
    (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S ≫
        S.fromNormalizedChainComplex (L.obj R) =
      (L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
        (chainComplexFunctorObjCompMapIso L R).hom.app S := by
  change ((L.mapHomologicalComplex (.down ℕ)).map (S.fromNormalizedChainComplex R) ≫
      (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
        S.toNormalizedChainComplex (L.obj R)) ≫
      S.fromNormalizedChainComplex (L.obj R) = _
  simp only [Category.assoc, toNormalizedChainComplex_fromNormalizedChainComplex]
  rw [← map_PInfty_chainComplexFunctorObjCompMapIso_hom_app R L S,
    ← Functor.map_comp_assoc, ← S.toNormalizedChainComplex_fromNormalizedChainComplex R]
  simp only [← Category.assoc, fromNormalizedChainComplex_toNormalizedChainComplex,
    Category.id_comp]

/-- On every normalized simplex generator, including a degenerate simplex's zero class,
the comparison is the canonical coefficient coproduct map. -/
@[reassoc]
theorem map_ιNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app_f
    (S : SSet.{w}) {n : ℕ} (x : S _⦋n⦌) :
    L.map (S.ιNormalizedChainComplex (R := R) x) ≫
        ((normalizedChainComplexFunctorObjCompMapIso R L).hom.app S).f n =
      S.ιNormalizedChainComplex x := by
  let b : (L.mapHomologicalComplex (.down ℕ)).obj (S.normalizedChainComplex R) ⟶
      S.normalizedChainComplex (L.obj R) :=
    (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S
  change L.map (S.ιNormalizedChainComplex (R := R) x) ≫ b.f n = _
  calc
    L.map (S.ιNormalizedChainComplex (R := R) x) ≫ b.f n =
        L.map (S.ιChainComplex (R := R) x) ≫
          L.map ((S.toNormalizedChainComplex R).f n) ≫ b.f n := by
      rw [← L.map_comp_assoc, ιChainComplex_toNormalizedChainComplex_f]
    _ = L.map (S.ιChainComplex (R := R) x) ≫
        ((chainComplexFunctorObjCompMapIso L R).hom.app S).f n ≫
          (S.toNormalizedChainComplex (L.obj R)).f n :=
      L.map (S.ιChainComplex (R := R) x) ≫=
        HomologicalComplex.congr_hom
          (toNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app R L S) n
    _ = S.ιNormalizedChainComplex x := by
      rw [map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f_assoc,
        ιChainComplex_toNormalizedChainComplex_f]

section UnderlyingCoefficientMorphisms

/-- In each degree, the all-simplex comparison is the coproduct comparison. -/
@[simp]
theorem chainComplexFunctorObjCompMapIso_hom_app_f (S : SSet.{w}) (n : ℕ) :
    ((chainComplexFunctorObjCompMapIso L R).hom.app S).f n =
      (sigmaConstObjCompIso L R).hom.app (S.obj (op ⦋n⦌)) := by
  apply (isColimitOfPreserves L (S.isColimitChainComplexXCofan R n)).hom_ext
  rintro ⟨x⟩
  change L.map (S.ιChainComplex (R := R) x) ≫
      ((chainComplexFunctorObjCompMapIso L R).hom.app S).f n =
    L.map (S.ιChainComplex (R := R) x) ≫
      (sigmaConstObjCompIso L R).hom.app (S.obj (op ⦋n⦌))
  exact (map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f S L (R := R) x).trans
    (map_ι_sigmaConstObjCompIso_hom_app L R x).symm

private theorem normalizedChainComplex_comparison_of_chainComplex
    (S T : SSet.{w}) (Φ : S ⋙ sigmaConst.obj R ⟶ T ⋙ sigmaConst.obj R)
    (Ψ : S ⋙ sigmaConst.obj (L.obj R) ⟶ T ⋙ sigmaConst.obj (L.obj R))
    (h : (L.mapHomologicalComplex (.down ℕ)).map
        ((alternatingFaceMapComplex C).map Φ) ≫
          (chainComplexFunctorObjCompMapIso L R).hom.app T =
      (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
        (alternatingFaceMapComplex D).map Ψ) :
    (L.mapHomologicalComplex (.down ℕ)).map
        ((S.splitting.map (sigmaConst.obj R)).nondegComplexMap
          (T.splitting.map (sigmaConst.obj R)) Φ) ≫
        (normalizedChainComplexFunctorObjCompMapIso R L).hom.app T =
      (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S ≫
        (S.splitting.map (sigmaConst.obj (L.obj R))).nondegComplexMap
          (T.splitting.map (sigmaConst.obj (L.obj R))) Ψ := by
  let K := L.mapHomologicalComplex (.down ℕ)
  let NΦ : S.normalizedChainComplex R ⟶ T.normalizedChainComplex R :=
    (S.splitting.map (sigmaConst.obj R)).nondegComplexMap
      (T.splitting.map (sigmaConst.obj R)) Φ
  let NΨ : S.normalizedChainComplex (L.obj R) ⟶ T.normalizedChainComplex (L.obj R) :=
    (S.splitting.map (sigmaConst.obj (L.obj R))).nondegComplexMap
      (T.splitting.map (sigmaConst.obj (L.obj R))) Ψ
  let bS : K.obj (S.normalizedChainComplex R) ⟶ S.normalizedChainComplex (L.obj R) :=
    (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S
  let bT : K.obj (T.normalizedChainComplex R) ⟶ T.normalizedChainComplex (L.obj R) :=
    (normalizedChainComplexFunctorObjCompMapIso R L).hom.app T
  let aS : K.obj (S.chainComplex R) ⟶ S.chainComplex (L.obj R) :=
    (chainComplexFunctorObjCompMapIso L R).hom.app S
  let aT : K.obj (T.chainComplex R) ⟶ T.chainComplex (L.obj R) :=
    (chainComplexFunctorObjCompMapIso L R).hom.app T
  have hqΦ : S.toNormalizedChainComplex R ≫ NΦ =
      (alternatingFaceMapComplex C).map Φ ≫ T.toNormalizedChainComplex R :=
    (S.splitting.map (sigmaConst.obj R)).toNondegComplex_nondegComplexMap
      (T.splitting.map (sigmaConst.obj R)) Φ
  have hqΨ : S.toNormalizedChainComplex (L.obj R) ≫ NΨ =
      (alternatingFaceMapComplex D).map Ψ ≫ T.toNormalizedChainComplex (L.obj R) :=
    (S.splitting.map (sigmaConst.obj (L.obj R))).toNondegComplex_nondegComplexMap
      (T.splitting.map (sigmaConst.obj (L.obj R))) Ψ
  have hbS : K.map (S.toNormalizedChainComplex R) ≫ bS =
      aS ≫ S.toNormalizedChainComplex (L.obj R) :=
    toNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app R L S
  have hbT : K.map (T.toNormalizedChainComplex R) ≫ bT =
      aT ≫ T.toNormalizedChainComplex (L.obj R) :=
    toNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app R L T
  have hmap : K.map (S.toNormalizedChainComplex R) ≫ K.map NΦ =
      K.map ((alternatingFaceMapComplex C).map Φ) ≫
        K.map (T.toNormalizedChainComplex R) :=
    (K.map_comp (S.toNormalizedChainComplex R) NΦ).symm.trans
      ((congrArg (fun k : S.chainComplex R ⟶ T.normalizedChainComplex R ↦ K.map k)
        hqΦ).trans
        (K.map_comp ((alternatingFaceMapComplex C).map Φ) (T.toNormalizedChainComplex R)))
  -- The projection remains a split epimorphism after applying any functor.
  apply (cancel_epi (K.map (S.toNormalizedChainComplex R))).1
  calc
    K.map (S.toNormalizedChainComplex R) ≫ (K.map NΦ ≫ bT) =
        (K.map (S.toNormalizedChainComplex R) ≫ K.map NΦ) ≫ bT :=
      (Category.assoc _ _ _).symm
    _ = (K.map ((alternatingFaceMapComplex C).map Φ) ≫
        K.map (T.toNormalizedChainComplex R)) ≫ bT :=
      congrArg (fun k : K.obj (S.chainComplex R) ⟶ K.obj (T.normalizedChainComplex R) ↦
        k ≫ bT) hmap
    _ = K.map ((alternatingFaceMapComplex C).map Φ) ≫
        (K.map (T.toNormalizedChainComplex R) ≫ bT) := Category.assoc _ _ _
    _ = K.map ((alternatingFaceMapComplex C).map Φ) ≫
        (aT ≫ T.toNormalizedChainComplex (L.obj R)) :=
      congrArg (fun k : K.obj (T.chainComplex R) ⟶ T.normalizedChainComplex (L.obj R) ↦
        K.map ((alternatingFaceMapComplex C).map Φ) ≫ k) hbT
    _ = (K.map ((alternatingFaceMapComplex C).map Φ) ≫ aT) ≫
        T.toNormalizedChainComplex (L.obj R) := (Category.assoc _ _ _).symm
    _ = (aS ≫ (alternatingFaceMapComplex D).map Ψ) ≫
        T.toNormalizedChainComplex (L.obj R) :=
      congrArg (fun k : K.obj (S.chainComplex R) ⟶ T.chainComplex (L.obj R) ↦
        k ≫ T.toNormalizedChainComplex (L.obj R)) h
    _ = aS ≫ ((alternatingFaceMapComplex D).map Ψ ≫
        T.toNormalizedChainComplex (L.obj R)) := Category.assoc _ _ _
    _ = aS ≫ (S.toNormalizedChainComplex (L.obj R) ≫ NΨ) :=
      congrArg (fun k : S.chainComplex (L.obj R) ⟶ T.normalizedChainComplex (L.obj R) ↦
        aS ≫ k) hqΨ.symm
    _ = (aS ≫ S.toNormalizedChainComplex (L.obj R)) ≫ NΨ := (Category.assoc _ _ _).symm
    _ = (K.map (S.toNormalizedChainComplex R) ≫ bS) ≫ NΨ :=
      congrArg (fun k : K.obj (S.chainComplex R) ⟶ S.normalizedChainComplex (L.obj R) ↦
        k ≫ NΨ) hbS.symm
    _ = K.map (S.toNormalizedChainComplex R) ≫ (bS ≫ NΨ) := Category.assoc _ _ _

/-- The normalized coefficient comparison commutes with every coefficient-valued
simplicial morphism, not only those induced by simplicial-set maps or compatible
with the chosen nondegenerate summands. The target morphism is transported through
the coproduct comparison. -/
theorem normalizedChainComplexFunctorObjCompMapIso_nondegComplexMap
    (S T : SSet.{w}) (Φ : S ⋙ sigmaConst.obj R ⟶ T ⋙ sigmaConst.obj R) :
    let ΦD : S ⋙ sigmaConst.obj (L.obj R) ⟶ T ⋙ sigmaConst.obj (L.obj R) :=
      Functor.whiskerLeft S (sigmaConstObjCompIso L R).inv ≫
        Functor.whiskerRight Φ L ≫
          Functor.whiskerLeft T (sigmaConstObjCompIso L R).hom
    (L.mapHomologicalComplex (.down ℕ)).map
        ((S.splitting.map (sigmaConst.obj R)).nondegComplexMap
          (T.splitting.map (sigmaConst.obj R)) Φ) ≫
        (normalizedChainComplexFunctorObjCompMapIso R L).hom.app T =
      (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S ≫
        (S.splitting.map (sigmaConst.obj (L.obj R))).nondegComplexMap
          (T.splitting.map (sigmaConst.obj (L.obj R))) ΦD := by
  dsimp only
  apply normalizedChainComplex_comparison_of_chainComplex R L
  ext n : 1
  simp

/-- Normalized transfer for an equifibered simplicial map with finite vertex fibers
commutes with any additive coefficient functor preserving coproducts indexed in
the simplex universe. No constant fiber cardinal or exactness is required. -/
@[reassoc]
theorem normalizedChainComplexFunctorObjCompMapIso_finiteFiberTransfer
    {F G : SSet.{w}} (p : F ⟶ G) (hp : NatTrans.Equifibered p)
    (hf : ∀ g : G _⦋0⦌, Finite {f : F _⦋0⦌ // p.app _ f = g}) :
    (L.mapHomologicalComplex (.down ℕ)).map
        ((G.splitting.map (sigmaConst.obj R)).nondegComplexMap
          (F.splitting.map (sigmaConst.obj R))
          (equifiberedSigmaTransfer p hp (finite_fiber_of_finite_vertices p hp hf) R)) ≫
        (normalizedChainComplexFunctorObjCompMapIso R L).hom.app F =
      (normalizedChainComplexFunctorObjCompMapIso R L).hom.app G ≫
        (G.splitting.map (sigmaConst.obj (L.obj R))).nondegComplexMap
          (F.splitting.map (sigmaConst.obj (L.obj R)))
          (equifiberedSigmaTransfer p hp
            (finite_fiber_of_finite_vertices p hp hf) (L.obj R)) := by
  apply normalizedChainComplex_comparison_of_chainComplex R L
  exact chainComplexTransfer_mapHomologicalComplex p hp L hf R

end UnderlyingCoefficientMorphisms

end CoefficientComparison

section CoefficientFunctorNaturality

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasCoproducts.{w} D]
  (L M : C ⥤ D) [L.Additive] [M.Additive]
  [∀ (T : Type w), PreservesColimitsOfShape (Discrete T) L]
  [∀ (T : Type w), PreservesColimitsOfShape (Discrete T) M]

/-- The all-simplex coefficient comparison is natural in a transformation of
additive coproduct-preserving coefficient functors. -/
@[reassoc]
theorem chainComplexFunctorObjCompMapIso_naturality (θ : L ⟶ M) (S : SSet.{w}) :
    (θ.mapHomologicalComplex (.down ℕ)).app (S.chainComplex R) ≫
        (chainComplexFunctorObjCompMapIso M R).hom.app S =
      (chainComplexFunctorObjCompMapIso L R).hom.app S ≫
        (alternatingFaceMapComplex D).map
          (Functor.whiskerLeft S (sigmaConst.map (θ.app R))) := by
  ext n : 1
  apply (isColimitOfPreserves L (S.isColimitChainComplexXCofan R n)).hom_ext
  rintro ⟨x⟩
  change L.map (S.ιChainComplex x) ≫ θ.app _ ≫
      ((chainComplexFunctorObjCompMapIso M R).hom.app S).f n =
    L.map (S.ιChainComplex x) ≫
      ((chainComplexFunctorObjCompMapIso L R).hom.app S).f n ≫
        (sigmaConst.map (θ.app R)).app _
  rw [θ.naturality_assoc,
    map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f,
    map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f_assoc]
  exact (Sigma.ι_map (fun _ ↦ θ.app R) x).symm

/-- The normalized coefficient comparison is natural in a transformation of
additive coproduct-preserving coefficient functors. The transformation acts on the
normalized source complex; on the target it acts coefficientwise on the
coproducts and then descends to normalization. -/
@[reassoc]
theorem normalizedChainComplexFunctorObjCompMapIso_naturality
    (θ : L ⟶ M) (S : SSet.{w}) :
    (θ.mapHomologicalComplex (.down ℕ)).app (S.normalizedChainComplex R) ≫
        (normalizedChainComplexFunctorObjCompMapIso R M).hom.app S =
      (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S ≫
        (S.splitting.map (sigmaConst.obj (L.obj R))).nondegComplexMap
          (S.splitting.map (sigmaConst.obj (M.obj R)))
          (Functor.whiskerLeft S (sigmaConst.map (θ.app R))) := by
  let K := L.mapHomologicalComplex (.down ℕ)
  let K' := M.mapHomologicalComplex (.down ℕ)
  let N : S.normalizedChainComplex (L.obj R) ⟶ S.normalizedChainComplex (M.obj R) :=
    (S.splitting.map (sigmaConst.obj (L.obj R))).nondegComplexMap
      (S.splitting.map (sigmaConst.obj (M.obj R)))
      (Functor.whiskerLeft S (sigmaConst.map (θ.app R)))
  let bL : K.obj (S.normalizedChainComplex R) ⟶ S.normalizedChainComplex (L.obj R) :=
    (normalizedChainComplexFunctorObjCompMapIso R L).hom.app S
  let bM : K'.obj (S.normalizedChainComplex R) ⟶ S.normalizedChainComplex (M.obj R) :=
    (normalizedChainComplexFunctorObjCompMapIso R M).hom.app S
  let aL : K.obj (S.chainComplex R) ⟶ S.chainComplex (L.obj R) :=
    (chainComplexFunctorObjCompMapIso L R).hom.app S
  let aM : K'.obj (S.chainComplex R) ⟶ S.chainComplex (M.obj R) :=
    (chainComplexFunctorObjCompMapIso M R).hom.app S
  let tN : K.obj (S.normalizedChainComplex R) ⟶ K'.obj (S.normalizedChainComplex R) :=
    (θ.mapHomologicalComplex (.down ℕ)).app (S.normalizedChainComplex R)
  let tK : K.obj (S.chainComplex R) ⟶ K'.obj (S.chainComplex R) :=
    (θ.mapHomologicalComplex (.down ℕ)).app (S.chainComplex R)
  let A : S.chainComplex (L.obj R) ⟶ S.chainComplex (M.obj R) :=
    (alternatingFaceMapComplex D).map
      (Functor.whiskerLeft S (sigmaConst.map (θ.app R)))
  have htq : K.map (S.toNormalizedChainComplex R) ≫ tN =
      tK ≫ K'.map (S.toNormalizedChainComplex R) :=
    (θ.mapHomologicalComplex (.down ℕ)).naturality (S.toNormalizedChainComplex R)
  have hbL : K.map (S.toNormalizedChainComplex R) ≫ bL =
      aL ≫ S.toNormalizedChainComplex (L.obj R) :=
    toNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app R L S
  have hbM : K'.map (S.toNormalizedChainComplex R) ≫ bM =
      aM ≫ S.toNormalizedChainComplex (M.obj R) :=
    toNormalizedChainComplex_normalizedChainComplexFunctorObjCompMapIso_hom_app R M S
  have hq : S.toNormalizedChainComplex (L.obj R) ≫ N =
      A ≫ S.toNormalizedChainComplex (M.obj R) :=
    (S.splitting.map (sigmaConst.obj (L.obj R))).toNondegComplex_nondegComplexMap
      (S.splitting.map (sigmaConst.obj (M.obj R)))
      (Functor.whiskerLeft S (sigmaConst.map (θ.app R)))
  have hA : tK ≫ aM = aL ≫ A :=
    chainComplexFunctorObjCompMapIso_naturality R L M θ S
  apply (cancel_epi (K.map (S.toNormalizedChainComplex R))).1
  calc
    K.map (S.toNormalizedChainComplex R) ≫ (tN ≫ bM) =
        (K.map (S.toNormalizedChainComplex R) ≫ tN) ≫ bM := (Category.assoc _ _ _).symm
    _ = (tK ≫ K'.map (S.toNormalizedChainComplex R)) ≫ bM :=
      congrArg (fun k : K.obj (S.chainComplex R) ⟶ K'.obj (S.normalizedChainComplex R) ↦
        k ≫ bM) htq
    _ = tK ≫ (K'.map (S.toNormalizedChainComplex R) ≫ bM) := Category.assoc _ _ _
    _ = tK ≫ (aM ≫ S.toNormalizedChainComplex (M.obj R)) :=
      congrArg (fun k : K'.obj (S.chainComplex R) ⟶ S.normalizedChainComplex (M.obj R) ↦
        tK ≫ k) hbM
    _ = (tK ≫ aM) ≫ S.toNormalizedChainComplex (M.obj R) := (Category.assoc _ _ _).symm
    _ = (aL ≫ A) ≫ S.toNormalizedChainComplex (M.obj R) :=
      congrArg (fun k : K.obj (S.chainComplex R) ⟶ S.chainComplex (M.obj R) ↦
        k ≫ S.toNormalizedChainComplex (M.obj R)) hA
    _ = aL ≫ (A ≫ S.toNormalizedChainComplex (M.obj R)) := Category.assoc _ _ _
    _ = aL ≫ (S.toNormalizedChainComplex (L.obj R) ≫ N) :=
      congrArg (fun k : S.chainComplex (L.obj R) ⟶ S.normalizedChainComplex (M.obj R) ↦
        aL ≫ k) hq.symm
    _ = (aL ≫ S.toNormalizedChainComplex (L.obj R)) ≫ N := (Category.assoc _ _ _).symm
    _ = (K.map (S.toNormalizedChainComplex R) ≫ bL) ≫ N :=
      congrArg (fun k : K.obj (S.chainComplex R) ⟶ S.normalizedChainComplex (L.obj R) ↦
        k ≫ N) hbL.symm
    _ = K.map (S.toNormalizedChainComplex R) ≫ (bL ≫ N) := Category.assoc _ _ _

end CoefficientFunctorNaturality

end SSet
