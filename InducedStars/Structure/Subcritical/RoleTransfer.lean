import InducedStars.Structure.Subcritical.RowCounting
import DenseGraph.FiniteModels.RestrictedPatternWitness

/-!
# Transferring restricted subcritical role patterns

This is the common finite transfer step for the three deterministic row
arguments.  Repeated division parents are grouped only when the visible cut
estimate is obtained; the individual role sets remain disjoint inside their
common union, where the normalized induced-pattern count is evaluated.
-/

noncomputable section

open Finset Set DenseGraph DenseGraph.FiniteWeightedGraph
open scoped BigOperators Classical SimpleGraph

namespace InducedStars

variable {k n R₀ : ℕ} {hk : 3 ≤ k}
  {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
  {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ}

/-- A role set regarded as a finset in the union of all role sets. -/
def subcriticalRestrictedRole
    (S : Fin k → Finset (Fin n)) (i : Fin k) :
    Finset ↥(visibleCutPartUnion S) :=
  (visibleCutPartUnion S).attach.filter fun x ↦ x.val ∈ S i

@[simp] theorem mem_subcriticalRestrictedRole
    (S : Fin k → Finset (Fin n)) (i : Fin k)
    (x : ↥(visibleCutPartUnion S)) :
    x ∈ subcriticalRestrictedRole S i ↔ x.val ∈ S i := by
  simp [subcriticalRestrictedRole]

theorem role_subset_visibleCutPartUnion
    (S : Fin k → Finset (Fin n)) (i : Fin k) :
    S i ⊆ visibleCutPartUnion S := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩

@[simp] theorem card_subcriticalRestrictedRole
    (S : Fin k → Finset (Fin n)) (i : Fin k) :
    (subcriticalRestrictedRole S i).card = (S i).card := by
  classical
  let U := visibleCutPartUnion S
  have hmap :
      (subcriticalRestrictedRole S i).map (restrictToFinsetEmbedding U) = S i := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact (mem_subcriticalRestrictedRole S i y).mp hy
    · intro hx
      have hxU : x ∈ U := by
        exact role_subset_visibleCutPartUnion S i hx
      exact Finset.mem_map.mpr
        ⟨⟨x, hxU⟩, (mem_subcriticalRestrictedRole S i ⟨x, hxU⟩).mpr hx, rfl⟩
  have hcard := congrArg Finset.card hmap
  simpa [U] using hcard

theorem subcriticalRestrictedRole_pairwiseDisjoint
    (S : Fin k → Finset (Fin n))
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin k)) S) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin k))
      (subcriticalRestrictedRole S) := by
  intro i _ j _ hij
  change Disjoint (subcriticalRestrictedRole S i)
    (subcriticalRestrictedRole S j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  have hd : Disjoint (S i) (S j) :=
    hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij
  exact Finset.disjoint_left.mp hd
    ((mem_subcriticalRestrictedRole S i x).mp hxi)
    ((mem_subcriticalRestrictedRole S j x).mp hxj)

theorem card_visibleCutPartUnion_eq_mul_of_equal_card
    (S : Fin k → Finset (Fin n))
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin k)) S)
    {s : ℕ} (hcard : ∀ i, (S i).card = s) :
    (visibleCutPartUnion S).card = k * s := by
  have hdisjoint' : Set.PairwiseDisjoint
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)) S := by
    simpa using hdisjoint
  rw [visibleCutPartUnion, Finset.card_biUnion hdisjoint']
  simp_rw [hcard]
  simp

private theorem ofSimpleGraph_induce_visibleCutPartUnion
    (S : Fin k → Finset (Fin n)) :
    ofSimpleGraph (G.induce (↑(visibleCutPartUnion S) : Set (Fin n))) =
      (ofSimpleGraph G).restrictToFinset (visibleCutPartUnion S) := by
  classical
  ext x y
  simp [ofSimpleGraph]

/-- A positive lower bound for every division-palette factor transfers one
exact restricted pattern to the original graph.  The root vertices used by
later applications are not among these `k` free roles.

Repeated values of `parent` are permitted.  They are grouped internally for
the cut estimate, while pairwise disjointness of `S` supplies injectivity of
the final transversal.
-/
theorem subcritical_exists_transversal_of_roleFactors
    (hk : 3 ≤ k)
    (R : SubcriticalCloseStructureResult hk G D L R₀
      omega eta theta alpha delta epsilon)
    (F : SimpleGraph (Fin k))
    (parent : Fin k →
      {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (S : Fin k → Finset (Fin n))
    (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    {s : ℕ} (hs : 0 < s) (hcard : ∀ i, (S i).card = s)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin k)) S)
    (hpart : ∀ i, S i ⊆ D.part (parent i).val)
    (hsize : ∀ i, alpha * theta * n / 4 ≤ ((S i).card : ℝ))
    (hfactor : ∀ a b, a ≠ b →
      subcriticalPaletteGap k ≤
        if F.Adj a b then
          subcriticalDivisionPartWeight D (parent a).val (parent b).val
        else
          1 - subcriticalDivisionPartWeight D (parent a).val (parent b).val) :
    ∃ f : Fin k ↪ Fin n,
      (∀ i, f i ∈ S i) ∧
        ∀ i j, F.Adj i j ↔ G.Adj (f i) (f j) := by
  classical
  let U := visibleCutPartUnion S
  let hostGraph : SimpleGraph U := G.induce (↑U : Set (Fin n))
  let hostKernel : FiniteWeightedGraph U :=
    (ofSimpleGraph G).restrictToFinset U
  let modelKernel : FiniteWeightedGraph U :=
    (subcriticalDivisionWeightedGraph hk D).restrictToFinset U
  let role : Fin k → Finset U := subcriticalRestrictedRole S
  let pairFactor : FinitePatternPair k → ℝ := fun e ↦
    if F.Adj e.val.1 e.val.2 then
      subcriticalDivisionPartWeight D (parent e.val.1).val (parent e.val.2).val
    else
      1 - subcriticalDivisionPartWeight D
        (parent e.val.1).val (parent e.val.2).val
  have hcardU : Fintype.card U = k * s := by
    simpa only [U, Fintype.card_coe] using
      card_visibleCutPartUnion_eq_mul_of_equal_card S hdisjoint hcard
  have hcardRole : ∀ i, (role i).card = s := by
    intro i
    dsimp only [role]
    exact (card_subcriticalRestrictedRole S i).trans (hcard i)
  have hroleDisjoint :
      Set.PairwiseDisjoint (Set.univ : Set (Fin k)) role := by
    simpa only [role] using subcriticalRestrictedRole_pairwiseDisjoint S hdisjoint
  have hconstant : ∀ (x : Fin k → U), (∀ i, x i ∈ role i) →
      ∀ e, restrictedInducedPairFactor F modelKernel e x = pairFactor e := by
    intro x hx e
    have hxleft : (x e.val.1).val ∈ S e.val.1 := by
      exact (mem_subcriticalRestrictedRole S e.val.1 (x e.val.1)).mp
        (by simpa only [role] using hx e.val.1)
    have hxright : (x e.val.2).val ∈ S e.val.2 := by
      exact (mem_subcriticalRestrictedRole S e.val.2 (x e.val.2)).mp
        (by simpa only [role] using hx e.val.2)
    have hw := subcriticalDivisionWeightedGraph_weight_eq_partWeight hk D
      (hpart e.val.1 hxleft) (hpart e.val.2 hxright)
    simp only [restrictedInducedPairFactor, modelKernel,
      restrictToFinset_weight, pairFactor]
    split_ifs
    · exact hw
    · exact congrArg (fun z : ℝ ↦ 1 - z) hw
  have hmodelLower : subcriticalRowCountingLower k ≤
      restrictedInducedPatternCount F modelKernel role := by
    exact one_div_pow_mul_pair_lower_le_restrictedInducedPatternCount
      F modelKernel role pairFactor (by omega) hs
      (subcriticalPaletteGap_pos hk).le hcardU hcardRole hconstant
      (fun e ↦ hfactor e.val.1 e.val.2 (ne_of_lt e.property))
  have hcut : finiteLabeledCutDist hostKernel modelKernel ≤ delta := by
    simpa only [hostKernel, modelKernel, U] using
      R.groupedRoles_visibleSetCutCloseness halpha htheta parent S hpart hsize
  have hUpos : 0 < Fintype.card U := by
    rw [hcardU]
    exact Nat.mul_pos (by omega) hs
  have hcountDiff :
      |restrictedInducedPatternCount F hostKernel role -
          restrictedInducedPatternCount F modelKernel role| ≤
        (Nat.choose k 2 : ℝ) * finiteLabeledCutDist hostKernel modelKernel := by
    exact abs_restrictedInducedPatternCount_sub_le_choose_mul_finiteLabeledCutDist
      hUpos F hostKernel modelKernel role
  have hcountDiffLt :
      |restrictedInducedPatternCount F hostKernel role -
          restrictedInducedPatternCount F modelKernel role| <
        subcriticalRowCountingLower k := by
    calc
      _ ≤ (Nat.choose k 2 : ℝ) * finiteLabeledCutDist hostKernel modelKernel :=
        hcountDiff
      _ ≤ (Nat.choose k 2 : ℝ) * delta := by
        gcongr
      _ ≤ (Nat.choose k 2 : ℝ) * subcriticalRowCountingTolerance k := by
        gcongr
      _ < subcriticalRowCountingLower k :=
        subcriticalRowCountingTolerance_preserves_positive hk
  have hhostPos : 0 < restrictedInducedPatternCount F hostKernel role := by
    have hreverse :
        restrictedInducedPatternCount F modelKernel role -
            restrictedInducedPatternCount F hostKernel role ≤
          |restrictedInducedPatternCount F hostKernel role -
            restrictedInducedPatternCount F modelKernel role| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith
  have hkernel : ofSimpleGraph hostGraph = hostKernel := by
    simpa only [hostGraph, hostKernel, U] using
      (ofSimpleGraph_induce_visibleCutPartUnion (G := G) S)
  have hhostGraphPos :
      0 < restrictedInducedPatternCount F (ofSimpleGraph hostGraph) role := by
    rwa [hkernel]
  obtain ⟨phi, hphiRole⟩ :=
    exists_restricted_induced_pattern_embedding_of_pos
      F hostGraph role hroleDisjoint hhostGraphPos
  let f : Fin k ↪ Fin n :=
    phi.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨f, ?_, ?_⟩
  · intro i
    have hiRole : phi i ∈ role i := hphiRole i
    exact (mem_subcriticalRestrictedRole S i (phi i)).mp
      (by simpa only [role] using hiRole)
  · intro i j
    change F.Adj i j ↔ G.Adj (phi i).val (phi j).val
    exact phi.map_rel_iff.symm

end InducedStars
