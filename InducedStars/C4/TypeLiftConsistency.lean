import InducedStars.C4.TypeLift

/-!
# Realization error of the lifted C4 type

Paper: the estimate `d(G,R') ≤ 3 τ n²` in `lemma:c4-rough-struc`.
Missing template pairs impose no consistency requirement. Only errors inside
clusters and wrong edges in the low/high density regular pairs are counted.
-/

noncomputable section
open Finset InducedStars.Regularity InducedStars.Regularity.RegularityColoredGraph
open scoped Classical
namespace InducedStars

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {eta tau : ℝ}

private def blueDensityErrors (A B : Finset (Fin n)) (tau : ℝ) :
    Finset (Fin n × Fin n) :=
  if 1 - tau < graphDensity G A B then Rel.interedges (fun x y ↦ ¬G.Adj x y) A B
  else ∅

private def greenDensityErrors (A B : Finset (Fin n)) (tau : ℝ) :
    Finset (Fin n × Fin n) :=
  if graphDensity G A B < tau then G.interedges A B else ∅

private theorem densityErrors_card_le (P : RegularPartition G eta) (htau : 0 ≤ tau)
    (i j : Fin P.clusterCount) :
    ((blueDensityErrors (G := G) (P.clusters i) (P.clusters j) tau).card : ℝ) ≤
        tau * (P.clusterSize : ℝ)^2 ∧
      ((greenDensityErrors (G := G) (P.clusters i) (P.clusters j) tau).card : ℝ) ≤
        tau * (P.clusterSize : ℝ)^2 := by
  let A := P.clusters i
  let B := P.clusters j
  have hcardA : A.card = P.clusterSize := P.cluster_card_eq i
  have hcardB : B.card = P.clusterSize := P.cluster_card_eq j
  have hsum : ((G.interedges A B).card : ℝ) +
      ((Rel.interedges (fun x y ↦ ¬G.Adj x y) A B).card : ℝ) =
      (P.clusterSize : ℝ)^2 := by
    have h := Rel.card_interedges_add_card_interedges_compl G.Adj A B
    change (G.interedges A B).card + _ = _ at h
    rw [hcardA, hcardB] at h
    simpa only [pow_two] using (show ((G.interedges A B).card : ℝ) +
      ((Rel.interedges (fun x y ↦ ¬G.Adj x y) A B).card : ℝ) =
      (P.clusterSize : ℝ)*P.clusterSize by exact_mod_cast h)
  have hd : graphDensity G A B = (G.interedges A B).card / (P.clusterSize : ℝ)^2 := by
    rw [graphDensity_eq, hcardA, hcardB, pow_two]
  by_cases hz : P.clusterSize = 0
  · have hA : A = ∅ := card_eq_zero.mp (hcardA.trans hz)
    change ((blueDensityErrors A B tau).card : ℝ) ≤ _ ∧
      ((greenDensityErrors A B tau).card : ℝ) ≤ _
    simp [blueDensityErrors, greenDensityErrors, hA, hz, SimpleGraph.interedges,
      Rel.interedges]
  have hpos : 0 < (P.clusterSize : ℝ)^2 := by
    exact sq_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hz)
  constructor
  · change ((blueDensityErrors A B tau).card : ℝ) ≤ _
    unfold blueDensityErrors
    split_ifs with h
    · rw [hd] at h
      have hlt := (lt_div_iff₀ hpos).mp h
      nlinarith
    · simp only [card_empty, Nat.cast_zero]
      positivity
  · change ((greenDensityErrors A B tau).card : ℝ) ≤ _
    unfold greenDensityErrors
    split_ifs with h
    · rw [hd] at h
      exact ((div_lt_iff₀ hpos).mp h).le
    · simp only [card_empty, Nat.cast_zero]
      positivity

private def liftedInconsistencyPairCover (T : RegularityType G eta tau 4) :
    Finset (Fin n × Fin n) :=
  (univ.biUnion fun i ↦ T.partition.clusters i ×ˢ T.partition.clusters i) ∪
    (univ.biUnion fun ij : Fin T.partition.clusterCount × Fin T.partition.clusterCount ↦
      blueDensityErrors (G := G) (T.partition.clusters ij.1) (T.partition.clusters ij.2) tau) ∪
    (univ.biUnion fun ij : Fin T.partition.clusterCount × Fin T.partition.clusterCount ↦
      greenDensityErrors (G := G) (T.partition.clusters ij.1) (T.partition.clusters ij.2) tau)

private theorem liftedInconsistency_subset (T : RegularityType G eta tau 4)
    (hk : 0 < T.partition.clusterCount) :
    DenseGraph.coloredInconsistencyFinset G (c4LiftedType T hk) ⊆
      (liftedInconsistencyPairCover T).image Sym2.mk.uncurry := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hh := (DenseGraph.mem_coloredInconsistencyFinset G (c4LiftedType T hk) s(x,y)).mp he
    have he : (c4LiftedType T hk).graph.Adj x y := by
      by_contra h
      simp only [DenseGraph.coloredPairStatus_mk, dif_neg h, reduceCtorEq,
        false_and, or_self, and_false] at hh
    have ha := (c4LiftedType_adj T hk x y).mp he
    let i := c4TypeClusterLabel T.partition hk x
    let j := c4TypeClusterLabel T.partition hk y
    have hx : x ∈ T.partition.clusters i := c4TypeClusterLabel_mem _ hk ha.2.1
    have hy : y ∈ T.partition.clusters j := c4TypeClusterLabel_mem _ hk ha.2.2.1
    apply mem_image.mpr
    refine ⟨(x,y), ?_, rfl⟩
    unfold liftedInconsistencyPairCover
    by_cases hij : i = j
    · apply mem_union_left
      apply mem_union_left
      exact mem_biUnion.mpr ⟨i, mem_univ _, mem_product.mpr ⟨hx, hij ▸ hy⟩⟩
    have hred : T.coloredGraph.graph.Adj i j := ha.2.2.2.resolve_left hij
    have hc : (c4LiftedType T hk).getEdgeColor x y he =
        T.coloredGraph.getEdgeColor i j hred := by
      change DenseGraph.coloredBlowUpLabel T.coloredGraph
        (c4TypeClusterLabel T.partition hk) {v | v ∉ T.partition.exceptional} x y he = _
      dsimp only [i, j] at hij ⊢
      simp only [DenseGraph.coloredBlowUpLabel, dif_neg hij]
    rcases hh.2 with hb | hg
    · have hb' : T.coloredGraph.getEdgeColor i j hred = .blue := by
        simpa only [DenseGraph.coloredPairStatus_mk, dif_pos he, hc, Option.some.injEq] using hb.1
      have hd := (edgeColor_eq_blue_iff T.partition T.delta_lt_half.le T.vertexColor hred).mp hb'
      apply mem_union_left
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨(i,j), mem_univ _, ?_⟩
      simp only [blueDensityErrors, if_pos hd, Rel.mem_interedges_iff]
      exact ⟨hx, hy, hb.2⟩
    · have hg' : T.coloredGraph.getEdgeColor i j hred = .green := by
        simpa only [DenseGraph.coloredPairStatus_mk, dif_pos he, hc, Option.some.injEq] using hg.1
      have hd := (edgeColor_eq_green_iff T.partition T.delta_lt_half.le T.vertexColor hred).mp hg'
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨(i,j), mem_univ _, ?_⟩
      simp only [greenDensityErrors, if_pos hd, SimpleGraph.mem_interedges_iff]
      exact ⟨hx, hy, hg.2⟩

private theorem liftedInconsistencyPairCover_card_le (T : RegularityType G eta tau 4) :
    ((liftedInconsistencyPairCover T).card : ℝ) ≤
      T.partition.clusterCount * (T.partition.clusterSize : ℝ)^2 +
        2*tau*(T.partition.clusterCount : ℝ)^2*(T.partition.clusterSize : ℝ)^2 := by
  let P := T.partition
  have hw : ((univ.biUnion fun i ↦ P.clusters i ×ˢ P.clusters i).card : ℝ) ≤
      P.clusterCount * (P.clusterSize : ℝ)^2 := by
    have h := card_biUnion_le (s := univ) (t := fun i ↦ P.clusters i ×ˢ P.clusters i)
    simp only [card_product, P.cluster_card_eq, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at h
    simpa only [pow_two] using (show
      ((univ.biUnion fun i ↦ P.clusters i ×ˢ P.clusters i).card : ℝ) ≤
        P.clusterCount*((P.clusterSize : ℝ)*P.clusterSize) by exact_mod_cast h)
  have hb : ((univ.biUnion fun ij : Fin P.clusterCount × Fin P.clusterCount ↦
      blueDensityErrors (G := G) (P.clusters ij.1) (P.clusters ij.2) tau).card : ℝ) ≤
      tau * (P.clusterCount : ℝ)^2 * (P.clusterSize : ℝ)^2 := by
    calc
      _ ≤ ∑ ij : Fin P.clusterCount × Fin P.clusterCount,
          ((blueDensityErrors (G := G) (P.clusters ij.1) (P.clusters ij.2) tau).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := univ)
          (t := fun ij : Fin P.clusterCount × Fin P.clusterCount ↦
            blueDensityErrors (G := G) (P.clusters ij.1) (P.clusters ij.2) tau))
      _ ≤ ∑ _ij : Fin P.clusterCount × Fin P.clusterCount, tau*(P.clusterSize : ℝ)^2 :=
        sum_le_sum fun ij _ ↦ (densityErrors_card_le P T.delta_pos.le ij.1 ij.2).1
      _ = _ := by simp [pow_two]; ring
  have hg : ((univ.biUnion fun ij : Fin P.clusterCount × Fin P.clusterCount ↦
      greenDensityErrors (G := G) (P.clusters ij.1) (P.clusters ij.2) tau).card : ℝ) ≤
      tau * (P.clusterCount : ℝ)^2 * (P.clusterSize : ℝ)^2 := by
    calc
      _ ≤ ∑ ij : Fin P.clusterCount × Fin P.clusterCount,
          ((greenDensityErrors (G := G) (P.clusters ij.1) (P.clusters ij.2) tau).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := univ)
          (t := fun ij : Fin P.clusterCount × Fin P.clusterCount ↦
            greenDensityErrors (G := G) (P.clusters ij.1) (P.clusters ij.2) tau))
      _ ≤ ∑ _ij : Fin P.clusterCount × Fin P.clusterCount, tau*(P.clusterSize : ℝ)^2 :=
        sum_le_sum fun ij _ ↦ (densityErrors_card_le P T.delta_pos.le ij.1 ij.2).2
      _ = _ := by simp [pow_two]; ring
  unfold liftedInconsistencyPairCover
  have hu := card_union_le
    ((univ.biUnion fun i ↦ P.clusters i ×ˢ P.clusters i) ∪
      (univ.biUnion fun ij : Fin P.clusterCount × Fin P.clusterCount ↦
        blueDensityErrors (G := G) (P.clusters ij.1) (P.clusters ij.2) tau))
    (univ.biUnion fun ij : Fin P.clusterCount × Fin P.clusterCount ↦
      greenDensityErrors (G := G) (P.clusters ij.1) (P.clusters ij.2) tau)
  have hu' := card_union_le (univ.biUnion fun i ↦ P.clusters i ×ˢ P.clusters i)
    (univ.biUnion fun ij : Fin P.clusterCount × Fin P.clusterCount ↦
      blueDensityErrors (G := G) (P.clusters ij.1) (P.clusters ij.2) tau)
  have huR := (Nat.cast_le (α := ℝ)).mpr hu
  have huR' := (Nat.cast_le (α := ℝ)).mpr hu'
  push_cast at huR huR'
  change _ ≤ P.clusterCount*(P.clusterSize : ℝ)^2 +
    2*tau*(P.clusterCount : ℝ)^2*(P.clusterSize : ℝ)^2
  linarith

/-- The genuine realization error, uniformly for every graph carrying the
type. Exceptional and irregular pairs cost zero, since they are absent from
the template. -/
theorem c4LiftedType_inconsistency_le (T : RegularityType G eta tau 4)
    (hk : 0 < T.partition.clusterCount) :
    (DenseGraph.coloredInconsistency G (c4LiftedType T hk) : ℝ) ≤
      (1 / (T.partition.clusterCount : ℝ) + 2*tau) * (n : ℝ)^2 := by
  let P := T.partition
  have hcard := (card_le_card (liftedInconsistency_subset T hk)).trans card_image_le
  have hbound := (Nat.cast_le (α := ℝ)).mpr hcard
  have hcover := P.exceptional_card_add_mul_clusterSize_eq
  have hprod : (P.clusterCount : ℝ)*P.clusterSize ≤ n := by
    exact_mod_cast (by omega : P.clusterCount*P.clusterSize ≤ n)
  have hsq : (P.clusterCount : ℝ)^2*(P.clusterSize : ℝ)^2 ≤ (n : ℝ)^2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hprod 2
  have hkR : 0 < (P.clusterCount : ℝ) := by exact_mod_cast hk
  have hw : (P.clusterCount : ℝ)*(P.clusterSize : ℝ)^2 ≤ (n : ℝ)^2/P.clusterCount := by
    apply (le_div_iff₀ hkR).mpr
    nlinarith
  have hx := mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    T.delta_pos.le)
  have hraw := liftedInconsistencyPairCover_card_le T
  change _ ≤ (1/(P.clusterCount : ℝ)+2*tau)*(n : ℝ)^2
  unfold DenseGraph.coloredInconsistency
  nlinarith [show (n : ℝ)^2/P.clusterCount =
    (1/(P.clusterCount : ℝ))*(n : ℝ)^2 by ring]

/-- Paper: the realization-error estimate in `lemma:c4-rough-struc`. -/
theorem c4LiftedType_inconsistency_le_three_mul (T : RegularityType G eta tau 4)
    (hk : 0 < T.partition.clusterCount)
    (hclusters : 1 / (T.partition.clusterCount : ℝ) ≤ tau) :
    (DenseGraph.coloredInconsistency G (c4LiftedType T hk) : ℝ) ≤ 3*tau*(n : ℝ)^2 := by
  exact (c4LiftedType_inconsistency_le T hk).trans
    (by nlinarith [sq_nonneg (n : ℝ)])

/-- The source's cluster-count hypothesis implies the uniform three-tau bound. -/
theorem c4LiftedType_inconsistency_le_of_ceil (T : RegularityType G eta tau 4)
    (hk : 0 < T.partition.clusterCount)
    (hclusters : Nat.ceil (1 / tau) ≤ T.partition.clusterCount) :
    (DenseGraph.coloredInconsistency G (c4LiftedType T hk) : ℝ) ≤ 3*tau*(n : ℝ)^2 := by
  apply c4LiftedType_inconsistency_le_three_mul T hk
  have hc : (1 / tau : ℝ) ≤ T.partition.clusterCount :=
    (Nat.le_ceil (1 / tau)).trans (by exact_mod_cast hclusters)
  have hmul := (div_le_iff₀ T.delta_pos).mp hc
  apply (div_le_iff₀ (by exact_mod_cast hk : (0 : ℝ) < T.partition.clusterCount)).mpr
  nlinarith

end InducedStars
