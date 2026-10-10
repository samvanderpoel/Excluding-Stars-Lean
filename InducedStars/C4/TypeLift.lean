import InducedStars.C4.ColoredDistance
import DenseGraph.Regularity.ColoredBlowUp
import InducedStars.Graphon.PartitionAlignment
import InducedStars.Graphon.PartitionCut

/-!
# The actual lifted regularity template for induced C4

Paper: the lift `R'` in the proof of `lemma:c4-rough-struc`.
Exceptional vertices remain isolated green vertices in this partial
template. Inside each cluster the reduced vertex color is promoted to an
edge color; regular intercluster pairs inherit the reduced edge color.
-/

noncomputable section
open Finset InducedStars.Regularity InducedStars.Regularity.RegularityColoredGraph
open scoped Classical
namespace InducedStars

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {eta tau : ℝ}

def c4TypeClusterLabel (P : RegularPartition G eta) (hk : 0 < P.clusterCount)
    (v : Fin n) : Fin P.clusterCount := P.alignmentLabel (v, ⟨0, hk⟩)

theorem c4TypeClusterLabel_of_mem (P : RegularPartition G eta) (hk : 0 < P.clusterCount)
    {i : Fin P.clusterCount} {v : Fin n} (hv : v ∈ P.clusters i) :
    c4TypeClusterLabel P hk v = i := P.alignmentLabel_of_mem_cluster i hv _

theorem c4TypeClusterLabel_mem (P : RegularPartition G eta) (hk : 0 < P.clusterCount)
    {v : Fin n} (hv : v ∉ P.exceptional) :
    v ∈ P.clusters (c4TypeClusterLabel P hk v) := P.mem_cluster_alignmentLabel hv _

def c4LiftedType (T : RegularityType G eta tau 4) (hk : 0 < T.partition.clusterCount) :
    RegularityColoredGraph (Fin n) :=
  DenseGraph.coloredBlowUp T.coloredGraph (c4TypeClusterLabel T.partition hk)
    {v | v ∉ T.partition.exceptional}

theorem c4LiftedType_no_coloredHom (T : RegularityType G eta tau 4)
    (hk : 0 < T.partition.clusterCount) (hfree : ¬InducedEmbeds inducedC4 G) :
    ¬ColoredHomExists inducedC4 (c4LiftedType T hk) := by
  intro h
  apply hfree
  apply T.inducedEmbedding 4 le_rfl inducedC4
  exact DenseGraph.coloredHomExists_project_blowUp _ _ _ _
    (by intro x; fin_cases x <;> first
      | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩) h

@[simp] theorem c4LiftedType_adj (T : RegularityType G eta tau 4)
    (hk : 0 < T.partition.clusterCount) (x y : Fin n) :
    (c4LiftedType T hk).graph.Adj x y ↔
      x ≠ y ∧ x ∉ T.partition.exceptional ∧ y ∉ T.partition.exceptional ∧
        (c4TypeClusterLabel T.partition hk x = c4TypeClusterLabel T.partition hk y ∨
          T.coloredGraph.graph.Adj (c4TypeClusterLabel T.partition hk x)
            (c4TypeClusterLabel T.partition hk y)) := Iff.rfl

def c4LiftedMissingPairCover (P : RegularPartition G eta) : Finset (Fin n × Fin n) :=
  (P.exceptional ×ˢ univ) ∪ (univ ×ˢ P.exceptional) ∪
    (orderedIrregularPairs eta P).biUnion (fun ij ↦ P.clusters ij.1 ×ˢ P.clusters ij.2)

theorem c4LiftedMissing_edges_subset (T : RegularityType G eta tau 4)
    (hk : 0 < T.partition.clusterCount) :
    finiteGraphEdges (c4LiftedType T hk).graphᶜ ⊆
      (c4LiftedMissingPairCover T.partition).image Sym2.mk.uncurry := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have h := (mk_mem_finiteGraphEdges _ _ _).mp he
    have hne : x ≠ y := h.1
    have hnon : ¬(c4LiftedType T hk).graph.Adj x y := h.2
    apply mem_image.mpr
    refine ⟨(x,y), ?_, rfl⟩
    unfold c4LiftedMissingPairCover
    by_cases hx : x ∈ T.partition.exceptional
    · exact mem_union_left _ (mem_union_left _ (mem_product.mpr ⟨hx, mem_univ _⟩))
    by_cases hy : y ∈ T.partition.exceptional
    · exact mem_union_left _ (mem_union_right _ (mem_product.mpr ⟨mem_univ _, hy⟩))
    apply mem_union_right
    apply mem_biUnion.mpr
    let i := c4TypeClusterLabel T.partition hk x
    let j := c4TypeClusterLabel T.partition hk y
    have hij : i ≠ j := fun hh ↦ hnon ((c4LiftedType_adj T hk x y).mpr
      ⟨hne, hx, hy, Or.inl hh⟩)
    have hirr : ¬IsRegularPair G eta (T.partition.clusters i) (T.partition.clusters j) := by
      intro hr
      apply hnon
      exact (c4LiftedType_adj T hk x y).mpr ⟨hne, hx, hy, Or.inr
        ((T.partition.regularPairGraph_adj i j).mpr ⟨hij, hr⟩)⟩
    refine ⟨(i,j), ?_, mem_product.mpr
      ⟨c4TypeClusterLabel_mem _ hk hx, c4TypeClusterLabel_mem _ hk hy⟩⟩
    simp [orderedIrregularPairs, hij, hirr]

theorem c4LiftedMissingPairCover_card_le (P : RegularPartition G eta) :
    (c4LiftedMissingPairCover P).card ≤ 2 * P.exceptional.card * n +
      2 * (irregularPairs G eta P.clusters).card * P.clusterSize^2 := by
  have hU : ((orderedIrregularPairs eta P).biUnion
      (fun ij ↦ P.clusters ij.1 ×ˢ P.clusters ij.2)).card ≤
      (orderedIrregularPairs eta P).card * P.clusterSize^2 := by
    calc
      _ ≤ ∑ ij ∈ orderedIrregularPairs eta P,
          (P.clusters ij.1 ×ˢ P.clusters ij.2).card := card_biUnion_le
      _ = _ := by simp [card_product, P.cluster_card_eq, pow_two]
  have hI := Nat.mul_le_mul_right (P.clusterSize^2) (card_orderedIrregularPairs_le P)
  have h1 := card_union_le (P.exceptional ×ˢ (univ : Finset (Fin n)))
    ((univ : Finset (Fin n)) ×ˢ P.exceptional)
  have h2 := card_union_le ((P.exceptional ×ˢ (univ : Finset (Fin n))) ∪
      ((univ : Finset (Fin n)) ×ˢ P.exceptional))
    ((orderedIrregularPairs eta P).biUnion (fun ij ↦ P.clusters ij.1 ×ˢ P.clusters ij.2))
  simp only [card_product, card_univ, Fintype.card_fin] at h1
  change _ ≤ _
  unfold c4LiftedMissingPairCover
  nlinarith

/-- The factor three is a harmless uniform allowance obtained without
dividing the ordered irregular-pair bound by two. -/
theorem c4LiftedType_missing_le (T : RegularityType G eta tau 4)
    (hk : 0 < T.partition.clusterCount) :
    ((finiteGraphEdges (c4LiftedType T hk).graphᶜ).card : ℝ) ≤ 3*eta*(n : ℝ)^2 := by
  let P := T.partition
  have hcard := (card_le_card (c4LiftedMissing_edges_subset T hk)).trans
    ((card_image_le).trans (c4LiftedMissingPairCover_card_le P))
  have hcardR : ((finiteGraphEdges (c4LiftedType T hk).graphᶜ).card : ℝ) ≤
      2*(P.exceptional.card : ℝ)*n +
        2*((irregularPairs G eta P.clusters).card : ℝ)*(P.clusterSize : ℝ)^2 := by
    exact_mod_cast hcard
  have hcover := P.exceptional_card_add_mul_clusterSize_eq
  have hcoverR : (P.clusterCount : ℝ)*P.clusterSize ≤ n := by exact_mod_cast (by omega :
    P.clusterCount*P.clusterSize ≤ n)
  have hsq : (P.clusterCount : ℝ)^2*(P.clusterSize : ℝ)^2 ≤ (n : ℝ)^2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hcoverR 2
  have hirr := P.irregular_pair_card_le
  have hchoose : (2 : ℝ)*(Nat.choose P.clusterCount 2 : ℝ) ≤ (P.clusterCount : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    nlinarith [Nat.cast_nonneg (α := ℝ) P.clusterCount]
  have hprod := mul_le_mul_of_nonneg_right hirr (sq_nonneg (P.clusterSize : ℝ))
  have hchooseprod := mul_le_mul_of_nonneg_right hchoose (sq_nonneg (P.clusterSize : ℝ))
  have hscale := mul_le_mul_of_nonneg_left hchooseprod T.epsilon_pos.le
  have hs := mul_le_mul_of_nonneg_left hsq T.epsilon_pos.le
  have hE : (P.exceptional.card : ℝ) ≤ eta*n := by
    simpa using P.exceptional_card_le
  have hEn := mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg (α := ℝ) n)
  nlinarith

end InducedStars
