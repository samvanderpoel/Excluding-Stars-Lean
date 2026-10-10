import InducedStars.Graphon.Approximation
import InducedStars.Graphon.CellRelabeling
import InducedStars.Graphon.ColorProfile
import InducedStars.Graphon.ExtremalBlockModel
import InducedStars.Graphon.LabeledPartitionRelabeling
import InducedStars.Graphon.ProfileBlocks
import InducedStars.Graphon.RelabelingValueMass
import InducedStars.EdgeColoring.Stability
import Mathlib.Tactic

/-!
# Coordinate-safe finite block equalization

This file contains the finite common-refinement estimates used to compare an
exact extremal coloring with its equalized block model.  The comparison keeps
the original finite coordinates until an explicit equal-cell relabeling is
introduced in the proof of `prop:graphon-char-fixed-gamma`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

open ColoredGraph

/-- A stable adjacency decision for finite graphs used by this module. -/
local instance blockEqualizationFiniteAdjDecidable {n : ℕ}
    (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

/-! ## Uniformly refined finite sets and permutations -/

/-- Replace every vertex in `S ⊆ Fin q` by its `P` consecutive fine cells. -/
def uniformRefinementFinset {q : ℕ} (P : ℕ) (S : Finset (Fin q)) :
    Finset (Fin (q * P)) :=
  (S.product (Finset.univ : Finset (Fin P))).map
    (typeFineCellEquiv q P).toEmbedding

@[simp] theorem mem_uniformRefinementFinset {q P : ℕ}
    (S : Finset (Fin q)) (x : Fin (q * P)) :
    x ∈ uniformRefinementFinset P S ↔
      ((typeFineCellEquiv q P).symm x).1 ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    simpa using (Finset.mem_product.mp hy).1
  · intro hx
    let y := (typeFineCellEquiv q P).symm x
    have hy : y ∈ S.product (Finset.univ : Finset (Fin P)) := by
      exact Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩
    refine Finset.mem_map.mpr ⟨y, hy, ?_⟩
    exact (typeFineCellEquiv q P).apply_symm_apply x

@[simp] theorem card_uniformRefinementFinset {q : ℕ} (P : ℕ)
    (S : Finset (Fin q)) :
    (uniformRefinementFinset P S).card = S.card * P := by
  simp [uniformRefinementFinset]

theorem uniformRefinementFinset_nonempty {q P : ℕ} {S : Finset (Fin q)}
    (hS : S.Nonempty) (hP : 0 < P) :
    (uniformRefinementFinset P S).Nonempty := by
  obtain ⟨x, hx⟩ := hS
  let a : Fin P := ⟨0, hP⟩
  refine ⟨typeFineCellEquiv q P (x, a), ?_⟩
  simp [hx]

theorem uniformRefinementFinset_mono {q P : ℕ} {S T : Finset (Fin q)}
    (hST : S ⊆ T) :
    uniformRefinementFinset P S ⊆ uniformRefinementFinset P T := by
  intro x hx
  rw [mem_uniformRefinementFinset] at hx ⊢
  exact hST hx

theorem disjoint_uniformRefinementFinset {q P : ℕ}
    {S T : Finset (Fin q)} (hST : Disjoint S T) :
    Disjoint (uniformRefinementFinset P S)
      (uniformRefinementFinset P T) := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  rw [mem_uniformRefinementFinset] at hxS hxT
  exact Finset.disjoint_left.mp hST hxS hxT

@[simp] theorem uniformRefinementFinset_union {q P : ℕ}
    (S T : Finset (Fin q)) :
    uniformRefinementFinset P (S ∪ T) =
      uniformRefinementFinset P S ∪ uniformRefinementFinset P T := by
  ext x
  simp only [mem_uniformRefinementFinset, Finset.mem_union]

@[simp] theorem uniformRefinementFinset_univ {q P : ℕ} :
    uniformRefinementFinset P (Finset.univ : Finset (Fin q)) =
      (Finset.univ : Finset (Fin (q * P))) := by
  ext x
  simp

/-- Uniform refinement commutes with the union of a finite labeled family. -/
theorem uniformRefinementFinset_clusterUnion
    {q P : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (parts : I → Finset (Fin q)) :
    uniformRefinementFinset P (clusterUnion parts) =
      clusterUnion (fun i ↦ uniformRefinementFinset P (parts i)) := by
  ext x
  simp only [mem_uniformRefinementFinset, mem_clusterUnion_iff]

/-- An equitable natural-valued family whose total is exactly a multiple of
its number of labels is constant. -/
theorem equitable_eq_of_sum_eq_mul {q t : ℕ} (hq : 0 < q)
    (f : Fin q → ℕ)
    (hequitable : Set.EquitableOn (Set.univ : Set (Fin q)) f)
    (hsum : ∑ i, f i = q * t) :
    ∀ i, f i = t := by
  intro i
  have havg : (∑ j : Fin q, f j) / q = t := by
    rw [hsum]
    simpa [Nat.mul_comm] using Nat.mul_div_left t hq
  have hlower (j : Fin q) : t ≤ f j := by
    have hequitable' :
        Set.EquitableOn ((Finset.univ : Finset (Fin q)) : Set (Fin q)) f := by
      simpa using hequitable
    have h := Finset.EquitableOn.le hequitable'
      (Finset.mem_univ j)
    simpa [havg] using h
  have herase :
      (Finset.univ.erase i).card * t ≤
        ∑ j ∈ (Finset.univ.erase i : Finset (Fin q)), f j := by
    calc
      (Finset.univ.erase i).card * t =
          ∑ _j ∈ (Finset.univ.erase i : Finset (Fin q)), t := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ ↦ hlower j
  have hcard : (Finset.univ.erase i : Finset (Fin q)).card = q - 1 := by
    simp
  have hdecomp :
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin q)), f j) + f i =
        ∑ j : Fin q, f j :=
    Finset.sum_erase_add _ _ (Finset.mem_univ i)
  rw [hcard] at herase
  have hupper : (q - 1) * t + f i ≤ q * t := by omega
  have hmul : q * t = (q - 1) * t + t := by
    have hqsplit : q = (q - 1) + 1 := by omega
    calc
      q * t = ((q - 1) + 1) * t := congrArg (fun n ↦ n * t) hqsplit
      _ = (q - 1) * t + t := by rw [add_mul, one_mul]
  apply Nat.le_antisymm
  · have hfi : (q - 1) * t + f i ≤ (q - 1) * t + t := by
      calc
      (q - 1) * t + f i ≤ q * t := hupper
      _ = (q - 1) * t + t := hmul
    exact Nat.le_of_add_le_add_left hfi
  · exact hlower i

/-- In a nonempty equitable partition, every part has size at most twice
the floor average. -/
theorem equitable_part_card_le_two_mul_div
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 0 < q) (parts : Fin q → Finset V)
    (hnonempty : ∀ i, (parts i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin q)) parts)
    (hequitable : Set.EquitableOn (Set.univ : Set (Fin q))
      (fun i ↦ (parts i).card)) (i : Fin q) :
    (parts i).card ≤ 2 * ((clusterUnion parts).card / q) := by
  have hsum : ∑ j : Fin q, (parts j).card = (clusterUnion parts).card :=
    (card_clusterUnion parts hdisj).symm
  have hqle : q ≤ (clusterUnion parts).card := by
    rw [← hsum]
    calc
      q = ∑ _j : Fin q, 1 := by simp
      _ ≤ ∑ j : Fin q, (parts j).card := by
        exact Finset.sum_le_sum fun j _ ↦
          Finset.card_pos.mpr (hnonempty j)
  have havgPos : 0 < (clusterUnion parts).card / q :=
    Nat.div_pos hqle hq
  have hequitable' :
      Set.EquitableOn ((Finset.univ : Finset (Fin q)) : Set (Fin q))
        (fun j ↦ (parts j).card) := by
    simpa using hequitable
  have hi := Finset.EquitableOn.le_add_one hequitable'
    (Finset.mem_univ i)
  simp only [Finset.sum_filter, Finset.filter_true_of_mem,
    Finset.card_univ, Fintype.card_fin, hsum] at hi
  omega

/-- Refine every cell uniformly and then rebalance.  If the number of new
copies is divisible by the number of labels, the balanced cells have exactly
equal size.  At most `ℓ * P` fine cells change label. -/
theorem exists_equalRepartition_uniformRefinement
    {q ℓ P : ℕ} (hℓ : 0 < ℓ) (hP : 0 < P) (hdiv : ℓ ∣ P)
    (parts : Fin ℓ → Finset (Fin q))
    (hnonempty : ∀ i, (parts i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin ℓ)) parts)
    (hequitable : ∀ i j, (parts i).card ≤ (parts j).card + 1) :
    ∃ balanced : Fin ℓ → Finset (Fin (q * P)),
      (∀ i, (balanced i).Nonempty) ∧
      Set.PairwiseDisjoint (Set.univ : Set (Fin ℓ)) balanced ∧
      clusterUnion balanced =
        uniformRefinementFinset P (clusterUnion parts) ∧
      (∀ i, (balanced i).card =
        (clusterUnion parts).card * (P / ℓ)) ∧
      (clusterMovedSet
        (fun i ↦ uniformRefinementFinset P (parts i)) balanced).card ≤ ℓ * P := by
  let refined : Fin ℓ → Finset (Fin (q * P)) :=
    fun i ↦ uniformRefinementFinset P (parts i)
  have hrefNonempty (i : Fin ℓ) : (refined i).Nonempty := by
    exact uniformRefinementFinset_nonempty (hnonempty i) hP
  have hrefDisj :
      Set.PairwiseDisjoint (Set.univ : Set (Fin ℓ)) refined := by
    intro i _ j _ hij
    exact disjoint_uniformRefinementFinset
      (hdisj (Set.mem_univ i) (Set.mem_univ j) hij)
  have hrefClose (i j : Fin ℓ) :
      Nat.dist (refined i).card (refined j).card ≤ P := by
    have hd : Nat.dist (parts i).card (parts j).card ≤ 1 := by
      have hij := hequitable i j
      have hji := hequitable j i
      unfold Nat.dist
      omega
    simp only [refined, card_uniformRefinementFinset, Nat.dist_mul_right]
    simpa using Nat.mul_le_mul_right P hd
  obtain ⟨balanced, hbalancedNonempty, hbalancedDisj, hbalancedUnion,
      hbalancedEquitable, hmoved⟩ :=
    exists_equitableRepartition hℓ refined hrefNonempty hrefDisj hrefClose
  have hrefUnion : clusterUnion refined =
      uniformRefinementFinset P (clusterUnion parts) := by
    exact (uniformRefinementFinset_clusterUnion parts).symm
  have hsum :
      ∑ i : Fin ℓ, (balanced i).card =
        ℓ * ((clusterUnion parts).card * (P / ℓ)) := by
    calc
      ∑ i : Fin ℓ, (balanced i).card =
          (clusterUnion balanced).card :=
        (card_clusterUnion balanced hbalancedDisj).symm
      _ = (clusterUnion refined).card := by rw [hbalancedUnion]
      _ = (uniformRefinementFinset P (clusterUnion parts)).card := by
        rw [hrefUnion]
      _ = (clusterUnion parts).card * P := card_uniformRefinementFinset _ _
      _ = ℓ * ((clusterUnion parts).card * (P / ℓ)) := by
        have hfactor : ℓ * (P / ℓ) = P := Nat.mul_div_cancel' hdiv
        calc
          (clusterUnion parts).card * P =
              (clusterUnion parts).card * (ℓ * (P / ℓ)) := by
            rw [hfactor]
          _ = ℓ * ((clusterUnion parts).card * (P / ℓ)) := by
            ac_rfl
  have hbalancedCard : ∀ i, (balanced i).card =
      (clusterUnion parts).card * (P / ℓ) :=
    equitable_eq_of_sum_eq_mul hℓ
      (fun i ↦ (balanced i).card) hbalancedEquitable hsum
  refine ⟨balanced, hbalancedNonempty, hbalancedDisj, ?_, hbalancedCard, ?_⟩
  · exact hbalancedUnion.trans hrefUnion
  · simpa only [clusterMovedSet] using hmoved

/-! ## Common refinement and balanced core clusters -/

namespace FiniteExtremalBlockModel

variable {k q : ℕ} {C : ColoredGraph (Fin q)}
    (M : FiniteExtremalBlockModel k q C)

theorem profileXiMatrix_transport {A B : RegularBlockCore k}
    (p : ℝ) (h : A = B) (i j : Fin A.order) :
    profileXiMatrix p B
        (Fin.cast (congrArg RegularBlockCore.order h) i)
        (Fin.cast (congrArg RegularBlockCore.order h) j) =
      profileXiMatrix p A i j := by
  subst B
  rfl

/-- Product of all active reduced-core orders.  Every active order divides
this common refinement factor. -/
def refinementFactor : ℕ :=
  ∏ a : Fin M.componentCount, M.orderedCoreOrder a

theorem refinementFactor_pos : 0 < M.refinementFactor := by
  unfold refinementFactor
  exact Finset.prod_pos fun a _ ↦ (M.orderedCore a).order_pos

theorem orderedCoreOrder_dvd_refinementFactor
    (a : Fin M.componentCount) :
    M.orderedCoreOrder a ∣ M.refinementFactor := by
  unfold refinementFactor
  exact Finset.dvd_prod_of_mem (fun b : Fin M.componentCount ↦
    M.orderedCoreOrder b) (Finset.mem_univ a)

/-- Total number of fine cells in the common refinement. -/
def refinementOrder : ℕ := q * M.refinementFactor

theorem refinementOrder_pos : 0 < M.refinementOrder :=
  Nat.mul_pos M.ambientOrder_pos M.refinementFactor_pos

/-- Literal ambient cluster at an ordered component position. -/
def orderedAmbientCluster (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) : Finset (Fin q) :=
  M.witness.ambientCoreCluster (M.orderedIndex a) i

theorem orderedAmbientCluster_nonempty (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) :
    (M.orderedAmbientCluster a i).Nonempty :=
  M.witness.ambientCoreCluster_nonempty (M.orderedIndex a) i

theorem orderedAmbientCluster_pairwiseDisjoint
    (a : Fin M.componentCount) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (M.orderedCore a).order))
      (M.orderedAmbientCluster a) :=
  M.witness.ambientCoreClusters_pairwiseDisjoint (M.orderedIndex a)

theorem orderedAmbientCluster_equitable (a : Fin M.componentCount)
    (i j : Fin (M.orderedCore a).order) :
    (M.orderedAmbientCluster a i).card ≤
      (M.orderedAmbientCluster a j).card + 1 :=
  M.witness.ambientCoreCluster_equitable (M.orderedIndex a) i j

theorem orderedAmbientCluster_cover (a : Fin M.componentCount) :
    clusterUnion (M.orderedAmbientCluster a) =
      M.witness.coreVertices (M.orderedIndex a) :=
  M.witness.ambientCoreClusters_cover (M.orderedIndex a)

/-- The literal ordered clusters after uniform fine-cell refinement. -/
def refinedCoreCluster (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) :
    Finset (Fin M.refinementOrder) :=
  uniformRefinementFinset M.refinementFactor
    (M.orderedAmbientCluster a i)

@[simp] theorem card_refinedCoreCluster (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) :
    (M.refinedCoreCluster a i).card =
      (M.orderedAmbientCluster a i).card * M.refinementFactor := by
  unfold refinedCoreCluster refinementOrder
  exact card_uniformRefinementFinset _ _

theorem clusterUnion_refinedCoreCluster (a : Fin M.componentCount) :
    clusterUnion (M.refinedCoreCluster a) =
      uniformRefinementFinset M.refinementFactor
        (clusterUnion (M.orderedAmbientCluster a)) := by
  unfold refinedCoreCluster refinementOrder
  exact (uniformRefinementFinset_clusterUnion
    (P := M.refinementFactor) (M.orderedAmbientCluster a)).symm

/-- The data returned by exact equalization of one core's refined clusters. -/
structure BalancedCoreData (a : Fin M.componentCount) where
  cluster : Fin (M.orderedCore a).order →
    Finset (Fin M.refinementOrder)
  nonempty : ∀ i, (cluster i).Nonempty
  pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (M.orderedCore a).order))
      cluster
  union_eq : clusterUnion cluster =
    uniformRefinementFinset M.refinementFactor
      (clusterUnion (M.orderedAmbientCluster a))
  card_eq : ∀ i, (cluster i).card =
    (clusterUnion (M.orderedAmbientCluster a)).card *
      (M.refinementFactor / (M.orderedCore a).order)
  moved_card_le :
    (clusterMovedSet (M.refinedCoreCluster a) cluster).card ≤
      (M.orderedCore a).order * M.refinementFactor

/-- Exact equalization data for one active reduced core. -/
noncomputable def balancedCoreData (a : Fin M.componentCount) :
    M.BalancedCoreData a := by
  let hexists := exists_equalRepartition_uniformRefinement
      (M.orderedCore a).order_pos M.refinementFactor_pos
      (M.orderedCoreOrder_dvd_refinementFactor a)
      (M.orderedAmbientCluster a)
      (M.orderedAmbientCluster_nonempty a)
      (M.orderedAmbientCluster_pairwiseDisjoint a)
      (M.orderedAmbientCluster_equitable a)
  let balanced := Classical.choose hexists
  have hs := Classical.choose_spec hexists
  exact ⟨balanced, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

end FiniteExtremalBlockModel

/-! ## Almost-everywhere identification of aligned finite cell unions -/

/-- Union of the canonical equal cells indexed by a finite set. -/
def equalCellFinsetUnion {D : ℕ} (S : Finset (Fin D)) : Set UnitInterval :=
  ⋃ x : {x // x ∈ S}, equalCell (x : Fin D)

theorem measurableSet_equalCellFinsetUnion {D : ℕ}
    (S : Finset (Fin D)) : MeasurableSet (equalCellFinsetUnion S) := by
  unfold equalCellFinsetUnion
  exact MeasurableSet.iUnion fun x ↦
    measurableSet_equalCell (x : Fin D)

theorem pairwise_disjoint_equalCell_subtype {D : ℕ}
    (S : Finset (Fin D)) :
    Pairwise fun x y : {x // x ∈ S} ↦
      Disjoint (equalCell (x : Fin D)) (equalCell (y : Fin D)) := by
  intro x y hxy
  rw [Set.disjoint_left]
  intro z hzx hzy
  apply hxy
  apply Subtype.ext
  exact equalCell_eq_of_mem hzx hzy

theorem volumeReal_equalCellFinsetUnion {D : ℕ} (hD : 0 < D)
    (S : Finset (Fin D)) :
    (volume : Measure UnitInterval).real (equalCellFinsetUnion S) =
      (S.card : ℝ) / (D : ℝ) := by
  unfold equalCellFinsetUnion
  rw [measureReal_iUnion_fintype (μ := volume)
    (pairwise_disjoint_equalCell_subtype S)
    (fun x ↦ measurableSet_equalCell (x : Fin D))]
  simp only [Measure.real, volume_equalCell, ENNReal.toReal_ofReal
    (by positivity : 0 ≤ (1 : ℝ) / (D : ℝ)), Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
  simp [div_eq_mul_inv]

/-- Finite union of all reduced-vertex cells inside one block. -/
def AdmissibleBlockSequence.blockCellUnion {k : ℕ}
    (L : AdmissibleBlockSequence k) (i : ℕ) : Set UnitInterval :=
  ⋃ v : Fin (L.core i).order, L.blockCell i v

theorem AdmissibleBlockSequence.measurableSet_blockCellUnion {k : ℕ}
    (L : AdmissibleBlockSequence k) (i : ℕ) :
    MeasurableSet (L.blockCellUnion i) := by
  unfold AdmissibleBlockSequence.blockCellUnion
  exact MeasurableSet.iUnion fun v ↦ L.measurableSet_blockCell i v

theorem AdmissibleBlockSequence.blockCellUnion_subset_interval {k : ℕ}
    (L : AdmissibleBlockSequence k) (i : ℕ) :
    L.blockCellUnion i ⊆ L.blockInterval i := by
  intro x hx
  obtain ⟨v, hxv⟩ := Set.mem_iUnion.1 hx
  exact L.blockCell_subset_interval i v hxv

theorem AdmissibleBlockSequence.volumeReal_blockCell {k : ℕ}
    (L : AdmissibleBlockSequence k) (i : ℕ)
    (v : Fin (L.core i).order) :
    (volume : Measure UnitInterval).real (L.blockCell i v) =
      L.alpha i / (L.core i).order := by
  rw [Measure.real, L.volume_blockCell, ENNReal.toReal_ofReal]
  exact div_nonneg (L.alpha_nonneg i) (by positivity)

theorem AdmissibleBlockSequence.volumeReal_blockCellUnion {k : ℕ}
    (L : AdmissibleBlockSequence k) (i : ℕ) :
    (volume : Measure UnitInterval).real (L.blockCellUnion i) = L.alpha i := by
  unfold AdmissibleBlockSequence.blockCellUnion
  have hpair : Pairwise fun v w : Fin (L.core i).order ↦
      Disjoint (L.blockCell i v) (L.blockCell i w) := by
    intro v w hvw
    rw [Set.disjoint_left]
    intro x hxv hxw
    exact hvw (L.blockCell_vertex_eq_of_mem hxv hxw)
  rw [measureReal_iUnion_fintype hpair
    (fun v ↦ L.measurableSet_blockCell i v)]
  simp_rw [L.volumeReal_blockCell i]
  have horder : ((L.core i).order : ℝ) ≠ 0 := by
    exact_mod_cast (L.core i).order_pos.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change ((L.core i).order : ℝ) *
      (L.alpha i / (L.core i).order) = L.alpha i
  field_simp

theorem AdmissibleBlockSequence.volumeReal_blockInterval {k : ℕ}
    (L : AdmissibleBlockSequence k) (i : ℕ) :
    (volume : Measure UnitInterval).real (L.blockInterval i) = L.alpha i := by
  rw [Measure.real, L.volume_blockInterval, ENNReal.toReal_ofReal]
  exact L.alpha_nonneg i

/-- A block interval is covered by its reduced-vertex cells up to a null set. -/
theorem AdmissibleBlockSequence.blockCellUnion_ae_eq_blockInterval {k : ℕ}
    (L : AdmissibleBlockSequence k) (i : ℕ) :
    L.blockCellUnion i =ᵐ[volume] L.blockInterval i := by
  apply ae_eq_of_subset_of_measure_ge
    (L.blockCellUnion_subset_interval i)
  · have hreal : (volume : Measure UnitInterval).real (L.blockInterval i) =
        (volume : Measure UnitInterval).real (L.blockCellUnion i) := by
      rw [L.volumeReal_blockInterval, L.volumeReal_blockCellUnion]
    exact ((measureReal_eq_measureReal_iff).1 hreal).le
  · exact (L.measurableSet_blockCellUnion i).nullMeasurableSet
  · finiteness

theorem AdmissibleBlockSequence.blockInterval_eq_empty_of_alpha_eq_zero
    {k : ℕ} (L : AdmissibleBlockSequence k) (i : ℕ)
    (hi : L.alpha i = 0) : L.blockInterval i = ∅ := by
  ext x
  simp only [AdmissibleBlockSequence.blockInterval, Set.mem_Ico,
    Set.mem_empty_iff_false, iff_false]
  intro hx
  have hend : L.blockEndUI i = L.blockStartUI i := by
    apply Subtype.ext
    simp [AdmissibleBlockSequence.blockEndUI,
      AdmissibleBlockSequence.blockStartUI,
      AdmissibleBlockSequence.blockEnd, hi]
  rw [hend] at hx
  exact (not_lt_of_ge hx.1) hx.2

/-! ## Labels induced by a finite family of disjoint clusters -/

/-- The unique cluster label of a vertex, or `none` outside the cluster
union.  The uniqueness property is supplied separately by pairwise
disjointness. -/
noncomputable def clusterLabel
    {V I : Type*} [Fintype I] [DecidableEq V] [DecidableEq I]
    (parts : I → Finset V) (x : V) : Option I :=
  if h : ∃ i, x ∈ parts i then some (Classical.choose h) else none

theorem clusterLabel_eq_some_iff
    {V I : Type*} [Fintype I] [DecidableEq V] [DecidableEq I]
    (parts : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) parts)
    (x : V) (i : I) :
    clusterLabel parts x = some i ↔ x ∈ parts i := by
  classical
  unfold clusterLabel
  split_ifs with h
  · let j := Classical.choose h
    have hj : x ∈ parts j := Classical.choose_spec h
    constructor
    · intro heq
      have hji : j = i := Option.some.inj heq
      simpa only [hji] using hj
    · intro hi
      congr 1
      by_contra hji
      exact Finset.disjoint_left.mp
        (hdisj (Set.mem_univ j) (Set.mem_univ i) hji) hj hi
  · simp only [false_iff]
    exact fun hi ↦ h ⟨i, hi⟩

theorem clusterLabel_eq_none_iff
    {V I : Type*} [Fintype I] [DecidableEq V] [DecidableEq I]
    (parts : I → Finset V) (x : V) :
    clusterLabel parts x = none ↔ x ∉ clusterUnion parts := by
  classical
  unfold clusterLabel
  split_ifs with h
  · simp only [false_iff]
    rw [mem_clusterUnion_iff]
    exact not_not.mpr h
  · simp only [true_iff]
    simpa only [mem_clusterUnion_iff, not_exists] using h

/-- A vertex outside the moved set keeps its unique cluster label. -/
theorem clusterLabel_eq_of_not_mem_clusterMovedSet
    {V I : Type*} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I]
    (old new : I → Finset V)
    (hold : Set.PairwiseDisjoint (Set.univ : Set I) old)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new)
    {x : V} (hx : x ∉ clusterMovedSet old new) :
    clusterLabel old x = clusterLabel new x := by
  cases hlabel : clusterLabel old x with
  | none =>
      have hxOld : x ∉ clusterUnion old :=
        (clusterLabel_eq_none_iff old x).mp hlabel
      have hxNew : x ∉ clusterUnion new := by simpa only [← hunion] using hxOld
      exact ((clusterLabel_eq_none_iff new x).mpr hxNew).symm
  | some i =>
      have hxiOld : x ∈ old i :=
        (clusterLabel_eq_some_iff old hold x i).mp hlabel
      have hxiNew : x ∈ new i :=
        (mem_old_iff_mem_new_of_not_mem_clusterMovedSet
          old new hnew hunion hx i).mp hxiOld
      exact ((clusterLabel_eq_some_iff new hnew x i).mpr hxiNew).symm

/-! ## Sparse profile kernels on labeled finite cores -/

/-- Profile kernel on optional core labels; `none` represents vertices
outside the component. -/
def optionalProfileXiMatrix {k : ℕ} (p : ℝ) (R : RegularBlockCore k) :
    Option (Fin R.order) → Option (Fin R.order) → ℝ
  | some i, some j => profileXiMatrix p R i j
  | _, _ => 0

theorem optionalProfileXiMatrix_nonneg {k : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (R : RegularBlockCore k) (i j : Option (Fin R.order)) :
    0 ≤ optionalProfileXiMatrix p R i j := by
  cases i <;> cases j <;> simp [optionalProfileXiMatrix,
    profileXiMatrix_nonneg hp]

theorem optionalProfileXiMatrix_le_one {k : ℕ} {p : ℝ}
    (hp : p ≤ 1) (R : RegularBlockCore k) (i j : Option (Fin R.order)) :
    optionalProfileXiMatrix p R i j ≤ 1 := by
  cases i <;> cases j <;> simp [optionalProfileXiMatrix,
    profileXiMatrix_le_one hp]

theorem optionalProfileXiMatrix_isSymm {k : ℕ} (p : ℝ)
    (R : RegularBlockCore k) :
    Function.swap (optionalProfileXiMatrix p R) = optionalProfileXiMatrix p R := by
  funext i j
  cases i <;> cases j <;>
    simp [optionalProfileXiMatrix, Matrix.IsSymm.apply
      (profileXiMatrix_isSymm p R)]

/-- A core vertex together with its reduced neighbors. -/
noncomputable def closedNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun j ↦ j = i ∨ G.Adj i j

@[simp] theorem mem_closedNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (i j : V) :
    j ∈ closedNeighborFinset G i ↔ j = i ∨ G.Adj i j := by
  classical
  simp [closedNeighborFinset]

theorem card_closedNeighborFinset {n : ℕ}
    (G : SimpleGraph (Fin n)) (i : Fin n) :
    (closedNeighborFinset G i).card = G.degree i + 1 := by
  classical
  have hset : closedNeighborFinset G i = insert i (G.neighborFinset i) := by
    ext j
    simp [mem_closedNeighborFinset, SimpleGraph.mem_neighborFinset]
  rw [hset, Finset.card_insert_of_notMem]
  · rfl
  · exact G.notMem_neighborFinset_self i

theorem profileXiMatrix_eq_zero_of_not_mem_closedNeighbor
    {k : ℕ} (p : ℝ) (R : RegularBlockCore k)
    (i j : Fin R.order) (hj : j ∉ closedNeighborFinset R.graph i) :
    profileXiMatrix p R i j = 0 := by
  apply profileXiMatrix_apply_of_ne_of_not_adj
  · exact fun hij ↦ hj ((mem_closedNeighborFinset R.graph i j).2
      (Or.inl hij.symm))
  · exact fun hadj ↦ hj ((mem_closedNeighborFinset R.graph i j).2
      (Or.inr hadj))

/-- Two optional profile values differ by at most one. -/
theorem abs_optionalProfileXiMatrix_sub_le_one
    {k : ℕ} {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (R : RegularBlockCore k)
    (i j t : Option (Fin R.order)) :
    |optionalProfileXiMatrix p R i t -
      optionalProfileXiMatrix p R j t| ≤ 1 := by
  rw [abs_le]
  constructor <;>
    have hi0 := optionalProfileXiMatrix_nonneg hp.1 R i t <;>
    have hi1 := optionalProfileXiMatrix_le_one hp.2 R i t <;>
    have hj0 := optionalProfileXiMatrix_nonneg hp.1 R j t <;>
    have hj1 := optionalProfileXiMatrix_le_one hp.2 R j t <;>
    linarith

/-- Sparse row comparison for a regular core.  Only the union of the two
closed neighborhoods can contribute. -/
theorem sum_abs_optionalProfileXiMatrix_rows_le
    {k : ℕ} (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (R : RegularBlockCore k)
    {V : Type*} [Fintype V] [DecidableEq V]
    (parts : Fin R.order → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin R.order)) parts)
    {s : ℕ} (hcard : ∀ t, (parts t).card ≤ s)
    (i j : Fin R.order) :
    (∑ y : V,
        |optionalProfileXiMatrix p R (some i) (clusterLabel parts y) -
          optionalProfileXiMatrix p R (some j) (clusterLabel parts y)|) ≤
      ((2 * (k - 1) * s : ℕ) : ℝ) := by
  classical
  let T : Finset (Fin R.order) :=
    closedNeighborFinset R.graph i ∪ closedNeighborFinset R.graph j
  have hpoint (y : V) :
      |optionalProfileXiMatrix p R (some i) (clusterLabel parts y) -
          optionalProfileXiMatrix p R (some j) (clusterLabel parts y)| ≤
        ∑ t ∈ T, if y ∈ parts t then (1 : ℝ) else 0 := by
    cases hlabel : clusterLabel parts y with
    | none => simp [hlabel, optionalProfileXiMatrix]
    | some t =>
        have hyt : y ∈ parts t :=
          (clusterLabel_eq_some_iff parts hdisj y t).mp hlabel
        change
          |optionalProfileXiMatrix p R (some i) (some t) -
              optionalProfileXiMatrix p R (some j) (some t)| ≤
            ∑ u ∈ T, if y ∈ parts u then (1 : ℝ) else 0
        by_cases ht : t ∈ T
        · calc
            |optionalProfileXiMatrix p R (some i) (some t) -
                optionalProfileXiMatrix p R (some j) (some t)| ≤
                1 := abs_optionalProfileXiMatrix_sub_le_one hp R _ _ _
            _ ≤ ∑ u ∈ T, if y ∈ parts u then (1 : ℝ) else 0 := by
              calc
                (1 : ℝ) = if y ∈ parts t then 1 else 0 := by simp [hyt]
                _ ≤ ∑ u ∈ T,
                    if y ∈ parts u then (1 : ℝ) else 0 := by
                  apply Finset.single_le_sum (fun u _ ↦ by positivity) ht
        · have hti : t ∉ closedNeighborFinset R.graph i := by
            intro h
            exact ht (Finset.mem_union_left _ h)
          have htj : t ∉ closedNeighborFinset R.graph j := by
            intro h
            exact ht (Finset.mem_union_right _ h)
          have hzi := profileXiMatrix_eq_zero_of_not_mem_closedNeighbor
            p R i t hti
          have hzj := profileXiMatrix_eq_zero_of_not_mem_closedNeighbor
            p R j t htj
          simp only [optionalProfileXiMatrix, hzi, hzj, sub_self, abs_zero]
          positivity
  calc
    (∑ y : V,
        |optionalProfileXiMatrix p R (some i) (clusterLabel parts y) -
          optionalProfileXiMatrix p R (some j) (clusterLabel parts y)|) ≤
        ∑ y : V, ∑ t ∈ T,
          if y ∈ parts t then (1 : ℝ) else 0 :=
      Finset.sum_le_sum fun y _ ↦ hpoint y
    _ = ∑ t ∈ T, ((parts t).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      simp
    _ ≤ ∑ _t ∈ T, (s : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      exact_mod_cast hcard t
    _ = (T.card : ℝ) * s := by simp
    _ ≤ ((2 * (k - 1) : ℕ) : ℝ) * s := by
      gcongr
      exact_mod_cast (calc
        T.card ≤ (closedNeighborFinset R.graph i).card +
            (closedNeighborFinset R.graph j).card := by
              change (closedNeighborFinset R.graph i ∪
                  closedNeighborFinset R.graph j).card ≤ _
              exact Finset.card_union_le _ _
        _ = (k - 1) + (k - 1) := by
          rw [card_closedNeighborFinset, card_closedNeighborFinset,
            R.degree_eq, R.degree_eq]
          omega
        _ = 2 * (k - 1) := by omega)
    _ = ((2 * (k - 1) * s : ℕ) : ℝ) := by norm_num

/-- Change one coordinate at a time.  If every changed first-coordinate row
and changed second-coordinate column has absolute discrepancy at most `B`,
then changing the labels on `S` costs at most `2 |S| B` in the ordered matrix
sum.  This is the counting device that avoids the false rectangle-area
argument in the printed proof. -/
theorem sum_abs_twoCoordinateChange_le
    {V I : Type*} [Fintype V] [DecidableEq V]
    (K : I → I → ℝ) (old new : V → I) (S : Finset V)
    (hsame : ∀ x, x ∉ S → old x = new x)
    {B : ℝ} (_hB : 0 ≤ B)
    (hrow : ∀ x, x ∈ S →
      ∑ y : V, |K (old x) (old y) - K (new x) (old y)| ≤ B)
    (hcol : ∀ y, y ∈ S →
      ∑ x : V, |K (new x) (old y) - K (new x) (new y)| ≤ B) :
    (∑ x : V, ∑ y : V,
        |K (old x) (old y) - K (new x) (new y)|) ≤
      2 * (S.card : ℝ) * B := by
  have hfirst :
      (∑ x : V, ∑ y : V,
          |K (old x) (old y) - K (new x) (old y)|) ≤
        (S.card : ℝ) * B := by
    calc
      _ ≤ ∑ x : V, if x ∈ S then B else 0 := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : x ∈ S
        · simpa [hx] using hrow x hx
        · rw [hsame x hx]
          simp [hx]
      _ = (S.card : ℝ) * B := by simp
  have hsecond :
      (∑ y : V, ∑ x : V,
          |K (new x) (old y) - K (new x) (new y)|) ≤
        (S.card : ℝ) * B := by
    calc
      _ ≤ ∑ y : V, if y ∈ S then B else 0 := by
        apply Finset.sum_le_sum
        intro y _
        by_cases hy : y ∈ S
        · simpa [hy] using hcol y hy
        · rw [hsame y hy]
          simp [hy]
      _ = (S.card : ℝ) * B := by simp
  calc
    (∑ x : V, ∑ y : V,
        |K (old x) (old y) - K (new x) (new y)|) ≤
        ∑ x : V, ∑ y : V,
          (|K (old x) (old y) - K (new x) (old y)| +
            |K (new x) (old y) - K (new x) (new y)|) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact abs_sub_le _ _ _
    _ = (∑ x : V, ∑ y : V,
          |K (old x) (old y) - K (new x) (old y)|) +
        (∑ y : V, ∑ x : V,
          |K (new x) (old y) - K (new x) (new y)|) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
    _ ≤ (S.card : ℝ) * B + (S.card : ℝ) * B :=
      add_le_add hfirst hsecond
    _ = 2 * (S.card : ℝ) * B := by ring

/-- Matrix obtained by assigning optional cluster labels and evaluating the
profile core kernel on those labels. -/
noncomputable def clusterProfileMatrix
    {k : ℕ} (p : ℝ) (R : RegularBlockCore k)
    {V : Type*} [Fintype V] [DecidableEq V]
    (parts : Fin R.order → Finset V) : Matrix V V ℝ :=
  fun x y ↦ optionalProfileXiMatrix p R
    (clusterLabel parts x) (clusterLabel parts y)

theorem clusterProfileMatrix_isSymm
    {k : ℕ} (p : ℝ) (R : RegularBlockCore k)
    {V : Type*} [Fintype V] [DecidableEq V]
    (parts : Fin R.order → Finset V) :
    (clusterProfileMatrix p R parts).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro x y
  exact congrFun (congrFun (optionalProfileXiMatrix_isSymm p R)
    (clusterLabel parts x)) (clusterLabel parts y)

theorem clusterProfileMatrix_nonneg
    {k : ℕ} {p : ℝ} (hp : 0 ≤ p) (R : RegularBlockCore k)
    {V : Type*} [Fintype V] [DecidableEq V]
    (parts : Fin R.order → Finset V) (x y : V) :
    0 ≤ clusterProfileMatrix p R parts x y :=
  optionalProfileXiMatrix_nonneg hp R _ _

theorem clusterProfileMatrix_le_one
    {k : ℕ} {p : ℝ} (hp : p ≤ 1) (R : RegularBlockCore k)
    {V : Type*} [Fintype V] [DecidableEq V]
    (parts : Fin R.order → Finset V) (x y : V) :
    clusterProfileMatrix p R parts x y ≤ 1 :=
  optionalProfileXiMatrix_le_one hp R _ _

theorem clusterProfileMatrix_eq_zero_of_not_mem
    {k : ℕ} (p : ℝ) (R : RegularBlockCore k)
    {V : Type*} [Fintype V] [DecidableEq V]
    (parts : Fin R.order → Finset V) {x y : V}
    (hx : x ∉ clusterUnion parts) :
    clusterProfileMatrix p R parts x y = 0 := by
  have hlabel : clusterLabel parts x = none :=
    (clusterLabel_eq_none_iff parts x).2 hx
  simp [clusterProfileMatrix, hlabel, optionalProfileXiMatrix]

theorem clusterProfileMatrix_of_mem
    {k : ℕ} (p : ℝ) (R : RegularBlockCore k)
    {V : Type*} [Fintype V] [DecidableEq V]
    (parts : Fin R.order → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin R.order)) parts)
    {x y : V} {i j : Fin R.order}
    (hx : x ∈ parts i) (hy : y ∈ parts j) :
    clusterProfileMatrix p R parts x y = profileXiMatrix p R i j := by
  rw [clusterProfileMatrix,
    (clusterLabel_eq_some_iff parts hdisj x i).2 hx,
    (clusterLabel_eq_some_iff parts hdisj y j).2 hy]
  rfl

/-- Entrywise cost of changing one core's cluster partition.  The estimate
uses both old and new cluster-size bounds because the two-coordinate
telescoping argument uses old labels in its rows and new labels in its
columns. -/
theorem sum_abs_clusterProfileMatrix_change_le
    {k : ℕ} (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (R : RegularBlockCore k)
    {V : Type*} [Fintype V] [DecidableEq V]
    (old new : Fin R.order → Finset V)
    (hold : Set.PairwiseDisjoint (Set.univ : Set (Fin R.order)) old)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set (Fin R.order)) new)
    (hunion : clusterUnion old = clusterUnion new)
    {s : ℕ} (holdCard : ∀ i, (old i).card ≤ s)
    (hnewCard : ∀ i, (new i).card ≤ s) :
    (∑ x : V, ∑ y : V,
        |clusterProfileMatrix p R old x y -
          clusterProfileMatrix p R new x y|) ≤
      2 * ((clusterMovedSet old new).card : ℝ) *
        ((2 * (k - 1) * s : ℕ) : ℝ) := by
  classical
  let K := optionalProfileXiMatrix p R
  let oldLabel := clusterLabel old
  let newLabel := clusterLabel new
  let S := clusterMovedSet old new
  have hsame (x : V) (hx : x ∉ S) : oldLabel x = newLabel x := by
    exact clusterLabel_eq_of_not_mem_clusterMovedSet
      old new hold hnew hunion hx
  have hrow (x : V) (_hx : x ∈ S) :
      ∑ y : V, |K (oldLabel x) (oldLabel y) -
          K (newLabel x) (oldLabel y)| ≤
        ((2 * (k - 1) * s : ℕ) : ℝ) := by
    cases holdx : oldLabel x with
    | none =>
        have hxOld : x ∉ clusterUnion old :=
          (clusterLabel_eq_none_iff old x).mp holdx
        have hxNew : x ∉ clusterUnion new := by
          simpa only [← hunion] using hxOld
        have hnewx : newLabel x = none :=
          clusterLabel_eq_none_iff new x |>.mpr hxNew
        simp [oldLabel, newLabel, K, hnewx, optionalProfileXiMatrix]
        positivity
    | some i =>
        cases hnewx : newLabel x with
        | none =>
            have hxNew : x ∉ clusterUnion new :=
              (clusterLabel_eq_none_iff new x).mp hnewx
            have hxOld : x ∉ clusterUnion old := by
              simpa only [hunion] using hxNew
            exact False.elim (hxOld (mem_clusterUnion_iff.2
              ⟨i, (clusterLabel_eq_some_iff old hold x i).mp holdx⟩))
        | some j =>
            simpa only [K, oldLabel, newLabel, holdx, hnewx] using
              sum_abs_optionalProfileXiMatrix_rows_le
                hk hp R old hold holdCard i j
  have hcol (y : V) (_hy : y ∈ S) :
      ∑ x : V, |K (newLabel x) (oldLabel y) -
          K (newLabel x) (newLabel y)| ≤
        ((2 * (k - 1) * s : ℕ) : ℝ) := by
    cases holdy : oldLabel y with
    | none =>
        have hyOld : y ∉ clusterUnion old :=
          (clusterLabel_eq_none_iff old y).mp holdy
        have hyNew : y ∉ clusterUnion new := by
          simpa only [← hunion] using hyOld
        have hnewy : newLabel y = none :=
          clusterLabel_eq_none_iff new y |>.mpr hyNew
        simp [oldLabel, newLabel, K, hnewy, optionalProfileXiMatrix]
        positivity
    | some i =>
        cases hnewy : newLabel y with
        | none =>
            have hyNew : y ∉ clusterUnion new :=
              (clusterLabel_eq_none_iff new y).mp hnewy
            have hyOld : y ∉ clusterUnion old := by
              simpa only [hunion] using hyNew
            exact False.elim (hyOld (mem_clusterUnion_iff.2
              ⟨i, (clusterLabel_eq_some_iff old hold y i).mp holdy⟩))
        | some j =>
            have hsymm (a b : Option (Fin R.order)) : K a b = K b a := by
              exact (congrFun (congrFun
                (optionalProfileXiMatrix_isSymm p R) a) b).symm
            calc
              (∑ x : V, |K (newLabel x) (some i) -
                  K (newLabel x) (some j)|) =
                  ∑ x : V, |K (some i) (newLabel x) -
                    K (some j) (newLabel x)| := by
                    apply Finset.sum_congr rfl
                    intro x _
                    rw [hsymm (newLabel x) (some i),
                      hsymm (newLabel x) (some j)]
              _ ≤ ((2 * (k - 1) * s : ℕ) : ℝ) := by
                simpa only [K, oldLabel, newLabel, holdy, hnewy] using
                  sum_abs_optionalProfileXiMatrix_rows_le
                    hk hp R new hnew hnewCard i j
  simpa only [clusterProfileMatrix, K, oldLabel, newLabel, S] using
    sum_abs_twoCoordinateChange_le K oldLabel newLabel S
      hsame (by positivity) hrow hcol

/-! ## Quantitative equalization of the finite extremal cores -/

namespace FiniteExtremalBlockModel

variable {k q : ℕ} {C : ColoredGraph (Fin q)}
    (M : FiniteExtremalBlockModel k q C)

@[simp] theorem card_clusterUnion_orderedAmbientCluster
    (a : Fin M.componentCount) :
    (clusterUnion (M.orderedAmbientCluster a)).card =
      M.witness.orderedCoreSize a := by
  rw [M.orderedAmbientCluster_cover a]
  rfl

theorem refinedCoreCluster_card_le
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order) :
    (M.refinedCoreCluster a i).card ≤
      2 * M.witness.orderedCoreSize a *
        (M.refinementFactor / (M.orderedCore a).order) := by
  have hbase : (M.orderedAmbientCluster a i).card ≤
      2 * ((clusterUnion (M.orderedAmbientCluster a)).card /
        (M.orderedCore a).order) :=
    equitable_part_card_le_two_mul_div
      (M.orderedCore a).order_pos (M.orderedAmbientCluster a)
      (M.orderedAmbientCluster_nonempty a)
      (M.orderedAmbientCluster_pairwiseDisjoint a)
      (by
        intro u v _ _
        exact M.orderedAmbientCluster_equitable a u v) i
  let ℓ := (M.orderedCore a).order
  let κ := M.witness.orderedCoreSize a
  let P := M.refinementFactor
  let r := P / ℓ
  have hfactor : ℓ * r = P := by
    exact Nat.mul_div_cancel' (M.orderedCoreOrder_dvd_refinementFactor a)
  have hdivMul : (κ / ℓ) * ℓ ≤ κ := Nat.div_mul_le_self κ ℓ
  rw [M.card_refinedCoreCluster a i]
  change (M.orderedAmbientCluster a i).card * P ≤ 2 * κ * r
  rw [← hfactor]
  calc
    (M.orderedAmbientCluster a i).card * (ℓ * r) ≤
        (2 * (κ / ℓ)) * (ℓ * r) := by
      exact Nat.mul_le_mul_right _ (by simpa [κ] using hbase)
    _ = 2 * ((κ / ℓ) * ℓ) * r := by ring
    _ ≤ 2 * κ * r := by
      exact Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 hdivMul)

theorem balancedCoreCluster_card_le
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order) :
    ((M.balancedCoreData a).cluster i).card ≤
      2 * M.witness.orderedCoreSize a *
        (M.refinementFactor / (M.orderedCore a).order) := by
  rw [(M.balancedCoreData a).card_eq i,
    M.card_clusterUnion_orderedAmbientCluster a]
  let b := M.witness.orderedCoreSize a *
    (M.refinementFactor / (M.orderedCore a).order)
  have hb : b ≤ 2 * b := by omega
  simpa only [b, mul_assoc] using hb

/-- One component contributes at most
`8 (k-1) κ_a P²` to the ordered entrywise discrepancy. -/
theorem sum_abs_refinedCoreCluster_balancedCoreCluster_le
    (a : Fin M.componentCount) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
        |clusterProfileMatrix p (M.orderedCore a)
            (M.refinedCoreCluster a) x y -
          clusterProfileMatrix p (M.orderedCore a)
            (M.balancedCoreData a).cluster x y|) ≤
      ((8 * (k - 1) * M.witness.orderedCoreSize a *
        M.refinementFactor ^ 2 : ℕ) : ℝ) := by
  let ℓ := (M.orderedCore a).order
  let κ := M.witness.orderedCoreSize a
  let P := M.refinementFactor
  let s := 2 * κ * (P / ℓ)
  have holdDisj :
      Set.PairwiseDisjoint (Set.univ : Set (Fin ℓ))
        (M.refinedCoreCluster a) := by
    intro i _ j _ hij
    exact disjoint_uniformRefinementFinset
      (M.orderedAmbientCluster_pairwiseDisjoint a
        (Set.mem_univ i) (Set.mem_univ j) hij)
  have hunion : clusterUnion (M.refinedCoreCluster a) =
      clusterUnion (M.balancedCoreData a).cluster := by
    rw [(M.balancedCoreData a).union_eq]
    exact M.clusterUnion_refinedCoreCluster a
  have hraw := sum_abs_clusterProfileMatrix_change_le
    M.three_le_k hp (M.orderedCore a)
    (M.refinedCoreCluster a) (M.balancedCoreData a).cluster
    holdDisj (M.balancedCoreData a).pairwiseDisjoint hunion
    (s := s) (M.refinedCoreCluster_card_le a)
    (M.balancedCoreCluster_card_le a)
  calc
    (∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
        |clusterProfileMatrix p (M.orderedCore a)
            (M.refinedCoreCluster a) x y -
          clusterProfileMatrix p (M.orderedCore a)
            (M.balancedCoreData a).cluster x y|) ≤
        2 * (((clusterMovedSet (M.refinedCoreCluster a)
          (M.balancedCoreData a).cluster).card : ℕ) : ℝ) *
          ((2 * (k - 1) * s : ℕ) : ℝ) := hraw
    _ ≤ 2 * ((ℓ * P : ℕ) : ℝ) *
          ((2 * (k - 1) * s : ℕ) : ℝ) := by
      gcongr
      exact_mod_cast (M.balancedCoreData a).moved_card_le
    _ = ((8 * (k - 1) * κ * P ^ 2 : ℕ) : ℝ) := by
      have hfactor : ℓ * (P / ℓ) = P :=
        Nat.mul_div_cancel' (M.orderedCoreOrder_dvd_refinementFactor a)
      have hfactorR : (ℓ : ℝ) * (P / ℓ : ℕ) = P := by
        exact_mod_cast hfactor
      dsimp only [s]
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      calc
        2 * ((ℓ : ℝ) * P) *
            (2 * ((k - 1 : ℕ) : ℝ) *
              (2 * κ * (P / ℓ : ℕ))) =
            8 * ((k - 1 : ℕ) : ℝ) * κ * P *
              ((ℓ : ℝ) * (P / ℓ : ℕ)) := by
          ring
        _ = 8 * ((k - 1 : ℕ) : ℝ) * κ * P ^ 2 := by
          rw [hfactorR]
          ring

/-- Sum of the literal refined component matrices, still in the original
ambient vertex order. -/
noncomputable def refinedExtremalCoreMatrix (p : ℝ) :
    Matrix (Fin M.refinementOrder) (Fin M.refinementOrder) ℝ :=
  ∑ a : Fin M.componentCount,
    clusterProfileMatrix p (M.orderedCore a) (M.refinedCoreCluster a)

/-- Sum of the equalized component matrices. -/
noncomputable def balancedExtremalCoreMatrix (p : ℝ) :
    Matrix (Fin M.refinementOrder) (Fin M.refinementOrder) ℝ :=
  ∑ a : Fin M.componentCount,
    clusterProfileMatrix p (M.orderedCore a)
      (M.balancedCoreData a).cluster

theorem refinedExtremalCoreMatrix_isSymm (p : ℝ) :
    (M.refinedExtremalCoreMatrix p).IsSymm := by
  unfold refinedExtremalCoreMatrix
  rw [Matrix.IsSymm.ext_iff]
  intro x y
  simp_rw [Matrix.sum_apply, Matrix.IsSymm.apply
    (clusterProfileMatrix_isSymm p _ _)]

theorem balancedExtremalCoreMatrix_isSymm (p : ℝ) :
    (M.balancedExtremalCoreMatrix p).IsSymm := by
  unfold balancedExtremalCoreMatrix
  rw [Matrix.IsSymm.ext_iff]
  intro x y
  simp_rw [Matrix.sum_apply, Matrix.IsSymm.apply
    (clusterProfileMatrix_isSymm p _ _)]

/-- Ordered core supports remain pairwise disjoint. -/
theorem orderedCoreVertices_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin M.componentCount))
      (fun a ↦ M.witness.coreVertices (M.orderedIndex a)) := by
  intro a _ b _ hab
  apply M.witness.coreVertices_pairwiseDisjoint
      (Set.mem_univ (M.orderedIndex a)) (Set.mem_univ (M.orderedIndex b))
  intro hindex
  apply hab
  exact M.componentOrder.injective hindex

/-- Refined component supports are pairwise disjoint. -/
theorem refinedCoreSupports_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin M.componentCount))
      (fun a ↦ clusterUnion (M.refinedCoreCluster a)) := by
  intro a _ b _ hab
  change Disjoint (clusterUnion (M.refinedCoreCluster a))
    (clusterUnion (M.refinedCoreCluster b))
  rw [M.clusterUnion_refinedCoreCluster a,
    M.clusterUnion_refinedCoreCluster b,
    M.orderedAmbientCluster_cover a,
    M.orderedAmbientCluster_cover b]
  exact disjoint_uniformRefinementFinset
    (M.orderedCoreVertices_pairwiseDisjoint
      (Set.mem_univ a) (Set.mem_univ b) hab)

/-- Equalization preserves each component support, hence those supports also
remain pairwise disjoint. -/
theorem balancedCoreSupports_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin M.componentCount))
      (fun a ↦ clusterUnion (M.balancedCoreData a).cluster) := by
  intro a _ b _ hab
  change Disjoint (clusterUnion (M.balancedCoreData a).cluster)
    (clusterUnion (M.balancedCoreData b).cluster)
  rw [(M.balancedCoreData a).union_eq,
    (M.balancedCoreData b).union_eq,
    M.orderedAmbientCluster_cover a,
    M.orderedAmbientCluster_cover b]
  exact disjoint_uniformRefinementFinset
    (M.orderedCoreVertices_pairwiseDisjoint
      (Set.mem_univ a) (Set.mem_univ b) hab)

private theorem sum_componentProfileMatrix_nonneg
    {p : ℝ} (hp : 0 ≤ p)
    (parts : (a : Fin M.componentCount) →
      Fin (M.orderedCore a).order → Finset (Fin M.refinementOrder))
    (x y : Fin M.refinementOrder) :
    0 ≤ ∑ a : Fin M.componentCount,
      clusterProfileMatrix p (M.orderedCore a) (parts a) x y := by
  exact Finset.sum_nonneg fun a _ ↦
    clusterProfileMatrix_nonneg hp (M.orderedCore a) (parts a) x y

private theorem sum_componentProfileMatrix_le_one
    {p : ℝ} (hp : p ≤ 1)
    (parts : (a : Fin M.componentCount) →
      Fin (M.orderedCore a).order → Finset (Fin M.refinementOrder))
    (hsupport : Set.PairwiseDisjoint
      (Set.univ : Set (Fin M.componentCount))
      (fun a ↦ clusterUnion (parts a)))
    (x y : Fin M.refinementOrder) :
    (∑ a : Fin M.componentCount,
      clusterProfileMatrix p (M.orderedCore a) (parts a) x y) ≤ 1 := by
  classical
  by_cases hx : ∃ a : Fin M.componentCount, x ∈ clusterUnion (parts a)
  · obtain ⟨a, hxa⟩ := hx
    rw [Finset.sum_eq_single a]
    · exact clusterProfileMatrix_le_one hp
        (M.orderedCore a) (parts a) x y
    · intro b _ hba
      apply clusterProfileMatrix_eq_zero_of_not_mem
      intro hxb
      exact Finset.disjoint_left.mp
        (hsupport (Set.mem_univ a) (Set.mem_univ b) hba.symm) hxa hxb
    · simp
  · have hzero (a : Fin M.componentCount) :
        clusterProfileMatrix p (M.orderedCore a) (parts a) x y = 0 := by
      apply clusterProfileMatrix_eq_zero_of_not_mem
      exact fun hxa ↦ hx ⟨a, hxa⟩
    simp_rw [hzero]
    norm_num

theorem refinedExtremalCoreMatrix_nonneg {p : ℝ} (hp : 0 ≤ p) :
    ∀ x y, 0 ≤ M.refinedExtremalCoreMatrix p x y := by
  intro x y
  unfold refinedExtremalCoreMatrix
  rw [Matrix.sum_apply]
  exact M.sum_componentProfileMatrix_nonneg hp M.refinedCoreCluster x y

theorem refinedExtremalCoreMatrix_le_one {p : ℝ} (hp : p ≤ 1) :
    ∀ x y, M.refinedExtremalCoreMatrix p x y ≤ 1 := by
  intro x y
  unfold refinedExtremalCoreMatrix
  rw [Matrix.sum_apply]
  exact M.sum_componentProfileMatrix_le_one hp M.refinedCoreCluster
    M.refinedCoreSupports_pairwiseDisjoint x y

theorem balancedExtremalCoreMatrix_nonneg {p : ℝ} (hp : 0 ≤ p) :
    ∀ x y, 0 ≤ M.balancedExtremalCoreMatrix p x y := by
  intro x y
  unfold balancedExtremalCoreMatrix
  rw [Matrix.sum_apply]
  exact M.sum_componentProfileMatrix_nonneg hp
    (fun a ↦ (M.balancedCoreData a).cluster) x y

theorem balancedExtremalCoreMatrix_le_one {p : ℝ} (hp : p ≤ 1) :
    ∀ x y, M.balancedExtremalCoreMatrix p x y ≤ 1 := by
  intro x y
  unfold balancedExtremalCoreMatrix
  rw [Matrix.sum_apply]
  exact M.sum_componentProfileMatrix_le_one hp
    (fun a ↦ (M.balancedCoreData a).cluster)
    M.balancedCoreSupports_pairwiseDisjoint x y

/-- Coarse ambient vertex underneath a common-refinement cell. -/
def refinedCoarseVertex (x : Fin M.refinementOrder) : Fin q :=
  ((typeFineCellEquiv q M.refinementFactor).symm x).1

@[simp] theorem mem_refinedCoreCluster_iff
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order)
    (x : Fin M.refinementOrder) :
    x ∈ M.refinedCoreCluster a i ↔
      M.refinedCoarseVertex x ∈ M.orderedAmbientCluster a i := by
  unfold refinedCoreCluster refinedCoarseVertex refinementOrder
  convert (mem_uniformRefinementFinset
    (P := M.refinementFactor) (M.orderedAmbientCluster a i) x) using 1

theorem refinedCoarseVertex_mem_core_iff
    (a : Fin M.componentCount) (x : Fin M.refinementOrder) :
    x ∈ clusterUnion (M.refinedCoreCluster a) ↔
      M.refinedCoarseVertex x ∈
        M.witness.coreVertices (M.orderedIndex a) := by
  rw [M.clusterUnion_refinedCoreCluster a,
    M.orderedAmbientCluster_cover a]
  unfold refinedCoarseVertex refinementOrder
  convert (mem_uniformRefinementFinset
    (P := M.refinementFactor)
    (M.witness.coreVertices (M.orderedIndex a)) x) using 1

theorem exists_orderedIndex_mem_iff
    (x : Fin q) :
    (∃ a : Fin M.componentCount,
      x ∈ M.witness.coreVertices (M.orderedIndex a)) ↔
      x ∈ M.witness.coveredCoreVertices := by
  rw [M.witness.mem_coveredCoreVertices]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨M.orderedIndex a, ha⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := M.componentOrder.surjective b
    exact ⟨a, hb⟩

theorem not_exists_orderedIndex_mem_iff_uncovered
    (x : Fin q) :
    (¬ ∃ a : Fin M.componentCount,
      x ∈ M.witness.coreVertices (M.orderedIndex a)) ↔
      x ∈ M.witness.uncoveredVertices := by
  rw [M.witness.mem_uncoveredVertices]
  constructor
  · intro h b hb
    obtain ⟨a, rfl⟩ := M.componentOrder.surjective b
    exact h ⟨a, hb⟩
  · intro h hordered
    obtain ⟨a, ha⟩ := hordered
    exact h (M.orderedIndex a) ha

/-- Summing the componentwise estimates uses disjoint ambient support sizes,
so the total entrywise cost is at most `8 (k-1) q P²`. -/
theorem sum_abs_refinedExtremalCoreMatrix_balancedExtremalCoreMatrix_le
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
        |M.refinedExtremalCoreMatrix p x y -
          M.balancedExtremalCoreMatrix p x y|) ≤
      ((8 * (k - 1) * q * M.refinementFactor ^ 2 : ℕ) : ℝ) := by
  have hpoint (x y : Fin M.refinementOrder) :
      |M.refinedExtremalCoreMatrix p x y -
          M.balancedExtremalCoreMatrix p x y| ≤
        ∑ a : Fin M.componentCount,
          |clusterProfileMatrix p (M.orderedCore a)
              (M.refinedCoreCluster a) x y -
            clusterProfileMatrix p (M.orderedCore a)
              (M.balancedCoreData a).cluster x y| := by
    rw [refinedExtremalCoreMatrix, balancedExtremalCoreMatrix,
      Matrix.sum_apply, Matrix.sum_apply, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  calc
    (∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
        |M.refinedExtremalCoreMatrix p x y -
          M.balancedExtremalCoreMatrix p x y|) ≤
        ∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
          ∑ a : Fin M.componentCount,
            |clusterProfileMatrix p (M.orderedCore a)
                (M.refinedCoreCluster a) x y -
              clusterProfileMatrix p (M.orderedCore a)
                (M.balancedCoreData a).cluster x y| := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact hpoint x y
    _ = ∑ x : Fin M.refinementOrder,
          ∑ a : Fin M.componentCount, ∑ y : Fin M.refinementOrder,
            |clusterProfileMatrix p (M.orderedCore a)
                (M.refinedCoreCluster a) x y -
              clusterProfileMatrix p (M.orderedCore a)
                (M.balancedCoreData a).cluster x y| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ a : Fin M.componentCount,
          ∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
            |clusterProfileMatrix p (M.orderedCore a)
                (M.refinedCoreCluster a) x y -
              clusterProfileMatrix p (M.orderedCore a)
                (M.balancedCoreData a).cluster x y| := by
      rw [Finset.sum_comm]
    _ ≤ ∑ a : Fin M.componentCount,
          ((8 * (k - 1) * M.witness.orderedCoreSize a *
            M.refinementFactor ^ 2 : ℕ) : ℝ) := by
      exact Finset.sum_le_sum fun a _ ↦
        M.sum_abs_refinedCoreCluster_balancedCoreCluster_le a hp
    _ = ((8 * (k - 1) * M.refinementFactor ^ 2 : ℕ) : ℝ) *
          ∑ a : Fin M.componentCount,
            (M.witness.orderedCoreSize a : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ((8 * (k - 1) * M.refinementFactor ^ 2 : ℕ) : ℝ) * q := by
      gcongr
      change ∑ a : Fin M.witness.coreCount,
          (M.witness.orderedCoreSize a : ℝ) ≤ (q : ℝ)
      have hnat :
        ∑ a : Fin M.witness.coreCount, M.witness.orderedCoreSize a =
            ∑ a : Fin M.witness.coreCount,
              (M.witness.coreVertices a).card :=
          M.witness.sum_orderedCoreSize
      have hnat_le :
          ∑ a : Fin M.witness.coreCount, M.witness.orderedCoreSize a ≤ q := by
        rw [hnat]
        exact M.witness.sum_coreSize_le
      have hcast :
          ((∑ a : Fin M.witness.coreCount,
              M.witness.orderedCoreSize a : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hnat_le
      calc
        ∑ a : Fin M.witness.coreCount,
            (M.witness.orderedCoreSize a : ℝ) =
            ((∑ a : Fin M.witness.coreCount,
                M.witness.orderedCoreSize a : ℕ) : ℝ) := by
              simp only [Nat.cast_sum]
        _ ≤ (q : ℝ) := hcast
    _ = ((8 * (k - 1) * q * M.refinementFactor ^ 2 : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      ring

/-! ## Canonical common-grid cells -/

/-- Ordered component size, extended by zero beyond the active list. -/
def finiteOrderedCoreSize (i : ℕ) : ℕ :=
  if hi : i < M.componentCount then
    M.witness.orderedCoreSize ⟨i, hi⟩
  else 0

@[simp] theorem finiteOrderedCoreSize_of_lt {i : ℕ}
    (hi : i < M.componentCount) :
    M.finiteOrderedCoreSize i = M.witness.orderedCoreSize ⟨i, hi⟩ := by
  simp [finiteOrderedCoreSize, hi]

@[simp] theorem finiteOrderedCoreSize_of_le {i : ℕ}
    (hi : M.componentCount ≤ i) : M.finiteOrderedCoreSize i = 0 := by
  simp [finiteOrderedCoreSize, Nat.not_lt_of_ge hi]

/-- Number of coarse ambient vertices in components preceding `a`. -/
def orderedCorePrefixSize (a : ℕ) : ℕ :=
  ∑ b ∈ Finset.range a, M.finiteOrderedCoreSize b

theorem orderedCorePrefixSize_add (a : Fin M.componentCount) :
    M.orderedCorePrefixSize (a + 1) =
      M.orderedCorePrefixSize a + M.witness.orderedCoreSize a := by
  rw [orderedCorePrefixSize, Finset.sum_range_succ,
    M.finiteOrderedCoreSize_of_lt a.isLt]
  rfl

theorem orderedCorePrefixSize_add_le_q (a : Fin M.componentCount) :
    M.orderedCorePrefixSize a + M.witness.orderedCoreSize a ≤ q := by
  rw [← M.orderedCorePrefixSize_add a]
  have hrange : Finset.range (a.val + 1) ⊆
      Finset.range M.componentCount := Finset.range_mono (Nat.succ_le_iff.2 a.isLt)
  calc
    M.orderedCorePrefixSize (a + 1) ≤
        ∑ b ∈ Finset.range M.componentCount,
          M.finiteOrderedCoreSize b := by
      unfold orderedCorePrefixSize
      exact Finset.sum_le_sum_of_subset_of_nonneg hrange
        (fun _ _ _ ↦ Nat.zero_le _)
    _ = ∑ b : Fin M.componentCount,
          M.witness.orderedCoreSize b := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro b _
      rw [M.finiteOrderedCoreSize_of_lt b.isLt]
      congr 1
    _ = ∑ b : Fin M.componentCount,
          (M.witness.coreVertices b).card := M.witness.sum_orderedCoreSize
    _ ≤ q := M.witness.sum_coreSize_le

/-- Fine-grid size of one canonical core vertex-cell. -/
def canonicalCoreClusterSize (a : Fin M.componentCount) : ℕ :=
  M.witness.orderedCoreSize a *
    (M.refinementFactor / (M.orderedCore a).order)

/-- Fine-grid left endpoint of canonical core vertex-cell `i`. -/
def canonicalCoreClusterStart (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) : ℕ :=
  M.orderedCorePrefixSize a * M.refinementFactor +
    M.canonicalCoreClusterSize a * i

theorem canonicalCoreClusterEnd_le (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) :
    M.canonicalCoreClusterStart a i + M.canonicalCoreClusterSize a ≤
      M.refinementOrder := by
  let ℓ := (M.orderedCore a).order
  let κ := M.witness.orderedCoreSize a
  let P := M.refinementFactor
  have hfactor : ℓ * (P / ℓ) = P :=
    Nat.mul_div_cancel' (M.orderedCoreOrder_dvd_refinementFactor a)
  have hi : i.val + 1 ≤ ℓ := i.isLt
  have hcell : κ * (P / ℓ) * i.val + κ * (P / ℓ) ≤ κ * P := by
    calc
      κ * (P / ℓ) * i.val + κ * (P / ℓ) =
          κ * (P / ℓ) * (i.val + 1) := by ring
      _ ≤ κ * (P / ℓ) * ℓ := Nat.mul_le_mul_left _ hi
      _ = κ * P := by
        rw [Nat.mul_assoc, Nat.mul_comm (P / ℓ) ℓ, hfactor]
  have hprefix := M.orderedCorePrefixSize_add_le_q a
  unfold canonicalCoreClusterStart canonicalCoreClusterSize refinementOrder
  change M.orderedCorePrefixSize a * P +
      κ * (P / ℓ) * i.val + κ * (P / ℓ) ≤ q * P
  calc
    _ = M.orderedCorePrefixSize a * P +
        (κ * (P / ℓ) * i.val + κ * (P / ℓ)) := by
      rw [Nat.add_assoc]
    _ ≤ M.orderedCorePrefixSize a * P + κ * P :=
      Nat.add_le_add_left hcell _
    _ = (M.orderedCorePrefixSize a + κ) * P := by ring
    _ ≤ q * P := Nat.mul_le_mul_right P hprefix

/-- Embedding of a canonical component/vertex cell into the common grid. -/
def canonicalCoreClusterEmbedding (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) :
    Fin (M.canonicalCoreClusterSize a) ↪ Fin M.refinementOrder where
  toFun r := ⟨M.canonicalCoreClusterStart a i + r,
    lt_of_lt_of_le (Nat.add_lt_add_left r.isLt _)
      (M.canonicalCoreClusterEnd_le a i)⟩
  inj' := by
    intro r s hrs
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hrs)

/-- Canonical consecutive fine cells representing one reduced-core vertex. -/
def canonicalCoreCluster (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) : Finset (Fin M.refinementOrder) :=
  (Finset.univ : Finset (Fin (M.canonicalCoreClusterSize a))).map
    (M.canonicalCoreClusterEmbedding a i)

@[simp] theorem card_canonicalCoreCluster (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) :
    (M.canonicalCoreCluster a i).card = M.canonicalCoreClusterSize a := by
  simp [canonicalCoreCluster]

theorem mem_canonicalCoreCluster_iff (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) (x : Fin M.refinementOrder) :
    x ∈ M.canonicalCoreCluster a i ↔
      M.canonicalCoreClusterStart a i ≤ x.val ∧
        x.val < M.canonicalCoreClusterStart a i +
          M.canonicalCoreClusterSize a := by
  constructor
  · intro hx
    obtain ⟨r, _hr, hrx⟩ := Finset.mem_map.1 hx
    have hxval : x.val = M.canonicalCoreClusterStart a i + r.val := by
      have hval := congrArg Fin.val hrx
      change M.canonicalCoreClusterStart a i + r.val = x.val at hval
      exact hval.symm
    constructor
    · omega
    · omega
  · rintro ⟨hlo, hhi⟩
    let r : Fin (M.canonicalCoreClusterSize a) :=
      ⟨x.val - M.canonicalCoreClusterStart a i, by omega⟩
    apply Finset.mem_map.2
    refine ⟨r, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change M.canonicalCoreClusterStart a i +
      (x.val - M.canonicalCoreClusterStart a i) = x.val
    omega

theorem canonicalCoreClusterSize_pos (a : Fin M.componentCount) :
    0 < M.canonicalCoreClusterSize a := by
  have hκ : 0 < M.witness.orderedCoreSize a := by
    change 0 < (M.witness.coreVertices (M.orderedIndex a)).card
    have hcore := M.witness.coreSize_lower (M.orderedIndex a)
    have hkpos : 0 < k := lt_of_lt_of_le (by omega : 0 < 3) M.three_le_k
    exact hkpos.trans_le hcore
  have hquot : 0 < M.refinementFactor / (M.orderedCore a).order := by
    apply Nat.div_pos
    · exact Nat.le_of_dvd M.refinementFactor_pos
        (M.orderedCoreOrder_dvd_refinementFactor a)
    · exact (M.orderedCore a).order_pos
  exact Nat.mul_pos hκ hquot

theorem orderedCorePrefixSize_mono : Monotone M.orderedCorePrefixSize := by
  intro a b hab
  unfold orderedCorePrefixSize
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    (fun _ _ _ ↦ Nat.zero_le _)

theorem canonicalCoreClusterEnd_le_componentEnd
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order) :
    M.canonicalCoreClusterStart a i + M.canonicalCoreClusterSize a ≤
      (M.orderedCorePrefixSize a + M.witness.orderedCoreSize a) *
        M.refinementFactor := by
  let ℓ := (M.orderedCore a).order
  let κ := M.witness.orderedCoreSize a
  let P := M.refinementFactor
  have hfactor : ℓ * (P / ℓ) = P :=
    Nat.mul_div_cancel' (M.orderedCoreOrder_dvd_refinementFactor a)
  have hi : i.val + 1 ≤ ℓ := i.isLt
  have hcell : κ * (P / ℓ) * i.val + κ * (P / ℓ) ≤ κ * P := by
    calc
      κ * (P / ℓ) * i.val + κ * (P / ℓ) =
          κ * (P / ℓ) * (i.val + 1) := by ring
      _ ≤ κ * (P / ℓ) * ℓ := Nat.mul_le_mul_left _ hi
      _ = κ * P := by
        rw [Nat.mul_assoc, Nat.mul_comm (P / ℓ) ℓ, hfactor]
  unfold canonicalCoreClusterStart canonicalCoreClusterSize
  calc
    M.orderedCorePrefixSize a * P + κ * (P / ℓ) * i.val +
        κ * (P / ℓ) =
        M.orderedCorePrefixSize a * P +
          (κ * (P / ℓ) * i.val + κ * (P / ℓ)) := by
      rw [Nat.add_assoc]
    _ ≤ M.orderedCorePrefixSize a * P + κ * P :=
      Nat.add_le_add_left hcell _
    _ = (M.orderedCorePrefixSize a + κ) * P := by ring

theorem canonicalCoreClusterEnd_le_nextStart
    {a b : Fin M.componentCount} (hab : a < b)
    (i : Fin (M.orderedCore a).order)
    (j : Fin (M.orderedCore b).order) :
    M.canonicalCoreClusterStart a i + M.canonicalCoreClusterSize a ≤
      M.canonicalCoreClusterStart b j := by
  have hpref : M.orderedCorePrefixSize (a.val + 1) ≤
      M.orderedCorePrefixSize b.val :=
    M.orderedCorePrefixSize_mono (by omega)
  have hend := M.canonicalCoreClusterEnd_le_componentEnd a i
  have hprefixAdd := M.orderedCorePrefixSize_add a
  unfold canonicalCoreClusterStart
  calc
    _ ≤ (M.orderedCorePrefixSize a + M.witness.orderedCoreSize a) *
        M.refinementFactor := hend
    _ = M.orderedCorePrefixSize (a.val + 1) * M.refinementFactor := by
      rw [hprefixAdd]
    _ ≤ M.orderedCorePrefixSize b * M.refinementFactor :=
      Nat.mul_le_mul_right _ hpref
    _ ≤ M.orderedCorePrefixSize b * M.refinementFactor +
        M.canonicalCoreClusterSize b * j.val := Nat.le_add_right _ _

theorem canonicalCoreCluster_disjoint_same
    (a : Fin M.componentCount) {i j : Fin (M.orderedCore a).order}
    (hij : i ≠ j) :
    Disjoint (M.canonicalCoreCluster a i) (M.canonicalCoreCluster a j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  have hi := (M.mem_canonicalCoreCluster_iff a i x).1 hxi
  have hj := (M.mem_canonicalCoreCluster_iff a j x).1 hxj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hend : M.canonicalCoreClusterStart a i +
        M.canonicalCoreClusterSize a ≤ M.canonicalCoreClusterStart a j := by
      have hsucc : i.val + 1 ≤ j.val := Nat.succ_le_iff.2 hijlt
      have hmul := Nat.mul_le_mul_left (M.canonicalCoreClusterSize a) hsucc
      unfold canonicalCoreClusterStart
      calc
        M.orderedCorePrefixSize a * M.refinementFactor +
              M.canonicalCoreClusterSize a * i.val +
              M.canonicalCoreClusterSize a =
            M.orderedCorePrefixSize a * M.refinementFactor +
              M.canonicalCoreClusterSize a * (i.val + 1) := by ring
        _ ≤ M.orderedCorePrefixSize a * M.refinementFactor +
              M.canonicalCoreClusterSize a * j.val :=
          Nat.add_le_add_left hmul _
    omega
  · have hend : M.canonicalCoreClusterStart a j +
        M.canonicalCoreClusterSize a ≤ M.canonicalCoreClusterStart a i := by
      have hsucc : j.val + 1 ≤ i.val := Nat.succ_le_iff.2 hjilt
      have hmul := Nat.mul_le_mul_left (M.canonicalCoreClusterSize a) hsucc
      unfold canonicalCoreClusterStart
      calc
        M.orderedCorePrefixSize a * M.refinementFactor +
              M.canonicalCoreClusterSize a * j.val +
              M.canonicalCoreClusterSize a =
            M.orderedCorePrefixSize a * M.refinementFactor +
              M.canonicalCoreClusterSize a * (j.val + 1) := by ring
        _ ≤ M.orderedCorePrefixSize a * M.refinementFactor +
              M.canonicalCoreClusterSize a * i.val :=
          Nat.add_le_add_left hmul _
    omega

theorem canonicalCoreCluster_disjoint_of_lt
    {a b : Fin M.componentCount} (hab : a < b)
    (i : Fin (M.orderedCore a).order)
    (j : Fin (M.orderedCore b).order) :
    Disjoint (M.canonicalCoreCluster a i)
      (M.canonicalCoreCluster b j) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have hia := (M.mem_canonicalCoreCluster_iff a i x).1 hxa
  have hib := (M.mem_canonicalCoreCluster_iff b j x).1 hxb
  have hend := M.canonicalCoreClusterEnd_le_nextStart hab i j
  omega

/-- Dependent label type for all active reduced-core vertex-cells. -/
abbrev coreCellLabel : Type :=
  Σ a : Fin M.componentCount, Fin (M.orderedCore a).order

/-- Canonical consecutive fine-grid partition pieces for active core cells. -/
def canonicalCorePart (z : M.coreCellLabel) :
    Finset (Fin M.refinementOrder) :=
  M.canonicalCoreCluster z.1 z.2

theorem canonicalCorePart_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set M.coreCellLabel)
      M.canonicalCorePart := by
  rintro ⟨a, i⟩ _ ⟨b, j⟩ _ hab
  change Disjoint (M.canonicalCoreCluster a i)
    (M.canonicalCoreCluster b j)
  rcases lt_trichotomy a b with halt | heq | hbalt
  · exact M.canonicalCoreCluster_disjoint_of_lt halt i j
  · subst b
    apply M.canonicalCoreCluster_disjoint_same a
    intro hij
    apply hab
    exact Sigma.ext rfl (by simpa using hij)
  · exact (M.canonicalCoreCluster_disjoint_of_lt hbalt j i).symm

/-- Equalized finite pieces with the same dependent labels. -/
def balancedCorePart (z : M.coreCellLabel) :
    Finset (Fin M.refinementOrder) :=
  (M.balancedCoreData z.1).cluster z.2

theorem balancedCorePart_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set M.coreCellLabel)
      M.balancedCorePart := by
  rintro ⟨a, i⟩ _ ⟨b, j⟩ _ hab
  change Disjoint ((M.balancedCoreData a).cluster i)
    ((M.balancedCoreData b).cluster j)
  by_cases heq : a = b
  · subst b
    apply (M.balancedCoreData a).pairwiseDisjoint
        (Set.mem_univ i) (Set.mem_univ j)
    intro hij
    apply hab
    exact Sigma.ext rfl (by simpa using hij)
  · have hsupport := M.balancedCoreSupports_pairwiseDisjoint
        (Set.mem_univ a) (Set.mem_univ b) heq
    rw [Finset.disjoint_left]
    intro x hxi hxj
    exact Finset.disjoint_left.mp hsupport
      (mem_clusterUnion_iff.2 ⟨i, hxi⟩)
      (mem_clusterUnion_iff.2 ⟨j, hxj⟩)

/-- Canonical covered part of the fine grid. -/
def canonicalCoreUnion : Finset (Fin M.refinementOrder) :=
  clusterUnion M.canonicalCorePart

/-- Equalized covered part of the fine grid. -/
def balancedCoreUnion : Finset (Fin M.refinementOrder) :=
  clusterUnion M.balancedCorePart

/-- Canonical labeled partition, with `none` carrying the uncovered tail. -/
def canonicalLabeledPart : Option M.coreCellLabel →
    Finset (Fin M.refinementOrder)
  | some z => M.canonicalCorePart z
  | none => Finset.univ \ M.canonicalCoreUnion

/-- Equalized labeled partition, with `none` carrying its common complement. -/
def balancedLabeledPart : Option M.coreCellLabel →
    Finset (Fin M.refinementOrder)
  | some z => M.balancedCorePart z
  | none => Finset.univ \ M.balancedCoreUnion

theorem canonicalLabeledPart_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Option M.coreCellLabel))
      M.canonicalLabeledPart := by
  intro o _ r _ hor
  cases o with
  | none =>
      cases r with
      | none => exact (hor rfl).elim
      | some z =>
          change Disjoint (Finset.univ \ M.canonicalCoreUnion)
            (M.canonicalCorePart z)
          rw [Finset.disjoint_left]
          intro x hxTail hxz
          have hxNot := (Finset.mem_sdiff.1 hxTail).2
          exact hxNot (mem_clusterUnion_iff.2 ⟨z, hxz⟩)
  | some z =>
      cases r with
      | none =>
          change Disjoint (M.canonicalCorePart z)
            (Finset.univ \ M.canonicalCoreUnion)
          rw [Finset.disjoint_left]
          intro x hxz hxTail
          have hxNot := (Finset.mem_sdiff.1 hxTail).2
          exact hxNot (mem_clusterUnion_iff.2 ⟨z, hxz⟩)
      | some w =>
          exact M.canonicalCorePart_pairwiseDisjoint
            (Set.mem_univ z) (Set.mem_univ w)
            (fun hzw ↦ hor (congrArg some hzw))

theorem balancedLabeledPart_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Option M.coreCellLabel))
      M.balancedLabeledPart := by
  intro o _ r _ hor
  cases o with
  | none =>
      cases r with
      | none => exact (hor rfl).elim
      | some z =>
          change Disjoint (Finset.univ \ M.balancedCoreUnion)
            (M.balancedCorePart z)
          rw [Finset.disjoint_left]
          intro x hxTail hxz
          have hxNot := (Finset.mem_sdiff.1 hxTail).2
          exact hxNot (mem_clusterUnion_iff.2 ⟨z, hxz⟩)
  | some z =>
      cases r with
      | none =>
          change Disjoint (M.balancedCorePart z)
            (Finset.univ \ M.balancedCoreUnion)
          rw [Finset.disjoint_left]
          intro x hxz hxTail
          have hxNot := (Finset.mem_sdiff.1 hxTail).2
          exact hxNot (mem_clusterUnion_iff.2 ⟨z, hxz⟩)
      | some w =>
          exact M.balancedCorePart_pairwiseDisjoint
            (Set.mem_univ z) (Set.mem_univ w)
            (fun hzw ↦ hor (congrArg some hzw))

theorem canonicalLabeledPart_cover :
    clusterUnion M.canonicalLabeledPart = Finset.univ := by
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  intro x _
  by_cases hx : x ∈ M.canonicalCoreUnion
  · obtain ⟨z, hxz⟩ := mem_clusterUnion_iff.1 hx
    exact mem_clusterUnion_iff.2 ⟨some z, hxz⟩
  · exact mem_clusterUnion_iff.2 ⟨none,
      Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩⟩

theorem balancedLabeledPart_cover :
    clusterUnion M.balancedLabeledPart = Finset.univ := by
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  intro x _
  by_cases hx : x ∈ M.balancedCoreUnion
  · obtain ⟨z, hxz⟩ := mem_clusterUnion_iff.1 hx
    exact mem_clusterUnion_iff.2 ⟨some z, hxz⟩
  · exact mem_clusterUnion_iff.2 ⟨none,
      Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩⟩

theorem card_canonicalCorePart_eq_balancedCorePart
    (z : M.coreCellLabel) :
    (M.canonicalCorePart z).card = (M.balancedCorePart z).card := by
  rcases z with ⟨a, i⟩
  rw [canonicalCorePart, balancedCorePart,
    M.card_canonicalCoreCluster, (M.balancedCoreData a).card_eq i,
    M.card_clusterUnion_orderedAmbientCluster a]
  rfl

theorem card_canonicalCoreUnion_eq_balancedCoreUnion :
    M.canonicalCoreUnion.card = M.balancedCoreUnion.card := by
  rw [canonicalCoreUnion, balancedCoreUnion,
    card_clusterUnion M.canonicalCorePart
      M.canonicalCorePart_pairwiseDisjoint,
    card_clusterUnion M.balancedCorePart
      M.balancedCorePart_pairwiseDisjoint]
  exact Finset.sum_congr rfl fun z _ ↦
    M.card_canonicalCorePart_eq_balancedCorePart z

theorem card_canonicalLabeledPart_eq_balancedLabeledPart
    (o : Option M.coreCellLabel) :
    (M.canonicalLabeledPart o).card = (M.balancedLabeledPart o).card := by
  cases o with
  | some z => exact M.card_canonicalCorePart_eq_balancedCorePart z
  | none =>
      simp only [canonicalLabeledPart, balancedLabeledPart,
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      rw [M.card_canonicalCoreUnion_eq_balancedCoreUnion]

/-- Explicit fine-cell permutation carrying canonical interval pieces to the
equalized pieces with the same dependent label. -/
noncomputable def canonicalToBalancedPerm : Equiv.Perm (Fin M.refinementOrder) :=
  labeledPartitionPerm M.canonicalLabeledPart M.balancedLabeledPart
    M.canonicalLabeledPart_pairwiseDisjoint M.canonicalLabeledPart_cover
    M.balancedLabeledPart_pairwiseDisjoint M.balancedLabeledPart_cover
    M.card_canonicalLabeledPart_eq_balancedLabeledPart

theorem canonicalToBalancedPerm_mem_iff
    (o : Option M.coreCellLabel) (x : Fin M.refinementOrder) :
    M.canonicalToBalancedPerm x ∈ M.balancedLabeledPart o ↔
      x ∈ M.canonicalLabeledPart o := by
  exact labeledPartitionPerm_mem_iff
    M.canonicalLabeledPart M.balancedLabeledPart
    M.canonicalLabeledPart_pairwiseDisjoint M.canonicalLabeledPart_cover
    M.balancedLabeledPart_pairwiseDisjoint M.balancedLabeledPart_cover
    M.card_canonicalLabeledPart_eq_balancedLabeledPart o x

theorem canonicalToBalancedPerm_mem_core_iff
    (z : M.coreCellLabel) (x : Fin M.refinementOrder) :
    M.canonicalToBalancedPerm x ∈ M.balancedCorePart z ↔
      x ∈ M.canonicalCorePart z := by
  exact M.canonicalToBalancedPerm_mem_iff (some z) x

theorem balancedExtremalCoreMatrix_of_mem_same
    (p : ℝ) (a : Fin M.componentCount)
    {i j : Fin (M.orderedCore a).order}
    {x y : Fin M.refinementOrder}
    (hx : x ∈ (M.balancedCoreData a).cluster i)
    (hy : y ∈ (M.balancedCoreData a).cluster j) :
    M.balancedExtremalCoreMatrix p x y =
      profileXiMatrix p (M.orderedCore a) i j := by
  unfold balancedExtremalCoreMatrix
  rw [Matrix.sum_apply, Finset.sum_eq_single a]
  · exact clusterProfileMatrix_of_mem p (M.orderedCore a)
      (M.balancedCoreData a).cluster
      (M.balancedCoreData a).pairwiseDisjoint hx hy
  · intro b _ hba
    apply clusterProfileMatrix_eq_zero_of_not_mem
    intro hxb
    have hxa : x ∈ clusterUnion (M.balancedCoreData a).cluster :=
      mem_clusterUnion_iff.2 ⟨i, hx⟩
    exact Finset.disjoint_left.mp
      (M.balancedCoreSupports_pairwiseDisjoint
        (Set.mem_univ a) (Set.mem_univ b) hba.symm) hxa hxb
  · simp

theorem balancedExtremalCoreMatrix_of_mem_distinct
    (p : ℝ) {a b : Fin M.componentCount} (hab : a ≠ b)
    {i : Fin (M.orderedCore a).order}
    {j : Fin (M.orderedCore b).order}
    {x y : Fin M.refinementOrder}
    (hx : x ∈ (M.balancedCoreData a).cluster i)
    (hy : y ∈ (M.balancedCoreData b).cluster j) :
    M.balancedExtremalCoreMatrix p x y = 0 := by
  unfold balancedExtremalCoreMatrix
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hca : c = a
  · subst c
    rw [← Matrix.IsSymm.apply
      (clusterProfileMatrix_isSymm p (M.orderedCore a)
        (M.balancedCoreData a).cluster) x y]
    apply clusterProfileMatrix_eq_zero_of_not_mem
    intro hyUnion
    have hyb : y ∈ clusterUnion (M.balancedCoreData b).cluster :=
      mem_clusterUnion_iff.2 ⟨j, hy⟩
    exact Finset.disjoint_left.mp
      (M.balancedCoreSupports_pairwiseDisjoint
        (Set.mem_univ a) (Set.mem_univ b) hab) hyUnion hyb
  · apply clusterProfileMatrix_eq_zero_of_not_mem
    intro hxUnion
    have hxa : x ∈ clusterUnion (M.balancedCoreData a).cluster :=
      mem_clusterUnion_iff.2 ⟨i, hx⟩
    exact Finset.disjoint_left.mp
      (M.balancedCoreSupports_pairwiseDisjoint
        (Set.mem_univ a) (Set.mem_univ c) (Ne.symm hca)) hxa hxUnion

theorem balancedExtremalCoreMatrix_eq_zero_of_not_mem
    (p : ℝ) {x y : Fin M.refinementOrder}
    (hx : x ∉ M.balancedCoreUnion) :
    M.balancedExtremalCoreMatrix p x y = 0 := by
  unfold balancedExtremalCoreMatrix
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro a _
  apply clusterProfileMatrix_eq_zero_of_not_mem
  intro hxa
  obtain ⟨i, hxi⟩ := mem_clusterUnion_iff.1 hxa
  exact hx (mem_clusterUnion_iff.2 ⟨⟨a, i⟩, hxi⟩)

/-- Equalized matrix reindexed into canonical consecutive block coordinates. -/
noncomputable def canonicalExtremalCoreMatrix (p : ℝ) :
    Matrix (Fin M.refinementOrder) (Fin M.refinementOrder) ℝ :=
  permuteMatrix M.canonicalToBalancedPerm (M.balancedExtremalCoreMatrix p)

theorem canonicalExtremalCoreMatrix_isSymm (p : ℝ) :
    (M.canonicalExtremalCoreMatrix p).IsSymm :=
  permuteMatrix_isSymm M.canonicalToBalancedPerm
    (M.balancedExtremalCoreMatrix_isSymm p)

theorem canonicalExtremalCoreMatrix_nonneg {p : ℝ} (hp : 0 ≤ p) :
    ∀ x y, 0 ≤ M.canonicalExtremalCoreMatrix p x y :=
  permuteMatrix_nonneg M.canonicalToBalancedPerm
    (M.balancedExtremalCoreMatrix_nonneg hp)

theorem canonicalExtremalCoreMatrix_le_one {p : ℝ} (hp : p ≤ 1) :
    ∀ x y, M.canonicalExtremalCoreMatrix p x y ≤ 1 :=
  permuteMatrix_le_one M.canonicalToBalancedPerm
    (M.balancedExtremalCoreMatrix_le_one hp)

theorem canonicalExtremalCoreMatrix_of_mem_same
    (p : ℝ) (a : Fin M.componentCount)
    {i j : Fin (M.orderedCore a).order}
    {x y : Fin M.refinementOrder}
    (hx : x ∈ M.canonicalCoreCluster a i)
    (hy : y ∈ M.canonicalCoreCluster a j) :
    M.canonicalExtremalCoreMatrix p x y =
      profileXiMatrix p (M.orderedCore a) i j := by
  apply M.balancedExtremalCoreMatrix_of_mem_same p a
  · exact (M.canonicalToBalancedPerm_mem_core_iff ⟨a, i⟩ x).2 hx
  · exact (M.canonicalToBalancedPerm_mem_core_iff ⟨a, j⟩ y).2 hy

theorem canonicalExtremalCoreMatrix_of_mem_distinct
    (p : ℝ) {a b : Fin M.componentCount} (hab : a ≠ b)
    {i : Fin (M.orderedCore a).order}
    {j : Fin (M.orderedCore b).order}
    {x y : Fin M.refinementOrder}
    (hx : x ∈ M.canonicalCoreCluster a i)
    (hy : y ∈ M.canonicalCoreCluster b j) :
    M.canonicalExtremalCoreMatrix p x y = 0 := by
  apply M.balancedExtremalCoreMatrix_of_mem_distinct p hab
  · exact (M.canonicalToBalancedPerm_mem_core_iff ⟨a, i⟩ x).2 hx
  · exact (M.canonicalToBalancedPerm_mem_core_iff ⟨b, j⟩ y).2 hy

theorem canonicalExtremalCoreMatrix_eq_zero_of_tail
    (p : ℝ) {x y : Fin M.refinementOrder}
    (hx : x ∈ M.canonicalLabeledPart none) :
    M.canonicalExtremalCoreMatrix p x y = 0 := by
  apply M.balancedExtremalCoreMatrix_eq_zero_of_not_mem p
  have hpermTail := (M.canonicalToBalancedPerm_mem_iff none x).2 hx
  exact (Finset.mem_sdiff.1 hpermTail).2

end FiniteExtremalBlockModel

/-- A canonical `D`-cell whose index lies between two integral endpoints is
contained in the corresponding half-open unit interval. -/
theorem equalCell_subset_Ico_of_endpoints {D s t : ℕ}
    (x : Fin D) (hsx : s ≤ x) (hxt : x < t)
    (u v : UnitInterval)
    (hu : (u : ℝ) = (s : ℝ) / (D : ℝ))
    (hv : (v : ℝ) = (t : ℝ) / (D : ℝ)) :
    equalCell x ⊆ Set.Ico u v := by
  intro z hz
  change equalCellLeft x ≤ z ∧ z < equalCellRight x at hz
  have hzlo : (equalCellLeft x : ℝ) ≤ (z : ℝ) := hz.1
  have hzhi : (z : ℝ) < (equalCellRight x : ℝ) := hz.2
  have hzlo' : (x : ℝ) / (D : ℝ) ≤ (z : ℝ) := by
    simpa [equalCellLeft] using hzlo
  have hzhi' : (z : ℝ) < (((x : ℕ) + 1 : ℕ) : ℝ) / (D : ℝ) := by
    simpa [equalCellRight] using hzhi
  change (u : ℝ) ≤ (z : ℝ) ∧ (z : ℝ) < (v : ℝ)
  constructor
  · rw [hu]
    exact ((div_le_div_iff_of_pos_right
      (by exact_mod_cast Nat.zero_lt_of_lt x.isLt)).2
      (by exact_mod_cast hsx)).trans hzlo'
  · rw [hv]
    exact hzhi'.trans_le ((div_le_div_iff_of_pos_right
      (by exact_mod_cast Nat.zero_lt_of_lt x.isLt)).2
      (by exact_mod_cast (Nat.succ_le_iff.mpr hxt)))

namespace FiniteExtremalBlockModel

variable {k q : ℕ} {C : ColoredGraph (Fin q)}
    (M : FiniteExtremalBlockModel k q C)

theorem blockSequence_blockStart_eq_prefix (a : Fin M.componentCount) :
    M.blockSequence.blockStart a.val =
      (M.orderedCorePrefixSize a.val : ℝ) / (q : ℝ) := by
  unfold AdmissibleBlockSequence.blockStart orderedCorePrefixSize
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  have hba : b < a.val := Finset.mem_range.1 hb
  have hbcount : b < M.componentCount := hba.trans a.isLt
  rw [M.blockSequence_alpha_of_lt hbcount,
    M.finiteOrderedCoreSize_of_lt hbcount]
  rfl

/-- The canonical transport of an ordered-core vertex into the definitionally
equal active core carried by the finite block sequence. -/
def canonicalBlockVertex (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) :
    Fin (M.blockSequence.core a.val).order :=
  Fin.cast (congrArg RegularBlockCore.order
    (M.blockSequence_core_of_lt a.isLt).symm) i

/-- The canonical vertex transport, packaged as an equivalence so that every
vertex of an active block core has a unique ordered-core preimage. -/
def canonicalBlockVertexEquiv (a : Fin M.componentCount) :
    Fin (M.orderedCore a).order ≃
      Fin (M.blockSequence.core a.val).order :=
  finCongr (congrArg RegularBlockCore.order
    (M.blockSequence_core_of_lt a.isLt).symm)

@[simp] theorem canonicalBlockVertexEquiv_apply
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order) :
    M.canonicalBlockVertexEquiv a i = M.canonicalBlockVertex a i := rfl

@[simp] theorem canonicalBlockVertex_val (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) :
    (M.canonicalBlockVertex a i).val = i.val := rfl

theorem blockSequence_cellLeftUI_eq_canonical
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order) :
    (M.blockSequence.cellLeftUI a.val (M.canonicalBlockVertex a i) : ℝ) =
      (M.canonicalCoreClusterStart a i : ℝ) /
        (M.refinementOrder : ℝ) := by
  have hfactor : (M.orderedCore a).order *
      (M.refinementFactor / (M.orderedCore a).order) = M.refinementFactor :=
    Nat.mul_div_cancel' (M.orderedCoreOrder_dvd_refinementFactor a)
  have hfactorR : ((M.orderedCore a).order : ℝ) *
      (M.refinementFactor / (M.orderedCore a).order : ℕ) =
        M.refinementFactor := by
    exact_mod_cast hfactor
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast M.ambientOrder_pos.ne'
  have hP : (M.refinementFactor : ℝ) ≠ 0 := by
    exact_mod_cast M.refinementFactor_pos.ne'
  have hℓ : ((M.orderedCore a).order : ℝ) ≠ 0 := by
    exact_mod_cast (M.orderedCore a).order_pos.ne'
  have hcoreOrder : (M.blockSequence.core a.val).order =
      (M.orderedCore a).order := congrArg RegularBlockCore.order
        (M.blockSequence_core_of_lt a.isLt)
  have hcoreOrderR : ((M.blockSequence.core a.val).order : ℝ) =
      ((M.orderedCore a).order : ℝ) := by exact_mod_cast hcoreOrder
  have hiValR : ((M.canonicalBlockVertex a i : ℕ) : ℝ) = (i : ℝ) := by
    exact_mod_cast M.canonicalBlockVertex_val a i
  change M.blockSequence.cellLeft a.val (M.canonicalBlockVertex a i) = _
  rw [AdmissibleBlockSequence.cellLeft,
    M.blockSequence_blockStart_eq_prefix a,
    M.blockSequence_alpha_of_lt a.isLt]
  unfold orderedLength ColoredGraph.ExtremalFamilyWitness.orderedCoreLength
  unfold canonicalCoreClusterStart canonicalCoreClusterSize refinementOrder
  push_cast
  rw [hcoreOrderR, hiValR]
  simp only [Fin.eta]
  field_simp [hq, hP, hℓ]
  rw [← hfactorR]
  ring

theorem blockSequence_cellRightUI_eq_canonical
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order) :
    (M.blockSequence.cellRightUI a.val (M.canonicalBlockVertex a i) : ℝ) =
      ((M.canonicalCoreClusterStart a i +
        M.canonicalCoreClusterSize a : ℕ) : ℝ) /
          (M.refinementOrder : ℝ) := by
  have hfactor : (M.orderedCore a).order *
      (M.refinementFactor / (M.orderedCore a).order) = M.refinementFactor :=
    Nat.mul_div_cancel' (M.orderedCoreOrder_dvd_refinementFactor a)
  have hfactorR : ((M.orderedCore a).order : ℝ) *
      (M.refinementFactor / (M.orderedCore a).order : ℕ) =
        M.refinementFactor := by
    exact_mod_cast hfactor
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast M.ambientOrder_pos.ne'
  have hP : (M.refinementFactor : ℝ) ≠ 0 := by
    exact_mod_cast M.refinementFactor_pos.ne'
  have hℓ : ((M.orderedCore a).order : ℝ) ≠ 0 := by
    exact_mod_cast (M.orderedCore a).order_pos.ne'
  have hcoreOrder : (M.blockSequence.core a.val).order =
      (M.orderedCore a).order := congrArg RegularBlockCore.order
        (M.blockSequence_core_of_lt a.isLt)
  have hcoreOrderR : ((M.blockSequence.core a.val).order : ℝ) =
      ((M.orderedCore a).order : ℝ) := by exact_mod_cast hcoreOrder
  have hiValR : ((M.canonicalBlockVertex a i : ℕ) : ℝ) = (i : ℝ) := by
    exact_mod_cast M.canonicalBlockVertex_val a i
  change M.blockSequence.cellRight a.val (M.canonicalBlockVertex a i) = _
  rw [AdmissibleBlockSequence.cellRight,
    M.blockSequence_blockStart_eq_prefix a,
    M.blockSequence_alpha_of_lt a.isLt]
  unfold orderedLength ColoredGraph.ExtremalFamilyWitness.orderedCoreLength
  unfold canonicalCoreClusterStart canonicalCoreClusterSize refinementOrder
  push_cast
  rw [hcoreOrderR, hiValR]
  simp only [Fin.eta]
  field_simp [hq, hP, hℓ]
  rw [← hfactorR]
  ring

/-- Every canonical common-grid cell carrying label `(a,i)` lies in the
corresponding block cell of the finite admissible sequence. -/
theorem equalCell_subset_blockCell_of_mem_canonicalCoreCluster
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order)
    (x : Fin M.refinementOrder) (hx : x ∈ M.canonicalCoreCluster a i) :
    equalCell x ⊆
      M.blockSequence.blockCell a.val (M.canonicalBlockVertex a i) := by
  have hrange := (M.mem_canonicalCoreCluster_iff a i x).1 hx
  apply equalCell_subset_Ico_of_endpoints x hrange.1 hrange.2
      (M.blockSequence.cellLeftUI a.val (M.canonicalBlockVertex a i))
      (M.blockSequence.cellRightUI a.val (M.canonicalBlockVertex a i))
  · exact M.blockSequence_cellLeftUI_eq_canonical a i
  · exact M.blockSequence_cellRightUI_eq_canonical a i

/-- Set-level union of the fine equal cells carrying one canonical core label. -/
def canonicalCoreCellSet (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) : Set UnitInterval :=
  equalCellFinsetUnion (M.canonicalCoreCluster a i)

theorem measurableSet_canonicalCoreCellSet (a : Fin M.componentCount)
    (i : Fin (M.orderedCore a).order) :
    MeasurableSet (M.canonicalCoreCellSet a i) :=
  measurableSet_equalCellFinsetUnion _

theorem canonicalCoreCellSet_subset_blockCell
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order) :
    M.canonicalCoreCellSet a i ⊆
      M.blockSequence.blockCell a.val (M.canonicalBlockVertex a i) := by
  intro x hx
  obtain ⟨t, hxt⟩ := Set.mem_iUnion.1 hx
  exact M.equalCell_subset_blockCell_of_mem_canonicalCoreCluster
    a i t t.property hxt

theorem volumeReal_canonicalCoreCellSet
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order) :
    (volume : Measure UnitInterval).real (M.canonicalCoreCellSet a i) =
      (M.canonicalCoreClusterSize a : ℝ) / (M.refinementOrder : ℝ) := by
  rw [canonicalCoreCellSet,
    volumeReal_equalCellFinsetUnion M.refinementOrder_pos,
    M.card_canonicalCoreCluster]

theorem canonicalCoreCellSet_ae_eq_blockCell
    (a : Fin M.componentCount) (i : Fin (M.orderedCore a).order) :
    M.canonicalCoreCellSet a i =ᵐ[volume]
      M.blockSequence.blockCell a.val (M.canonicalBlockVertex a i) := by
  apply ae_eq_of_subset_of_measure_ge
    (M.canonicalCoreCellSet_subset_blockCell a i)
  · have hfactor : (M.orderedCore a).order *
        (M.refinementFactor / (M.orderedCore a).order) = M.refinementFactor :=
      Nat.mul_div_cancel' (M.orderedCoreOrder_dvd_refinementFactor a)
    have hfactorR : ((M.orderedCore a).order : ℝ) *
        (M.refinementFactor / (M.orderedCore a).order : ℕ) =
          M.refinementFactor := by exact_mod_cast hfactor
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast M.ambientOrder_pos.ne'
    have hP : (M.refinementFactor : ℝ) ≠ 0 := by
      exact_mod_cast M.refinementFactor_pos.ne'
    have hℓ : ((M.orderedCore a).order : ℝ) ≠ 0 := by
      exact_mod_cast (M.orderedCore a).order_pos.ne'
    have hcoreOrder : (M.blockSequence.core a.val).order =
        (M.orderedCore a).order := congrArg RegularBlockCore.order
          (M.blockSequence_core_of_lt a.isLt)
    have hcoreOrderR : ((M.blockSequence.core a.val).order : ℝ) =
        ((M.orderedCore a).order : ℝ) := by exact_mod_cast hcoreOrder
    have hreal :
        (volume : Measure UnitInterval).real
            (M.blockSequence.blockCell a.val (M.canonicalBlockVertex a i)) =
          (volume : Measure UnitInterval).real (M.canonicalCoreCellSet a i) := by
      rw [M.blockSequence.volumeReal_blockCell,
        M.volumeReal_canonicalCoreCellSet,
        M.blockSequence_alpha_of_lt a.isLt, hcoreOrderR]
      unfold orderedLength ColoredGraph.ExtremalFamilyWitness.orderedCoreLength
      unfold canonicalCoreClusterSize refinementOrder
      push_cast
      simp only [Fin.eta]
      field_simp [hq, hP, hℓ]
      rw [← hfactorR]
      ring
    exact ((measureReal_eq_measureReal_iff).1 hreal).le
  · exact (M.measurableSet_canonicalCoreCellSet a i).nullMeasurableSet
  · finiteness

/-- Union of all canonical fine-grid cells that carry an active core label. -/
def canonicalCoreCellUnion : Set UnitInterval :=
  ⋃ z : M.coreCellLabel, M.canonicalCoreCellSet z.1 z.2

/-- Union of the finitely many active block intervals. -/
def activeBlockIntervalUnion : Set UnitInterval :=
  ⋃ a : Fin M.componentCount, M.blockSequence.blockInterval a.val

/-- The canonical common-grid support and the active block support agree up
to the endpoint null sets. -/
theorem canonicalCoreCellUnion_ae_eq_activeBlockIntervalUnion :
    M.canonicalCoreCellUnion =ᵐ[volume] M.activeBlockIntervalUnion := by
  have hcells : ∀ᵐ u ∂volume, ∀ z : M.coreCellLabel,
      (u ∈ M.canonicalCoreCellSet z.1 z.2 ↔
        u ∈ M.blockSequence.blockCell z.1.val
          (M.canonicalBlockVertex z.1 z.2)) :=
    Filter.eventually_all.2 fun z ↦
      (M.canonicalCoreCellSet_ae_eq_blockCell z.1 z.2).mono
        (fun u hu ↦ by
          change M.canonicalCoreCellSet z.1 z.2 u ↔
            M.blockSequence.blockCell z.1.val
              (M.canonicalBlockVertex z.1 z.2) u
          exact iff_of_eq hu)
  have hblocks : ∀ᵐ u ∂volume, ∀ a : Fin M.componentCount,
      (u ∈ M.blockSequence.blockCellUnion a.val ↔
        u ∈ M.blockSequence.blockInterval a.val) :=
    Filter.eventually_all.2 fun a ↦
      (M.blockSequence.blockCellUnion_ae_eq_blockInterval a.val).mono
        (fun u hu ↦ by
          change M.blockSequence.blockCellUnion a.val u ↔
            M.blockSequence.blockInterval a.val u
          exact iff_of_eq hu)
  filter_upwards [hcells, hblocks] with u hcell hblock
  apply propext
  constructor
  · intro hu
    obtain ⟨z, huz⟩ := Set.mem_iUnion.1 hu
    refine Set.mem_iUnion.2 ⟨z.1, (hblock z.1).1 ?_⟩
    exact Set.mem_iUnion.2
      ⟨M.canonicalBlockVertex z.1 z.2, (hcell z).1 huz⟩
  · intro hu
    obtain ⟨a, hua⟩ := Set.mem_iUnion.1 hu
    have huCells : u ∈ M.blockSequence.blockCellUnion a.val :=
      (hblock a).2 hua
    obtain ⟨v, huv⟩ := Set.mem_iUnion.1 huCells
    obtain ⟨i, rfl⟩ := (M.canonicalBlockVertexEquiv a).surjective v
    exact Set.mem_iUnion.2
      ⟨⟨a, i⟩, (hcell ⟨a, i⟩).2 (by simpa using huv)⟩

theorem not_mem_canonicalCoreCellUnion_of_tail
    {x : Fin M.refinementOrder}
    (hx : x ∈ M.canonicalLabeledPart none) {u : UnitInterval}
    (hux : u ∈ equalCell x) : u ∉ M.canonicalCoreCellUnion := by
  intro hu
  obtain ⟨z, huz⟩ := Set.mem_iUnion.1 hu
  obtain ⟨t, hut⟩ := Set.mem_iUnion.1 huz
  have htx : (t : Fin M.refinementOrder) = x :=
    equalCell_eq_of_mem hut hux
  have hxCore : x ∈ M.canonicalCoreUnion := by
    apply mem_clusterUnion_iff.2
    refine ⟨z, ?_⟩
    simpa [canonicalCorePart, htx] using t.property
  exact (Finset.mem_sdiff.1 hx).2 hxCore

/-- At an a.e. support-identification point, lying in a tail equal cell rules
out every block interval, including the zero-length inactive blocks. -/
theorem not_mem_any_blockInterval_of_tail
    {x : Fin M.refinementOrder}
    (hx : x ∈ M.canonicalLabeledPart none) {u : UnitInterval}
    (hux : u ∈ equalCell x)
    (hsupport :
      (u ∈ M.canonicalCoreCellUnion ↔
        u ∈ M.activeBlockIntervalUnion)) :
    ∀ n : ℕ, u ∉ M.blockSequence.blockInterval n := by
  intro n
  by_cases hn : n < M.componentCount
  · intro hun
    apply M.not_mem_canonicalCoreCellUnion_of_tail hx hux
    exact hsupport.2 (Set.mem_iUnion.2 ⟨⟨n, hn⟩, hun⟩)
  · rw [M.blockSequence.blockInterval_eq_empty_of_alpha_eq_zero n
      (M.blockSequence_alpha_of_le (Nat.le_of_not_gt hn))]
    simp

end FiniteExtremalBlockModel

/-- Lift a permutation of the coarse cells, without changing the fine index
inside any coarse cell. -/
def uniformRefinementPerm {q : ℕ} (P : ℕ)
    (perm : Equiv.Perm (Fin q)) : Equiv.Perm (Fin (q * P)) :=
  (typeFineCellEquiv q P).symm |>.trans
    (((perm.prodCongr (Equiv.refl (Fin P))).trans (typeFineCellEquiv q P)))

@[simp] theorem uniformRefinementPerm_apply {q P : ℕ}
    (perm : Equiv.Perm (Fin q)) (i : Fin q) (a : Fin P) :
    uniformRefinementPerm P perm (typeFineCellEquiv q P (i, a)) =
      typeFineCellEquiv q P (perm i, a) := by
  simp [uniformRefinementPerm]

/-- Uniform refinement commutes exactly with a lifted coarse permutation. -/
theorem permuteMatrix_uniformRefinementPerm {q P : ℕ}
    (perm : Equiv.Perm (Fin q)) (M : Matrix (Fin q) (Fin q) ℝ) :
    permuteMatrix (uniformRefinementPerm P perm)
        (typeUniformRefinementMatrix (n := P) M) =
      typeUniformRefinementMatrix (n := P) (permuteMatrix perm M) := by
  ext x y
  obtain ⟨xa, rfl⟩ := (typeFineCellEquiv q P).surjective x
  obtain ⟨yb, rfl⟩ := (typeFineCellEquiv q P).surjective y
  have hx : (typeFineCellEquiv q P).symm
      (uniformRefinementPerm P perm (typeFineCellEquiv q P xa)) =
      (perm xa.1, xa.2) := by
    rw [uniformRefinementPerm_apply]
    exact (typeFineCellEquiv q P).symm_apply_apply _
  have hy : (typeFineCellEquiv q P).symm
      (uniformRefinementPerm P perm (typeFineCellEquiv q P yb)) =
      (perm yb.1, yb.2) := by
    rw [uniformRefinementPerm_apply]
    exact (typeFineCellEquiv q P).symm_apply_apply _
  simp only [permuteMatrix, typeUniformRefinementMatrix, Matrix.submatrix_apply]
  rw [hx, hy]
  simp

/-! ## Exact `L¹` accounting for equal-cell matrix graphons -/

/-- The `L¹` distance between two equal-cell matrix graphons is the average
absolute entrywise difference. -/
theorem graphonL1Dist_matrixGraphon_eq_entrySum {q : ℕ} (hq : 0 < q)
    (M N : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (hN : N.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (hN₀ : ∀ i j, 0 ≤ N i j) (hN₁ : ∀ i j, N i j ≤ 1) :
    graphonL1Dist (matrixGraphon M hM hM₀ hM₁)
        (matrixGraphon N hN hN₀ hN₁) =
      (1 / (q : ℝ)) ^ 2 *
        ∑ i : Fin q, ∑ j : Fin q, |M i j - N i j| := by
  let WM := matrixGraphon M hM hM₀ hM₁
  let WN := matrixGraphon N hN hN₀ hN₁
  have hcell (i j : Fin q) :
      (∫ z in equalCell i ×ˢ equalCell j, |WM z - WN z| ∂unitSquareMeasure) =
        (1 / (q : ℝ)) ^ 2 * |M i j - N i j| := by
    calc
      _ = ∫ _z in equalCell i ×ˢ equalCell j, |M i j - N i j|
          ∂unitSquareMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem ((measurableSet_equalCell i).prod
            (measurableSet_equalCell j)),
          ae_restrict_of_ae
            (matrixGraphon_ae_eq_on_cell M hM hM₀ hM₁ i j),
          ae_restrict_of_ae
            (matrixGraphon_ae_eq_on_cell N hN hN₀ hN₁ i j)]
          with z hzMem hzM hzN
        simpa only [WM, WN] using
          congrArg₂ (fun x y : ℝ ↦ |x - y|) (hzM hzMem) (hzN hzMem)
      _ = (unitSquareMeasure (equalCell i ×ˢ equalCell j)).toReal *
          |M i j - N i j| := by
        rw [integral_const]
        simp [smul_eq_mul, Measure.real_def]
      _ = _ := by
        rw [show unitSquareMeasure (equalCell i ×ˢ equalCell j) =
            ENNReal.ofReal (1 / (q : ℝ)) ^ 2 from volume_equalCell_prod i j,
          ENNReal.toReal_pow, ENNReal.toReal_ofReal]
        positivity
  rw [graphonL1Dist_eq_integral,
    integral_eq_setIntegral (ae_mem_iUnion_equalCell_prod hq),
    integral_iUnion_fintype]
  · calc
      (∑ ij : Fin q × Fin q,
          ∫ z in equalCell ij.1 ×ˢ equalCell ij.2, |WM z - WN z|
            ∂unitSquareMeasure) =
          ∑ ij : Fin q × Fin q,
            (1 / (q : ℝ)) ^ 2 * |M ij.1 ij.2 - N ij.1 ij.2| := by
        apply Finset.sum_congr rfl
        intro ij _
        exact hcell ij.1 ij.2
      _ = _ := by rw [← Finset.mul_sum, Fintype.sum_prod_type]
  · intro ij
    exact (measurableSet_equalCell ij.1).prod (measurableSet_equalCell ij.2)
  · exact pairwise_disjoint_equalCell_prod
  · intro ij
    exact ((matrixGraphon M hM hM₀ hM₁).integrable.sub
      (matrixGraphon N hN hN₀ hN₁).integrable).abs.integrableOn

/-! ## Canonical finite graphon representation of the equalized block model -/

namespace FiniteExtremalBlockModel

variable {k q : ℕ} {C : ColoredGraph (Fin q)}
    (M : FiniteExtremalBlockModel k q C)

theorem profileXiMatrix_blockSequence_canonicalBlockVertex
    (p : ℝ) (a : Fin M.componentCount)
    (i j : Fin (M.orderedCore a).order) :
    profileXiMatrix p (M.blockSequence.core a.val)
        (M.canonicalBlockVertex a i) (M.canonicalBlockVertex a j) =
      profileXiMatrix p (M.orderedCore a) i j := by
  simpa only [canonicalBlockVertex] using
    profileXiMatrix_transport p
      (M.blockSequence_core_of_lt a.isLt).symm i j

/-- Equal-cell matrix graphon in the balanced finite coordinates. -/
noncomputable def balancedExtremalCoreGraphon
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : Graphon :=
  matrixGraphon (M.balancedExtremalCoreMatrix p)
    (M.balancedExtremalCoreMatrix_isSymm p)
    (M.balancedExtremalCoreMatrix_nonneg hp.1)
    (M.balancedExtremalCoreMatrix_le_one hp.2)

/-- The same equalized finite graphon in canonical consecutive block
coordinates. -/
noncomputable def canonicalExtremalCoreGraphon
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : Graphon :=
  matrixGraphon (M.canonicalExtremalCoreMatrix p)
    (M.canonicalExtremalCoreMatrix_isSymm p)
    (M.canonicalExtremalCoreMatrix_nonneg hp.1)
    (M.canonicalExtremalCoreMatrix_le_one hp.2)

/-- The explicit labeled-partition permutation is exactly the relabeling from
balanced finite coordinates to canonical block coordinates. -/
theorem canonicalExtremalCoreGraphon_eq_relabel
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    M.canonicalExtremalCoreGraphon p hp =
      (M.balancedExtremalCoreGraphon p hp).relabel
        (cellPermRelabeling M.canonicalToBalancedPerm) := by
  simpa only [canonicalExtremalCoreGraphon, balancedExtremalCoreGraphon,
    canonicalExtremalCoreMatrix] using
    matrixGraphon_permuteMatrix_eq_relabel M.canonicalToBalancedPerm
      (M.balancedExtremalCoreMatrix p)
      (M.balancedExtremalCoreMatrix_isSymm p)
      (M.balancedExtremalCoreMatrix_nonneg hp.1)
      (M.balancedExtremalCoreMatrix_le_one hp.2)

/-- Consequently, the balanced equal-cell model and its canonical-coordinate
version have cut distance zero. -/
theorem cutDist_canonicalExtremalCoreGraphon_balancedExtremalCoreGraphon_eq_zero
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    cutDist (M.canonicalExtremalCoreGraphon p hp)
      (M.balancedExtremalCoreGraphon p hp) = 0 := by
  simpa only [canonicalExtremalCoreGraphon, balancedExtremalCoreGraphon,
    canonicalExtremalCoreMatrix] using
    cutDist_matrixGraphon_permuteMatrix_eq_zero
      M.canonicalToBalancedPerm (M.balancedExtremalCoreMatrix p)
      (M.balancedExtremalCoreMatrix_isSymm p)
      (M.balancedExtremalCoreMatrix_nonneg hp.1)
      (M.balancedExtremalCoreMatrix_le_one hp.2)

/-- The literal refined-core matrix graphon is within
`8 (k-1) / q` in `L¹` of the balanced finite-coordinate graphon.  This is
the quantitative equalization leg before the exact canonical relabeling. -/
theorem graphonL1Dist_matrixGraphon_refinedExtremalCoreMatrix_balancedExtremalCoreGraphon_le
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonL1Dist
        (matrixGraphon (M.refinedExtremalCoreMatrix p)
          (M.refinedExtremalCoreMatrix_isSymm p)
          (M.refinedExtremalCoreMatrix_nonneg hp.1)
          (M.refinedExtremalCoreMatrix_le_one hp.2))
        (M.balancedExtremalCoreGraphon p hp) ≤
      ((8 * (k - 1) : ℕ) : ℝ) / (q : ℝ) := by
  unfold balancedExtremalCoreGraphon
  rw [graphonL1Dist_matrixGraphon_eq_entrySum M.refinementOrder_pos
    (M.refinedExtremalCoreMatrix p) (M.balancedExtremalCoreMatrix p)
    (M.refinedExtremalCoreMatrix_isSymm p)
    (M.balancedExtremalCoreMatrix_isSymm p)
    (M.refinedExtremalCoreMatrix_nonneg hp.1)
    (M.refinedExtremalCoreMatrix_le_one hp.2)
    (M.balancedExtremalCoreMatrix_nonneg hp.1)
    (M.balancedExtremalCoreMatrix_le_one hp.2)]
  calc
    (1 / (M.refinementOrder : ℝ)) ^ 2 *
        ∑ x : Fin M.refinementOrder, ∑ y : Fin M.refinementOrder,
          |M.refinedExtremalCoreMatrix p x y -
            M.balancedExtremalCoreMatrix p x y| ≤
      (1 / (M.refinementOrder : ℝ)) ^ 2 *
        ((8 * (k - 1) * q * M.refinementFactor ^ 2 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (M.sum_abs_refinedExtremalCoreMatrix_balancedExtremalCoreMatrix_le hp)
        (sq_nonneg _)
    _ = ((8 * (k - 1) : ℕ) : ℝ) / (q : ℝ) := by
      have hq : (q : ℝ) ≠ 0 := by
        exact_mod_cast M.ambientOrder_pos.ne'
      have hP : (M.refinementFactor : ℝ) ≠ 0 := by
        exact_mod_cast M.refinementFactor_pos.ne'
      unfold refinementOrder
      push_cast
      field_simp [hq, hP]

/-- The canonical common-grid matrix is literally the finite block-profile
graphon.  Endpoint choices are handled by the preceding a.e. support
identification; no arbitrary ambient-coordinate relabeling is used. -/
theorem canonicalExtremalCoreGraphon_eq_profileGraphon
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    M.canonicalExtremalCoreGraphon p hp = M.profileGraphon p hp := by
  apply Graphon.ext
  have hsupport : ∀ᵐ u ∂volume,
      (u ∈ M.canonicalCoreCellUnion ↔
        u ∈ M.activeBlockIntervalUnion) :=
    M.canonicalCoreCellUnion_ae_eq_activeBlockIntervalUnion.mono
      (fun u hu ↦ iff_of_eq hu)
  have hsupport₁ : ∀ᵐ z : UnitSquare ∂unitSquareMeasure,
      (z.1 ∈ M.canonicalCoreCellUnion ↔
        z.1 ∈ M.activeBlockIntervalUnion) :=
    (measurePreserving_fst (μ := (volume : Measure UnitInterval))
      (ν := (volume : Measure UnitInterval))).quasiMeasurePreserving.ae hsupport
  have hsupport₂ : ∀ᵐ z : UnitSquare ∂unitSquareMeasure,
      (z.2 ∈ M.canonicalCoreCellUnion ↔
        z.2 ∈ M.activeBlockIntervalUnion) :=
    (measurePreserving_snd (μ := (volume : Measure UnitInterval))
      (ν := (volume : Measure UnitInterval))).quasiMeasurePreserving.ae hsupport
  filter_upwards [matrixGraphon_ae_eq_kernel
      (M.canonicalExtremalCoreMatrix p)
      (M.canonicalExtremalCoreMatrix_isSymm p)
      (M.canonicalExtremalCoreMatrix_nonneg hp.1)
      (M.canonicalExtremalCoreMatrix_le_one hp.2),
    profileWLambda_ae_eq_profileKernel p M.blockSequence hp,
    ae_mem_iUnion_equalCell_prod M.refinementOrder_pos,
    hsupport₁, hsupport₂] with z hmatrix hprofile hcover hsupp₁ hsupp₂
  rw [show M.canonicalExtremalCoreGraphon p hp z =
      matrixKernel (M.canonicalExtremalCoreMatrix p) z by
        simpa only [canonicalExtremalCoreGraphon] using hmatrix,
    show M.profileGraphon p hp z = M.blockSequence.profileKernel p z by
      simpa only [profileGraphon] using hprofile]
  obtain ⟨xy, hxy⟩ := Set.mem_iUnion.1 hcover
  rw [matrixKernel_of_mem (M.canonicalExtremalCoreMatrix p)
    xy.1 xy.2 z hxy.1 hxy.2]
  have hxCover : xy.1 ∈ clusterUnion M.canonicalLabeledPart := by
    rw [M.canonicalLabeledPart_cover]
    simp
  have hyCover : xy.2 ∈ clusterUnion M.canonicalLabeledPart := by
    rw [M.canonicalLabeledPart_cover]
    simp
  obtain ⟨ox, hx⟩ := mem_clusterUnion_iff.1 hxCover
  obtain ⟨oy, hy⟩ := mem_clusterUnion_iff.1 hyCover
  cases ox with
  | none =>
      rw [M.canonicalExtremalCoreMatrix_eq_zero_of_tail p hx]
      exact (M.blockSequence.profileKernel_eq_zero_of_no_block p z
        (M.not_mem_any_blockInterval_of_tail hx hxy.1 hsupp₁)).symm
  | some sx =>
      rcases sx with ⟨a, i⟩
      cases oy with
      | none =>
          have hmatrixZero :
              M.canonicalExtremalCoreMatrix p xy.1 xy.2 = 0 := by
            rw [(M.canonicalExtremalCoreMatrix_isSymm p).apply]
            exact M.canonicalExtremalCoreMatrix_eq_zero_of_tail p hy
          rw [hmatrixZero]
          rw [← M.blockSequence.profileKernel_symm p z]
          exact (M.blockSequence.profileKernel_eq_zero_of_no_block p (z.2, z.1)
            (M.not_mem_any_blockInterval_of_tail hy hxy.2 hsupp₂)).symm
      | some sy =>
          rcases sy with ⟨b, j⟩
          by_cases hab : a = b
          · subst b
            have hxBlock :=
              M.equalCell_subset_blockCell_of_mem_canonicalCoreCluster
                a i xy.1 hx hxy.1
            have hyBlock :=
              M.equalCell_subset_blockCell_of_mem_canonicalCoreCluster
                a j xy.2 hy hxy.2
            rw [M.canonicalExtremalCoreMatrix_of_mem_same p a hx hy,
              M.blockSequence.profileKernel_of_mem M.three_le_k p a.val
                (M.canonicalBlockVertex a i)
                (M.canonicalBlockVertex a j) z hxBlock hyBlock,
              M.profileXiMatrix_blockSequence_canonicalBlockVertex p a i j]
          · have hxBlock :=
              M.equalCell_subset_blockCell_of_mem_canonicalCoreCluster
                a i xy.1 hx hxy.1
            have hyBlock :=
              M.equalCell_subset_blockCell_of_mem_canonicalCoreCluster
                b j xy.2 hy hxy.2
            rw [M.canonicalExtremalCoreMatrix_of_mem_distinct p hab hx hy]
            exact (M.blockSequence.profileKernel_eq_zero_of_mem_distinct_blocks p
              (fun habv ↦ hab (Fin.ext habv)) z
              (M.blockSequence.blockCell_subset_interval a.val
                (M.canonicalBlockVertex a i) hxBlock)
              (M.blockSequence.blockCell_subset_interval b.val
                (M.canonicalBlockVertex b j) hyBlock)).symm

/-- The balanced-coordinate graphon retains the separated palette
`{0,p,1}`.  The proof transports the already identified canonical profile
back through the explicit finite-cell relabeling. -/
theorem balancedExtremalCoreGraphon_ae_threeValued
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      (M.balancedExtremalCoreGraphon p hp).value z = 0 ∨
        (M.balancedExtremalCoreGraphon p hp).value z = p ∨
          (M.balancedExtremalCoreGraphon p hp).value z = 1 := by
  let B := M.balancedExtremalCoreGraphon p hp
  let e := cellPermRelabeling M.canonicalToBalancedPerm
  have hcanonical : ∀ᵐ z ∂unitSquareMeasure,
      (M.canonicalExtremalCoreGraphon p hp).value z = 0 ∨
        (M.canonicalExtremalCoreGraphon p hp).value z = p ∨
          (M.canonicalExtremalCoreGraphon p hp).value z = 1 := by
    rw [M.canonicalExtremalCoreGraphon_eq_profileGraphon p hp]
    exact M.profileGraphon_ae_threeValued p hp
  rw [M.canonicalExtremalCoreGraphon_eq_relabel p hp] at hcanonical
  have hpushed : ∀ᵐ z ∂unitSquareMeasure,
      B.value (e.prodEquiv z) = 0 ∨
        B.value (e.prodEquiv z) = p ∨
          B.value (e.prodEquiv z) = 1 := by
    filter_upwards [hcanonical, B.relabel_value_ae_eq e] with z hz hrel
    simpa only [B, e, hrel] using hz
  have hpull :=
    e.symm.measurePreserving_prodEquiv.quasiMeasurePreserving.ae hpushed
  filter_upwards [hpull] with z hz
  simpa [GraphonRelabeling.prodEquiv_apply] using hz

end FiniteExtremalBlockModel

end InducedStars
