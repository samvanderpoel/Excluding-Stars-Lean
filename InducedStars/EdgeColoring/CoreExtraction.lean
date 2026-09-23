import InducedStars.EdgeColoring.StabilityBasic
import InducedStars.PriorLiterature

/-!
# Colored core extraction

This file contains the finite witness returned by the core-extraction
recursion.  The elementary set operations below are kept transparent so that
later arguments can unfold the extracted core and its remainder without
passing through an opaque predicate.
-/

namespace InducedStars

namespace ColoredGraph

/-! ## Elementary large-order absorption -/

/-- A fixed nonnegative additive error is eventually absorbed by any
strictly positive gap between two linear coefficients.  Core extraction uses
this one lemma for ceiling constants in the seed, overlap, regularity, and
boundary estimates. -/
theorem exists_nat_forall_mul_add_le_mul
    {a b c : ℝ} (hab : a < b) (hc : 0 ≤ c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      a * (n : ℝ) + c ≤ b * (n : ℝ) := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  let n₀ : ℕ := ⌈c / (b - a)⌉₊
  refine ⟨n₀, ?_⟩
  intro n hn
  have hceil : c / (b - a) ≤ (n₀ : ℝ) := by
    exact Nat.le_ceil _
  have hcast : (n₀ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hdiv : c / (b - a) ≤ (n : ℝ) := hceil.trans hcast
  have hmul := (div_le_iff₀ hgap).mp hdiv
  nlinarith

/-! ## Finite low-blue counting -/

section LowBlueCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices of `S` having at most `b` blue neighbors inside `S`. -/
def lowBlueVertices (C : ColoredGraph V) (S : Finset V) (b : ℕ) : Finset V :=
  S.filter fun v ↦ C.blueDegreeIn v S ≤ b

@[simp]
theorem mem_lowBlueVertices (C : ColoredGraph V) (S : Finset V) (b : ℕ) (v : V) :
    v ∈ C.lowBlueVertices S b ↔ v ∈ S ∧ C.blueDegreeIn v S ≤ b := by
  simp [lowBlueVertices]

/-- At a vertex belonging to `S`, the three restricted color degrees count
exactly the other vertices of `S`. -/
theorem redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_mem
    (C : ColoredGraph V) {v : V} {S : Finset V} (hv : v ∈ S) :
    C.redDegreeIn v S + C.greenDegreeIn v S + C.blueDegreeIn v S =
      S.card - 1 := by
  have hdegree (c : EdgeColor) : C.degreeIn c v S = C.degreeIn c v (S.erase v) := by
    unfold degreeIn neighborFinsetIn
    congr 1
    ext w
    by_cases hwv : w = v
    · subst w
      simp
    · simp [hwv]
  simpa only [hdegree, Finset.card_erase_of_mem hv] using
    C.redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_not_mem
      v (S.erase v) (by simp)

/-- Finite Markov/counting estimate used in the seed-cleaning step of core
extraction.  Every vertex with blue degree at most `b` contributes at least
`|S| - 1 - b` red-or-green incidences, while each internal red or green edge
is counted twice. -/
theorem lowBlueVertices_card_mul_le (C : ColoredGraph V) (S : Finset V) (b : ℕ) :
    (C.lowBlueVertices S b).card * (S.card - 1 - b) ≤
      2 * (C.redEdgeCountIn S + C.greenEdgeCountIn S) := by
  classical
  let B := C.lowBlueVertices S b
  have hpoint : ∀ v ∈ B,
      S.card - 1 - b ≤ C.redDegreeIn v S + C.greenDegreeIn v S := by
    intro v hv
    have hvB := (C.mem_lowBlueVertices S b v).1 (by simpa [B] using hv)
    have hcolors := C.redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_mem hvB.1
    omega
  calc
    B.card * (S.card - 1 - b) =
        ∑ v ∈ B, (S.card - 1 - b) := by simp
    _ ≤ ∑ v ∈ B, (C.redDegreeIn v S + C.greenDegreeIn v S) := by
      exact Finset.sum_le_sum fun v hv ↦ hpoint v hv
    _ ≤ ∑ v ∈ S, (C.redDegreeIn v S + C.greenDegreeIn v S) := by
      exact Finset.sum_le_sum_of_subset (by simp [B, lowBlueVertices])
    _ = 2 * (C.redEdgeCountIn S + C.greenEdgeCountIn S) := by
      rw [Finset.sum_add_distrib,
        C.sum_degreeIn_eq_two_mul_edgeCountIn .red S,
        C.sum_degreeIn_eq_two_mul_edgeCountIn .green S]
      change 2 * C.edgeCountIn .red S + 2 * C.edgeCountIn .green S =
        2 * (C.edgeCountIn .red S + C.edgeCountIn .green S)
      omega

end LowBlueCounting

/-! ## Elementary density and boundary double counting -/

section DensityAndBoundaryCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A pointwise lower bound on the internal blue degree gives the matching
blue-edge-density bound.  The hypothesis uses `|S| - 1`, rather than `|S|`,
so the handshake identity produces exactly `Nat.choose |S| 2`. -/
theorem blueEdgeCountIn_lower_of_pointwise_degree
    (C : ColoredGraph V) (S : Finset V) (error : ℝ)
    (hdegree : ∀ v ∈ S,
      (1 - error) * ((S.card : ℝ) - 1) ≤
        (C.blueDegreeIn v S : ℝ)) :
    (1 - error) * (Nat.choose S.card 2 : ℝ) ≤
      (C.blueEdgeCountIn S : ℝ) := by
  have hsum :
      ∑ v ∈ S, (1 - error) * ((S.card : ℝ) - 1) ≤
        ∑ v ∈ S, (C.blueDegreeIn v S : ℝ) :=
    Finset.sum_le_sum fun v hv ↦ hdegree v hv
  have hhandshake :
      ∑ v ∈ S, (C.blueDegreeIn v S : ℝ) =
        2 * (C.blueEdgeCountIn S : ℝ) := by
    exact_mod_cast C.sum_degreeIn_eq_two_mul_edgeCountIn .blue S
  have hscaled :
      (S.card : ℝ) * ((1 - error) * ((S.card : ℝ) - 1)) ≤
        2 * (C.blueEdgeCountIn S : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, hhandshake] using hsum
  have hchoose :
      (Nat.choose S.card 2 : ℝ) =
        (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 := by
    simpa using (Nat.cast_choose_two (K := ℝ) S.card)
  rw [hchoose]
  nlinarith

/-- Summing pointwise red-plus-blue degree bounds over the source set gives
the corresponding bound on the two between-set edge counts. -/
theorem redBlueColorEdgeCountBetween_le_of_pointwise
    (C : ColoredGraph V) (U T : Finset V) (bound : ℝ)
    (hdegree : ∀ v ∈ U,
      (C.redDegreeIn v T : ℝ) + (C.blueDegreeIn v T : ℝ) ≤ bound) :
    (C.colorEdgeCountBetween .red U T : ℝ) +
        (C.colorEdgeCountBetween .blue U T : ℝ) ≤
      (U.card : ℝ) * bound := by
  have hsum :
      ∑ v ∈ U,
          ((C.redDegreeIn v T : ℝ) + (C.blueDegreeIn v T : ℝ)) ≤
        ∑ _v ∈ U, bound :=
    Finset.sum_le_sum fun v hv ↦ hdegree v hv
  have hred :
      ∑ v ∈ U, (C.redDegreeIn v T : ℝ) =
        (C.colorEdgeCountBetween .red U T : ℝ) := by
    exact_mod_cast C.sum_degreeIn_eq_colorEdgeCountBetween .red U T
  have hblue :
      ∑ v ∈ U, (C.blueDegreeIn v T : ℝ) =
        (C.colorEdgeCountBetween .blue U T : ℝ) := by
    exact_mod_cast C.sum_degreeIn_eq_colorEdgeCountBetween .blue U T
  simpa only [Finset.sum_add_distrib, hred, hblue, Finset.sum_const,
    nsmul_eq_mul] using hsum

/-- The ambient-`Fin n` specialization of
`redBlueColorEdgeCountBetween_le_of_pointwise`: a pointwise `error * n`
bound implies the paper's `error * n²` boundary bound. -/
theorem redBlueColorEdgeCountBetween_le_sq_of_pointwise
    {n : ℕ} (C : ColoredGraph (Fin n)) (U T : Finset (Fin n))
    (error : ℝ) (herror : 0 ≤ error)
    (hdegree : ∀ v ∈ U,
      (C.redDegreeIn v T : ℝ) + (C.blueDegreeIn v T : ℝ) ≤
        error * (n : ℝ)) :
    (C.colorEdgeCountBetween .red U T : ℝ) +
        (C.colorEdgeCountBetween .blue U T : ℝ) ≤
      error * (n : ℝ) ^ 2 := by
  have hcardNat : U.card ≤ n := by
    simpa using Finset.card_le_univ U
  have hcard : (U.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcardNat
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    (C.colorEdgeCountBetween .red U T : ℝ) +
          (C.colorEdgeCountBetween .blue U T : ℝ) ≤
        (U.card : ℝ) * (error * (n : ℝ)) :=
      redBlueColorEdgeCountBetween_le_of_pointwise C U T
        (error * (n : ℝ)) hdegree
    _ ≤ (n : ℝ) * (error * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg herror hn)
    _ = error * (n : ℝ) ^ 2 := by ring

end DensityAndBoundaryCounting

/-- The union `U` of the nonexceptional clusters in a core-extraction
witness. -/
def coreExtractionClusterUnion {V : Type*} [Fintype V] [DecidableEq V]
    {l : ℕ} (clusters : Fin l → Finset V) : Finset V :=
  clusterUnion clusters

/-- The full extracted core `U₀ ∪ U`, including its exceptional set. -/
def coreExtractionCore {V : Type*} [Fintype V] [DecidableEq V]
    {l : ℕ} (exceptional : Finset V) (clusters : Fin l → Finset V) : Finset V :=
  exceptional ∪ coreExtractionClusterUnion clusters

/-- The remainder after deleting the full extracted core. -/
def coreExtractionRemainder {V : Type*} [Fintype V] [DecidableEq V]
    {l : ℕ} (exceptional : Finset V) (clusters : Fin l → Finset V) : Finset V :=
  Finset.univ \ coreExtractionCore exceptional clusters

/-! ## Exact cluster-degree bookkeeping for Stage F8 -/

section ClusterDegreeBookkeeping

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

/-- For one cluster in a pairwise-disjoint family, the sum of color degrees
into the full cluster union is twice the internal color-edge count plus one
copy of every color-edge count to a different cluster. -/
theorem sum_degreeIn_clusterUnion_eq_two_mul_edgeCountIn_add_between
    (C : ColoredGraph V) (c : EdgeColor) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters) (r : I) :
    ∑ v ∈ clusters r, C.degreeIn c v (clusterUnion clusters) =
      2 * C.edgeCountIn c (clusters r) +
        ∑ j ∈ (Finset.univ : Finset I).erase r,
          C.colorEdgeCountBetween c (clusters r) (clusters j) := by
  classical
  have hdisj' :
      ((Finset.univ : Finset I) : Set I).PairwiseDisjoint clusters := by
    simpa using hdisj
  have hdegree (v : V) :
      C.degreeIn c v (clusterUnion clusters) =
        ∑ j : I, C.degreeIn c v (clusters j) := by
    simpa only [clusterUnion] using
      C.degreeIn_biUnion c v (Finset.univ : Finset I) clusters hdisj'
  calc
    ∑ v ∈ clusters r, C.degreeIn c v (clusterUnion clusters) =
        ∑ v ∈ clusters r, ∑ j : I, C.degreeIn c v (clusters j) := by
          exact Finset.sum_congr rfl fun v _ ↦ hdegree v
    _ = ∑ j : I, ∑ v ∈ clusters r, C.degreeIn c v (clusters j) := by
      rw [Finset.sum_comm]
    _ = (∑ v ∈ clusters r, C.degreeIn c v (clusters r)) +
        ∑ j ∈ (Finset.univ : Finset I).erase r,
          ∑ v ∈ clusters r, C.degreeIn c v (clusters j) := by
      rw [Finset.add_sum_erase Finset.univ
        (fun j ↦ ∑ v ∈ clusters r, C.degreeIn c v (clusters j))
        (Finset.mem_univ r)]
    _ = 2 * C.edgeCountIn c (clusters r) +
        ∑ j ∈ (Finset.univ : Finset I).erase r,
          C.colorEdgeCountBetween c (clusters r) (clusters j) := by
      rw [C.sum_degreeIn_eq_two_mul_edgeCountIn]
      apply congrArg (2 * C.edgeCountIn c (clusters r) + ·)
      apply Finset.sum_congr rfl
      intro j _
      exact C.sum_degreeIn_eq_colorEdgeCountBetween c (clusters r) (clusters j)

/-- Red specialization of the exact cluster-degree identity. -/
theorem sum_redDegreeIn_clusterUnion_eq_two_mul_redEdgeCountIn_add_between
    (C : ColoredGraph V) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters) (r : I) :
    ∑ v ∈ clusters r, C.redDegreeIn v (clusterUnion clusters) =
      2 * C.redEdgeCountIn (clusters r) +
        ∑ j ∈ (Finset.univ : Finset I).erase r,
          C.colorEdgeCountBetween .red (clusters r) (clusters j) := by
  exact sum_degreeIn_clusterUnion_eq_two_mul_edgeCountIn_add_between
    C .red clusters hdisj r

/-- Blue specialization of the exact cluster-degree identity. -/
theorem sum_blueDegreeIn_clusterUnion_eq_two_mul_blueEdgeCountIn_add_between
    (C : ColoredGraph V) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters) (r : I) :
    ∑ v ∈ clusters r, C.blueDegreeIn v (clusterUnion clusters) =
      2 * C.blueEdgeCountIn (clusters r) +
        ∑ j ∈ (Finset.univ : Finset I).erase r,
          C.colorEdgeCountBetween .blue (clusters r) (clusters j) := by
  exact sum_degreeIn_clusterUnion_eq_two_mul_edgeCountIn_add_between
    C .blue clusters hdisj r

/-- Summing the restricted weighted degree over one cluster gives twice its
internal objective plus the sum of all weighted crossing contributions to
the other clusters. -/
theorem sum_weightedDegreeIn_clusterUnion_eq_two_mul_objectiveIn_add_between
    (k : ℕ) (C : ColoredGraph V) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters) (r : I) :
    ∑ v ∈ clusters r, weightedDegreeIn k C v (clusterUnion clusters) =
      2 * objectiveIn k C (clusters r) +
        ∑ j ∈ (Finset.univ : Finset I).erase r,
          objectiveBetween k C (clusters r) (clusters j) := by
  have hrNat :=
    sum_redDegreeIn_clusterUnion_eq_two_mul_redEdgeCountIn_add_between
      C clusters hdisj r
  have hbNat :=
    sum_blueDegreeIn_clusterUnion_eq_two_mul_blueEdgeCountIn_add_between
      C clusters hdisj r
  have hr := congrArg (fun m : ℕ ↦ (m : ℤ)) hrNat
  have hb := congrArg (fun m : ℕ ↦ (m : ℤ)) hbNat
  push_cast at hr hb
  simp only [weightedDegreeIn, objectiveIn, objectiveBetween,
    Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [hr, hb]
  rw [← Finset.mul_sum]
  ring

/-- Real-cast form of the exact weighted cluster identity, convenient for
the analytic error estimates in Stage F8. -/
theorem sum_weightedDegreeIn_clusterUnion_eq_two_mul_objectiveIn_add_between_real
    (k : ℕ) (C : ColoredGraph V) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters) (r : I) :
    ∑ v ∈ clusters r,
        (weightedDegreeIn k C v (clusterUnion clusters) : ℝ) =
      2 * (objectiveIn k C (clusters r) : ℝ) +
        ∑ j ∈ (Finset.univ : Finset I).erase r,
          (objectiveBetween k C (clusters r) (clusters j) : ℝ) := by
  have h := congrArg (fun z : ℤ ↦ (z : ℝ))
    (sum_weightedDegreeIn_clusterUnion_eq_two_mul_objectiveIn_add_between
      k C clusters hdisj r)
  push_cast at h
  exact h

/-- A pointwise absolute-error bound sums to at most cardinality times the
error. -/
theorem abs_sum_le_card_mul_of_pointwise_abs_le {A : Type*}
    (S : Finset A) (f : A → ℝ) (error : ℝ)
    (h : ∀ x ∈ S, |f x| ≤ error) :
    |∑ x ∈ S, f x| ≤ (S.card : ℝ) * error := by
  calc
    |∑ x ∈ S, f x| ≤ ∑ x ∈ S, |f x| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ S, error := by
      exact Finset.sum_le_sum fun x hx ↦ h x hx
    _ = (S.card : ℝ) * error := by simp

/-- Pointwise control of the weighted degrees on a cluster gives the
corresponding summed-error bound used with the exact identity above. -/
theorem abs_sum_weightedDegreeIn_clusterUnion_le
    (k : ℕ) (C : ColoredGraph V) (clusters : I → Finset V)
    (r : I) (error : ℝ)
    (h : ∀ v ∈ clusters r,
      |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤ error) :
    |∑ v ∈ clusters r,
        (weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
      ((clusters r).card : ℝ) * error := by
  exact abs_sum_le_card_mul_of_pointwise_abs_le
    (clusters r)
    (fun v ↦ (weightedDegreeIn k C v (clusterUnion clusters) : ℝ)) error h

end ClusterDegreeBookkeeping

/-! ## Quantitative reduced-degree bridge for Stage F8 -/

section ReducedDegreeBridge

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

/-- The red edge mass from cluster `i` to all other clusters. -/
noncomputable def interclusterRedCount (C : ColoredGraph V)
    (clusters : I → Finset V) (i : I) : ℝ :=
  ∑ j ∈ (Finset.univ : Finset I).erase i,
    (C.colorEdgeCountBetween .red (clusters i) (clusters j) : ℝ)

/-- Internal blue-degree concentration, a small external blue degree, and
balance around a reference size give pointwise concentration of the total
blue degree into the cluster union. -/
theorem blueDegreeIn_clusterUnion_close_reference
    (C : ColoredGraph V) (clusters : I → Finset V) (i : I) (v : V)
    (reference ownError outsideError sizeError : ℝ)
    (hownError : 0 ≤ ownError) (houtsideError : 0 ≤ outsideError)
    (hsizeError : 0 ≤ sizeError)
    (hsize : |((clusters i).card : ℝ) - reference| ≤ sizeError)
    (hown : ((clusters i).card : ℝ) - ownError ≤
      (C.blueDegreeIn v (clusters i) : ℝ))
    (houtside :
      (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
        outsideError) :
    |(C.blueDegreeIn v (clusterUnion clusters) : ℝ) - reference| ≤
      ownError + outsideError + sizeError := by
  have hsubset : clusters i ⊆ clusterUnion clusters :=
    cluster_subset_clusterUnion clusters i
  have hsplitNat := C.degreeIn_add_degreeIn_sdiff .blue v hsubset
  have hsplit :
      (C.blueDegreeIn v (clusterUnion clusters) : ℝ) =
        (C.blueDegreeIn v (clusters i) : ℝ) +
          (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) := by
    exact_mod_cast hsplitNat.symm
  have hownUpper : (C.blueDegreeIn v (clusters i) : ℝ) ≤
      ((clusters i).card : ℝ) := by
    exact_mod_cast degreeIn_le_card C .blue v (clusters i)
  have houtsideNonneg :
      0 ≤ (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) := by
    positivity
  rw [abs_le] at hsize ⊢
  constructor <;> rw [hsplit] <;> linarith

/-- A between-set color count is at most the number of ordered source-target
pairs. -/
theorem colorEdgeCountBetween_le_card_mul_card_real
    (C : ColoredGraph V) (c : EdgeColor) (S T : Finset V) :
    (C.colorEdgeCountBetween c S T : ℝ) ≤
      (S.card : ℝ) * (T.card : ℝ) := by
  have hsum := C.sum_degreeIn_eq_colorEdgeCountBetween c S T
  have hpoint : ∀ v ∈ S, C.degreeIn c v T ≤ T.card :=
    fun v _ ↦ degreeIn_le_card C c v T
  have hle : C.colorEdgeCountBetween c S T ≤ S.card * T.card := by
    rw [← hsum]
    calc
      ∑ v ∈ S, C.degreeIn c v T ≤ ∑ _v ∈ S, T.card :=
        Finset.sum_le_sum fun v hv ↦ hpoint v hv
      _ = S.card * T.card := by simp
  exact_mod_cast hle

/-- If two nonnegative factors are each within `error` of a nonnegative
reference, their product is within an explicit quadratic error of the
reference square. -/
theorem abs_mul_sub_sq_le_of_abs_sub_le
    {a b reference error : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (href : 0 ≤ reference)
    (herror : 0 ≤ error)
    (ha : |a - reference| ≤ error)
    (hb : |b - reference| ≤ error) :
    |a * b - reference ^ 2| ≤
      2 * (reference + error) * error := by
  have hbUpper : b ≤ reference + error := by
    linarith [le_abs_self (b - reference)]
  have hdecomp :
      a * b - reference ^ 2 =
        (a - reference) * b + reference * (b - reference) := by
    ring
  rw [hdecomp]
  calc
    |(a - reference) * b + reference * (b - reference)| ≤
        |(a - reference) * b| + |reference * (b - reference)| :=
      abs_add_le _ _
    _ = |a - reference| * b + reference * |b - reference| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg href]
    _ ≤ error * (reference + error) + reference * error := by
      exact add_le_add
        (mul_le_mul ha hbUpper hb0 herror)
        (mul_le_mul_of_nonneg_left hb href)
    _ ≤ 2 * (reference + error) * error := by nlinarith

/-- Summing a uniform pairwise approximation over all indices different from
`i` approximates the red intercluster mass by the reduced degree times the
common pair scale. -/
theorem interclusterRedCount_close_reducedDegreeScale_of_pairwise
    (C : ColoredGraph V) (clusters : I → Finset V)
    (R : SimpleGraph I) [DecidableRel R.Adj] (i : I)
    (scale pairError : ℝ) (hpairError : 0 ≤ pairError)
    (hpair : ∀ j, j ≠ i →
      |(C.colorEdgeCountBetween .red (clusters i) (clusters j) : ℝ) -
          (if R.Adj i j then scale else 0)| ≤ pairError) :
    |interclusterRedCount C clusters i - (R.degree i : ℝ) * scale| ≤
      (Fintype.card I : ℝ) * pairError := by
  classical
  have hindicator :
      ∑ j ∈ (Finset.univ : Finset I).erase i,
          (if R.Adj i j then scale else 0) =
        (R.degree i : ℝ) * scale := by
    rw [← Finset.sum_filter]
    have hfilter :
        ((Finset.univ : Finset I).erase i).filter (R.Adj i) =
          R.neighborFinset i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
        and_true, SimpleGraph.mem_neighborFinset]
      constructor
      · exact fun h ↦ h.2
      · intro hij
        exact ⟨(R.ne_of_adj hij).symm, hij⟩
    rw [hfilter]
    simp only [Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree]
  rw [interclusterRedCount, ← hindicator, ← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ (Finset.univ : Finset I).erase i,
        ((C.colorEdgeCountBetween .red (clusters i) (clusters j) : ℝ) -
          (if R.Adj i j then scale else 0))| ≤
        ∑ j ∈ (Finset.univ : Finset I).erase i,
          |(C.colorEdgeCountBetween .red (clusters i) (clusters j) : ℝ) -
            (if R.Adj i j then scale else 0)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ (Finset.univ : Finset I).erase i, pairError := by
      apply Finset.sum_le_sum
      intro j hj
      exact hpair j (Finset.mem_erase.mp hj).1
    _ = (((Finset.univ : Finset I).erase i).card : ℝ) * pairError := by
      simp
    _ ≤ (Fintype.card I : ℝ) * pairError := by
      apply mul_le_mul_of_nonneg_right _ hpairError
      exact_mod_cast Finset.card_le_univ ((Finset.univ : Finset I).erase i)

/-- Red density near one on reduced edges and near zero on reduced nonedges,
together with balance around a common reference size, gives a uniform
pair-count approximation by the reduced adjacency indicator. -/
theorem redPairCount_close_reducedIndicator_of_density
    (C : ColoredGraph V) (clusters : I → Finset V)
    (R : SimpleGraph I) [DecidableRel R.Adj] {i j : I} (hij : i ≠ j)
    (reference sizeError densityError : ℝ)
    (href : 0 ≤ reference) (hsizeError : 0 ≤ sizeError)
    (hdensityError : 0 ≤ densityError)
    (hnonempty : ∀ a, (clusters a).Nonempty)
    (hsize : ∀ a,
      |((clusters a).card : ℝ) - reference| ≤ sizeError)
    (hredEdge : ∀ {a b}, R.Adj a b →
      1 - densityError ≤
        C.colorDensity .red (clusters a) (clusters b))
    (hredNonedge : ∀ {a b}, a ≠ b → ¬ R.Adj a b →
      C.colorDensity .red (clusters a) (clusters b) ≤ densityError) :
    |(C.colorEdgeCountBetween .red (clusters i) (clusters j) : ℝ) -
        (if R.Adj i j then reference ^ 2 else 0)| ≤
      2 * (reference + sizeError) * sizeError +
        densityError * (reference + sizeError) ^ 2 := by
  let a : ℝ := ((clusters i).card : ℝ)
  let b : ℝ := ((clusters j).card : ℝ)
  let e : ℝ :=
    (C.colorEdgeCountBetween .red (clusters i) (clusters j) : ℝ)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have ha := hsize i
  have hb := hsize j
  change |a - reference| ≤ sizeError at ha
  change |b - reference| ≤ sizeError at hb
  have haUpper : a ≤ reference + sizeError := by
    linarith [le_abs_self (a - reference)]
  have hbUpper : b ≤ reference + sizeError := by
    linarith [le_abs_self (b - reference)]
  have hrefError : 0 ≤ reference + sizeError := add_nonneg href hsizeError
  have hprodUpper : a * b ≤ (reference + sizeError) ^ 2 := by
    have := mul_le_mul haUpper hbUpper hb0 hrefError
    nlinarith
  have hprodClose :
      |a * b - reference ^ 2| ≤
        2 * (reference + sizeError) * sizeError :=
    abs_mul_sub_sq_le_of_abs_sub_le ha0 hb0 href hsizeError ha hb
  have hprodPos : 0 < a * b := by
    have hai : 0 < a := by
      dsimp [a]
      exact_mod_cast (Finset.card_pos.mpr (hnonempty i))
    have hbj : 0 < b := by
      dsimp [b]
      exact_mod_cast (Finset.card_pos.mpr (hnonempty j))
    exact mul_pos hai hbj
  by_cases hadj : R.Adj i j
  · rw [if_pos hadj]
    have hdensity := hredEdge hadj
    change 1 - densityError ≤ e / (a * b) at hdensity
    rw [le_div_iff₀ hprodPos] at hdensity
    have hcountUpper : e ≤ a * b := by
      dsimp [e, a, b]
      exact colorEdgeCountBetween_le_card_mul_card_real
        C .red (clusters i) (clusters j)
    have hcountProduct : |e - a * b| ≤ densityError * (a * b) := by
      rw [abs_le]
      constructor <;> nlinarith [mul_nonneg hdensityError (mul_nonneg ha0 hb0)]
    calc
      |e - reference ^ 2| ≤ |e - a * b| + |a * b - reference ^ 2| := by
        have hdecomp : e - reference ^ 2 =
            (e - a * b) + (a * b - reference ^ 2) := by ring
        rw [hdecomp]
        exact abs_add_le _ _
      _ ≤ densityError * (a * b) +
          2 * (reference + sizeError) * sizeError :=
        add_le_add hcountProduct hprodClose
      _ ≤ 2 * (reference + sizeError) * sizeError +
          densityError * (reference + sizeError) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hprodUpper hdensityError
        linarith
  · rw [if_neg hadj, sub_zero, abs_of_nonneg he0]
    have hdensity := hredNonedge hij hadj
    change e / (a * b) ≤ densityError at hdensity
    rw [div_le_iff₀ hprodPos] at hdensity
    have hmul := mul_le_mul_of_nonneg_left hprodUpper hdensityError
    have hsizeTerm :
        0 ≤ 2 * (reference + sizeError) * sizeError := by positivity
    linarith

/-- The second approximation in Stage F8: the red/green reduced-pair
dichotomy and balanced sizes approximate the intercluster red mass by the
reduced degree times the common pair scale. -/
theorem interclusterRedCount_close_reducedDegreeScale_of_density
    (C : ColoredGraph V) (clusters : I → Finset V)
    (R : SimpleGraph I) [DecidableRel R.Adj] (i : I)
    (reference sizeError densityError : ℝ)
    (href : 0 ≤ reference) (hsizeError : 0 ≤ sizeError)
    (hdensityError : 0 ≤ densityError)
    (hnonempty : ∀ a, (clusters a).Nonempty)
    (hsize : ∀ a,
      |((clusters a).card : ℝ) - reference| ≤ sizeError)
    (hredEdge : ∀ {a b}, R.Adj a b →
      1 - densityError ≤
        C.colorDensity .red (clusters a) (clusters b))
    (hredNonedge : ∀ {a b}, a ≠ b → ¬ R.Adj a b →
      C.colorDensity .red (clusters a) (clusters b) ≤ densityError) :
    |interclusterRedCount C clusters i -
        (R.degree i : ℝ) * reference ^ 2| ≤
      (Fintype.card I : ℝ) *
        (2 * (reference + sizeError) * sizeError +
          densityError * (reference + sizeError) ^ 2) := by
  apply interclusterRedCount_close_reducedDegreeScale_of_pairwise
    C clusters R i (reference ^ 2)
      (2 * (reference + sizeError) * sizeError +
        densityError * (reference + sizeError) ^ 2)
  · positivity
  · intro j hji
    exact redPairCount_close_reducedIndicator_of_density
      C clusters R hji.symm reference sizeError densityError
      href hsizeError hdensityError hnonempty hsize hredEdge hredNonedge

/-- Exact form of the first line of the paper's reduced-regularity
calculation: isolate the intercluster red mass from the weighted-degree sum,
the blue-degree sum, and the internal red incidences. -/
theorem interclusterRedCount_eq_weighted_sum_add_blue_sum_sub_internal
    (k : ℕ) (C : ColoredGraph V) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters) (i : I) :
    interclusterRedCount C clusters i =
      (∑ v ∈ clusters i,
          (weightedDegreeIn k C v (clusterUnion clusters) : ℝ)) +
        (delta k : ℝ) *
          (∑ v ∈ clusters i,
            (C.blueDegreeIn v (clusterUnion clusters) : ℝ)) -
        2 * (C.redEdgeCountIn (clusters i) : ℝ) := by
  have hrNat :=
    sum_redDegreeIn_clusterUnion_eq_two_mul_redEdgeCountIn_add_between
      C clusters hdisj i
  have hr := congrArg (fun m : ℕ ↦ (m : ℝ)) hrNat
  push_cast at hr
  have hweighted :
      (∑ v ∈ clusters i,
          (weightedDegreeIn k C v (clusterUnion clusters) : ℝ)) =
        (∑ v ∈ clusters i,
          (C.redDegreeIn v (clusterUnion clusters) : ℝ)) -
          (delta k : ℝ) *
            (∑ v ∈ clusters i,
              (C.blueDegreeIn v (clusterUnion clusters) : ℝ)) := by
    simp only [weightedDegreeIn, Int.cast_sub, Int.cast_natCast, Int.cast_mul,
      Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
  unfold interclusterRedCount
  rw [hweighted]
  linarith

/-- The first approximation in Stage F8.  Pointwise weighted-degree and
blue-degree control, balance around a common reference size, and a bound on
internal red edges give an explicit approximation of the intercluster red
mass by `Δ · reference²`. -/
theorem interclusterRedCount_close_delta_mul_reference_sq
    (k : ℕ) (C : ColoredGraph V) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters) (i : I)
    (reference weightedError blueError sizeError internalRedError : ℝ)
    (href : 0 ≤ reference) (hweightedError : 0 ≤ weightedError)
    (hblueError : 0 ≤ blueError) (hsizeError : 0 ≤ sizeError)
    (hinternalRedError : 0 ≤ internalRedError)
    (hsize : |((clusters i).card : ℝ) - reference| ≤ sizeError)
    (hweighted : ∀ v ∈ clusters i,
      |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
        weightedError)
    (hblue : ∀ v ∈ clusters i,
      |(C.blueDegreeIn v (clusterUnion clusters) : ℝ) - reference| ≤
        blueError)
    (hinternalRed :
      (C.redEdgeCountIn (clusters i) : ℝ) ≤ internalRedError) :
    |interclusterRedCount C clusters i -
        (delta k : ℝ) * reference ^ 2| ≤
      ((clusters i).card : ℝ) * weightedError +
        (delta k : ℝ) *
          (((clusters i).card : ℝ) * blueError +
            reference * sizeError) +
        2 * internalRedError := by
  let a : ℝ := ((clusters i).card : ℝ)
  let Dsum : ℝ :=
    ∑ v ∈ clusters i,
      (weightedDegreeIn k C v (clusterUnion clusters) : ℝ)
  let Bsum : ℝ :=
    ∑ v ∈ clusters i,
      (C.blueDegreeIn v (clusterUnion clusters) : ℝ)
  let redInternal : ℝ := (C.redEdgeCountIn (clusters i) : ℝ)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hdelta0 : 0 ≤ (delta k : ℝ) := by positivity
  have hred0 : 0 ≤ redInternal := by dsimp [redInternal]; positivity
  have hexact :=
    interclusterRedCount_eq_weighted_sum_add_blue_sum_sub_internal
      k C clusters hdisj i
  change interclusterRedCount C clusters i =
    Dsum + (delta k : ℝ) * Bsum - 2 * redInternal at hexact
  have hD : |Dsum| ≤ a * weightedError := by
    exact abs_sum_weightedDegreeIn_clusterUnion_le
      k C clusters i weightedError hweighted
  have hB : |Bsum - a * reference| ≤ a * blueError := by
    have hsum := abs_sum_le_card_mul_of_pointwise_abs_le
      (clusters i)
      (fun v ↦
        (C.blueDegreeIn v (clusterUnion clusters) : ℝ) - reference)
      blueError hblue
    have hsumIdentity :
        Bsum - a * reference =
          ∑ v ∈ clusters i,
            ((C.blueDegreeIn v (clusterUnion clusters) : ℝ) - reference) := by
      dsimp [Bsum, a]
      rw [Finset.sum_sub_distrib]
      simp
    rw [hsumIdentity]
    exact hsum
  have hred : redInternal ≤ internalRedError := by
    exact hinternalRed
  have hdecomp :
      interclusterRedCount C clusters i -
          (delta k : ℝ) * reference ^ 2 =
        Dsum +
          (delta k : ℝ) * (Bsum - a * reference) +
          ((delta k : ℝ) * reference) * (a - reference) +
          (-2 * redInternal) := by
    rw [hexact]
    ring
  rw [hdecomp]
  calc
    |Dsum + (delta k : ℝ) * (Bsum - a * reference) +
        ((delta k : ℝ) * reference) * (a - reference) +
        (-2 * redInternal)| ≤
      |Dsum| + |(delta k : ℝ) * (Bsum - a * reference)| +
        |((delta k : ℝ) * reference) * (a - reference)| +
        |-2 * redInternal| := by
      calc
        |Dsum + (delta k : ℝ) * (Bsum - a * reference) +
            ((delta k : ℝ) * reference) * (a - reference) +
            (-2 * redInternal)| ≤
            |Dsum + (delta k : ℝ) * (Bsum - a * reference) +
              ((delta k : ℝ) * reference) * (a - reference)| +
              |-2 * redInternal| := abs_add_le _ _
        _ ≤ (|Dsum + (delta k : ℝ) * (Bsum - a * reference)| +
              |((delta k : ℝ) * reference) * (a - reference)|) +
              |-2 * redInternal| := by
            have hmiddle :
                |Dsum + (delta k : ℝ) * (Bsum - a * reference) +
                    ((delta k : ℝ) * reference) * (a - reference)| ≤
                  |Dsum + (delta k : ℝ) * (Bsum - a * reference)| +
                    |((delta k : ℝ) * reference) * (a - reference)| :=
              abs_add_le _ _
            linarith
        _ ≤ (|Dsum| + |(delta k : ℝ) * (Bsum - a * reference)| +
              |((delta k : ℝ) * reference) * (a - reference)|) +
              |-2 * redInternal| := by
            have hfirst :
                |Dsum + (delta k : ℝ) * (Bsum - a * reference)| ≤
                  |Dsum| + |(delta k : ℝ) * (Bsum - a * reference)| :=
              abs_add_le _ _
            linarith
    _ = |Dsum| + (delta k : ℝ) * |Bsum - a * reference| +
        ((delta k : ℝ) * reference) * |a - reference| +
        2 * redInternal := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hdelta0, abs_of_nonneg href,
        abs_of_nonneg hred0]
      norm_num
    _ ≤ a * weightedError +
        (delta k : ℝ) * (a * blueError + reference * sizeError) +
        2 * internalRedError := by
      have hblueMul := mul_le_mul_of_nonneg_left hB hdelta0
      have hsizeMul := mul_le_mul_of_nonneg_left hsize
        (mul_nonneg hdelta0 href)
      have hredMul := mul_le_mul_of_nonneg_left hred (by norm_num : (0 : ℝ) ≤ 2)
      linarith

end ReducedDegreeBridge

/-! ## Transparent final-core set identities -/

/-- The exceptional output set from the paper's final step:
`U₀ = retainedᶜ ∪ (A \ U)`. -/
def coreExtractionExceptional {V : Type*} [Fintype V] [DecidableEq V]
    (retained A U : Finset V) : Finset V :=
  retainedᶜ ∪ (A \ U)

/-- Under `U ⊆ A ⊆ retained`, the exceptional set is disjoint from the
nonexceptional cluster union. -/
theorem coreExtractionExceptional_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {retained A U : Finset V} (hUA : U ⊆ A) (hAR : A ⊆ retained) :
    Disjoint (coreExtractionExceptional retained A U) U := by
  rw [Finset.disjoint_left]
  intro v hvExceptional hvU
  rcases Finset.mem_union.mp hvExceptional with hvOutside | hvDiff
  · exact (Finset.mem_compl.mp hvOutside) (hAR (hUA hvU))
  · exact (Finset.mem_sdiff.mp hvDiff).2 hvU

/-- The full core obtained from `U₀ = retainedᶜ ∪ (A \ U)` and `U`
is transparently `retainedᶜ ∪ A`. -/
theorem coreExtractionExceptional_union_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {retained A U : Finset V} (hUA : U ⊆ A) :
    coreExtractionExceptional retained A U ∪ U = retainedᶜ ∪ A := by
  ext v
  simp only [coreExtractionExceptional, Finset.mem_union, Finset.mem_compl,
    Finset.mem_sdiff]
  constructor
  · rintro ((hvOutside | ⟨hvA, _⟩) | hvU)
    · exact Or.inl hvOutside
    · exact Or.inr hvA
    · exact Or.inr (hUA hvU)
  · rintro (hvOutside | hvA)
    · exact Or.inl (Or.inl hvOutside)
    · by_cases hvU : v ∈ U
      · exact Or.inr hvU
      · exact Or.inl (Or.inr ⟨hvA, hvU⟩)

/-- The complement of the full core is exactly the part of `retained` not
covered by `A`. -/
theorem coreExtractionCore_compl_eq_retained_sdiff
    {V : Type*} [Fintype V] [DecidableEq V]
    {retained A U : Finset V} (hUA : U ⊆ A) :
    Finset.univ \ (coreExtractionExceptional retained A U ∪ U) =
      retained \ A := by
  rw [coreExtractionExceptional_union_eq hUA]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_compl]
  tauto

/-- Version of `coreExtractionExceptional_union_eq` phrased through the
paper-facing `coreExtractionCore` definition. -/
theorem coreExtractionCore_eq_retained_compl_union
    {V : Type*} [Fintype V] [DecidableEq V] {l : ℕ}
    {retained A U : Finset V} {clusters : Fin l → Finset V}
    (hUA : U ⊆ A) (hclusters : coreExtractionClusterUnion clusters = U) :
    coreExtractionCore (coreExtractionExceptional retained A U) clusters =
      retainedᶜ ∪ A := by
  rw [coreExtractionCore, hclusters, coreExtractionExceptional_union_eq hUA]

/-- Version of `coreExtractionCore_compl_eq_retained_sdiff` phrased through
the paper-facing `coreExtractionRemainder` definition. -/
theorem coreExtractionRemainder_eq_retained_sdiff
    {V : Type*} [Fintype V] [DecidableEq V] {l : ℕ}
    {retained A U : Finset V} {clusters : Fin l → Finset V}
    (hUA : U ⊆ A) (hclusters : coreExtractionClusterUnion clusters = U) :
    coreExtractionRemainder (coreExtractionExceptional retained A U) clusters =
      retained \ A := by
  rw [coreExtractionRemainder, coreExtractionCore, hclusters]
  exact coreExtractionCore_compl_eq_retained_sdiff hUA

/-- Two natural numbers whose real casts are less than one apart are equal.
This is the integer-gap step used to turn the approximate reduced-degree
identity in the core-extraction argument into an exact identity. -/
theorem nat_eq_of_abs_cast_sub_lt_one {a b : ℕ}
    (h : |(a : ℝ) - (b : ℝ)| < 1) : a = b := by
  apply Nat.le_antisymm
  · by_contra hab
    have hba : b + 1 ≤ a := by omega
    have hba' : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hba
    have hgap : (1 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by linarith
    have habs : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| :=
      hgap.trans (le_abs_self ((a : ℝ) - (b : ℝ)))
    exact (not_le_of_gt h) habs
  · by_contra hab
    have hab' : a + 1 ≤ b := by omega
    have hab'' : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab'
    have hgap : (1 : ℝ) ≤ -((a : ℝ) - (b : ℝ)) := by linarith
    have habs : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| :=
      hgap.trans (neg_le_abs ((a : ℝ) - (b : ℝ)))
    exact (not_le_of_gt h) habs

/-- A scaled form of `nat_eq_of_abs_cast_sub_lt_one`: if the error in an
integer-valued comparison is strictly smaller than one unit of its positive
scale, the two integer values agree exactly. -/
theorem nat_eq_of_scaled_abs_cast_sub_lt {a b : ℕ} {scale error : ℝ}
    (hscale : 0 < scale)
    (hbound : scale * |(a : ℝ) - (b : ℝ)| ≤ error)
    (herror : error < scale) : a = b := by
  apply nat_eq_of_abs_cast_sub_lt_one
  exact lt_of_mul_lt_mul_left
    (by simpa only [mul_one] using hbound.trans_lt herror) hscale.le

/-! ## A fixed parameter hierarchy for core extraction -/

/-- One master constant used throughout core extraction.  Unlike the paper's
changing `C_k`, this is a single explicit number depending only on `k`. -/
def coreExtractionMasterConstant (k : ℕ) : ℝ :=
  10000 * (k + 1 : ℝ) ^ 4

theorem coreExtractionMasterConstant_pos (k : ℕ) :
    0 < coreExtractionMasterConstant k := by
  rw [coreExtractionMasterConstant]
  positivity

theorem one_lt_coreExtractionMasterConstant (k : ℕ) :
    1 < coreExtractionMasterConstant k := by
  rw [coreExtractionMasterConstant]
  have hkNat : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hkNat
  nlinarith [one_le_pow₀ hk (n := 4)]

/-- The direct Erdős--Simonovits modulus used at a seed stage.  For `k = 3`
the red neighborhood has one part and no stability theorem is needed, so the
identity modulus is used.  For `k ≥ 4` this is a choice from the one approved
prior-literature theorem. -/
noncomputable def coreExtractionESModulus (k : ℕ) (ε : ℝ) : ℝ :=
  if hk : 4 ≤ k then
    if hε : 0 < ε then
      Classical.choose
        (PriorLiterature.erdosSimonovitsStability (delta k)
          (by unfold delta; omega) ε hε)
    else 1
  else ε

theorem coreExtractionESModulus_pos {k : ℕ} (hk : 3 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    0 < coreExtractionESModulus k ε := by
  by_cases hk4 : 4 ≤ k
  · rw [coreExtractionESModulus, dif_pos hk4, dif_pos hε]
    exact (Classical.choose_spec
      (PriorLiterature.erdosSimonovitsStability (delta k)
        (by unfold delta; omega) ε hε)).1
  · simp [coreExtractionESModulus, hk4, hε]

/-- The chosen modulus really has the Erdős--Simonovits conclusion.  This is
a choice wrapper, not another assumption. -/
theorem coreExtractionESModulus_spec {k : ℕ} (hk : 4 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        n₀ ≤ Fintype.card V →
        ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
          G.CliqueFree (delta k + 1) →
          (SimpleGraph.turanNumber (Fintype.card V) (delta k) : ℝ) -
                coreExtractionESModulus k ε * (Fintype.card V : ℝ) ^ 2 ≤
              (G.edgeFinset.card : ℝ) →
          ∃ parts : Fin (delta k) → Finset V,
            Set.PairwiseDisjoint (Set.univ : Set (Fin (delta k))) parts ∧
            (Finset.univ : Finset (Fin (delta k))).biUnion parts = Finset.univ ∧
            (∑ i : Fin (delta k),
                ((G.edgeFinset ∩ (parts i).sym2).card : ℝ)) ≤
              ε * (Fintype.card V : ℝ) ^ 2 ∧
            ∀ i : Fin (delta k),
              |((parts i).card : ℝ) -
                  (Fintype.card V : ℝ) / (delta k : ℝ)| ≤
                ε * (Fintype.card V : ℝ) := by
  classical
  rw [coreExtractionESModulus, dif_pos hk, dif_pos hε]
  let δES := Classical.choose
    (PriorLiterature.erdosSimonovitsStability (delta k)
      (by unfold delta; omega) ε hε)
  have hchoice := Classical.choose_spec
    (PriorLiterature.erdosSimonovitsStability (delta k)
      (by unfold delta; omega) ε hε)
  obtain ⟨n₀, hES⟩ := hchoice.2
  exact ⟨n₀,
    PriorLiterature.erdosSimonovitsStabilityFiniteOfFin
      (delta k) ε δES n₀ hES⟩

/-- A positive contraction small enough for one backwards step of the seed
scale hierarchy.  Besides strict decrease, it reserves the square losses in
the local-Turán argument and the chosen Erdős--Simonovits modulus. -/
noncomputable def coreExtractionScaleStep
    (k : ℕ) (η master x : ℝ) : ℝ :=
  min
    (min (x / 2)
      (min ((η * x) ^ 2 / (2 * master))
        (min ((η * coreExtractionESModulus k x) ^ 2 / (2 * master))
          (coreExtractionESModulus k x / 24))))
    (min ((η * x) ^ 2 / (2 * master ^ 2))
      ((η * coreExtractionESModulus k x) ^ 2 / (2 * master ^ 2)))

theorem coreExtractionScaleStep_pos {k : ℕ} (hk : 3 ≤ k)
    {η master x : ℝ} (hη : 0 < η) (hmaster : 0 < master) (hx : 0 < x) :
    0 < coreExtractionScaleStep k η master x := by
  have hES : 0 < coreExtractionESModulus k x :=
    coreExtractionESModulus_pos hk hx
  unfold coreExtractionScaleStep
  refine lt_min ?_ ?_
  · refine lt_min (by positivity) ?_
    refine lt_min (by positivity) ?_
    exact lt_min (by positivity) (by positivity)
  · exact lt_min (by positivity) (by positivity)

theorem coreExtractionScaleStep_lt {k : ℕ} {η master x : ℝ}
    (hx : 0 < x) : coreExtractionScaleStep k η master x < x := by
  exact ((min_le_left _ _).trans (min_le_left _ _)).trans_lt
    (half_lt_self hx)

theorem coreExtractionScaleStep_master_mul_lt {k : ℕ} (hk : 3 ≤ k)
    {η master x : ℝ} (hη : 0 < η) (hmaster : 0 < master) (hx : 0 < x) :
    master * coreExtractionScaleStep k η master x < (η * x) ^ 2 := by
  have hle : coreExtractionScaleStep k η master x ≤
      (η * x) ^ 2 / (2 * master) :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsquare : 0 < (η * x) ^ 2 := sq_pos_of_pos (mul_pos hη hx)
  calc
    master * coreExtractionScaleStep k η master x ≤
        master * ((η * x) ^ 2 / (2 * master)) :=
      mul_le_mul_of_nonneg_left hle hmaster.le
    _ = (η * x) ^ 2 / 2 := by field_simp [hmaster.ne']
    _ < (η * x) ^ 2 := half_lt_self hsquare

theorem coreExtractionScaleStep_ES_master_mul_lt {k : ℕ} (hk : 3 ≤ k)
    {η master x : ℝ} (hη : 0 < η) (hmaster : 0 < master) (hx : 0 < x) :
    master * coreExtractionScaleStep k η master x <
      (η * coreExtractionESModulus k x) ^ 2 := by
  have hES := coreExtractionESModulus_pos hk hx
  have hle : coreExtractionScaleStep k η master x ≤
      (η * coreExtractionESModulus k x) ^ 2 / (2 * master) :=
    (min_le_left _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hsquare : 0 < (η * coreExtractionESModulus k x) ^ 2 :=
    sq_pos_of_pos (mul_pos hη hES)
  calc
    master * coreExtractionScaleStep k η master x ≤
        master * ((η * coreExtractionESModulus k x) ^ 2 / (2 * master)) :=
      mul_le_mul_of_nonneg_left hle hmaster.le
    _ = (η * coreExtractionESModulus k x) ^ 2 / 2 := by
      field_simp [hmaster.ne']
    _ < (η * coreExtractionESModulus k x) ^ 2 := half_lt_self hsquare

/-- Strong square reserve needed when the one fixed master constant replaces
several changing occurrences of the paper's `C_k`. -/
theorem coreExtractionScaleStep_master_sq_mul_lt {k : ℕ} (hk : 3 ≤ k)
    {η master x : ℝ} (hη : 0 < η) (hmaster : 0 < master) (hx : 0 < x) :
    master ^ 2 * coreExtractionScaleStep k η master x < (η * x) ^ 2 := by
  have hle : coreExtractionScaleStep k η master x ≤
      (η * x) ^ 2 / (2 * master ^ 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hmasterSq : 0 < master ^ 2 := sq_pos_of_pos hmaster
  have hsquare : 0 < (η * x) ^ 2 := sq_pos_of_pos (mul_pos hη hx)
  calc
    master ^ 2 * coreExtractionScaleStep k η master x ≤
        master ^ 2 * ((η * x) ^ 2 / (2 * master ^ 2)) :=
      mul_le_mul_of_nonneg_left hle hmasterSq.le
    _ = (η * x) ^ 2 / 2 := by field_simp [hmaster.ne']
    _ < (η * x) ^ 2 := half_lt_self hsquare

/-- Strong Erdős--Simonovits square reserve for the fixed master constant. -/
theorem coreExtractionScaleStep_ES_master_sq_mul_lt {k : ℕ} (hk : 3 ≤ k)
    {η master x : ℝ} (hη : 0 < η) (hmaster : 0 < master) (hx : 0 < x) :
    master ^ 2 * coreExtractionScaleStep k η master x <
      (η * coreExtractionESModulus k x) ^ 2 := by
  have hES := coreExtractionESModulus_pos hk hx
  have hle : coreExtractionScaleStep k η master x ≤
      (η * coreExtractionESModulus k x) ^ 2 / (2 * master ^ 2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmasterSq : 0 < master ^ 2 := sq_pos_of_pos hmaster
  have hsquare : 0 < (η * coreExtractionESModulus k x) ^ 2 :=
    sq_pos_of_pos (mul_pos hη hES)
  calc
    master ^ 2 * coreExtractionScaleStep k η master x ≤
        master ^ 2 *
          ((η * coreExtractionESModulus k x) ^ 2 / (2 * master ^ 2)) :=
      mul_le_mul_of_nonneg_left hle hmasterSq.le
    _ = (η * coreExtractionESModulus k x) ^ 2 / 2 := by
      field_simp [hmaster.ne']
    _ < (η * coreExtractionESModulus k x) ^ 2 := half_lt_self hsquare

theorem twelve_mul_coreExtractionScaleStep_lt_ES {k : ℕ} (hk : 3 ≤ k)
    {η master x : ℝ} (hη : 0 < η) (hmaster : 0 < master) (hx : 0 < x) :
    12 * coreExtractionScaleStep k η master x <
      coreExtractionESModulus k x := by
  have hES := coreExtractionESModulus_pos hk hx
  have hle : coreExtractionScaleStep k η master x ≤
      coreExtractionESModulus k x / 24 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  nlinarith

/-- The backwards sequence obtained by repeatedly applying the scale
contraction, written in increasing order from the initial to terminal scale. -/
noncomputable def coreExtractionScaleSequence
    (k : ℕ) (η master terminal : ℝ) (L : ℕ) : Fin (L + 1) → ℝ :=
  fun q ↦ (coreExtractionScaleStep k η master)^[L - q.1] terminal

theorem coreExtractionScaleSequence_succ
    (k : ℕ) (η master terminal : ℝ) (L : ℕ) (q : Fin L) :
    coreExtractionScaleSequence k η master terminal L q.castSucc =
      coreExtractionScaleStep k η master
        (coreExtractionScaleSequence k η master terminal L q.succ) := by
  unfold coreExtractionScaleSequence
  change (coreExtractionScaleStep k η master)^[L - q.1] terminal =
    coreExtractionScaleStep k η master
      ((coreExtractionScaleStep k η master)^[L - (q.1 + 1)] terminal)
  have hsub : L - q.1 = (L - (q.1 + 1)) + 1 := by omega
  rw [hsub, Function.iterate_succ_apply']

theorem coreExtractionScaleSequence_pos {k : ℕ} (hk : 3 ≤ k)
    {η master terminal : ℝ} (hη : 0 < η) (hmaster : 0 < master)
    (hterminal : 0 < terminal) (L : ℕ) :
    ∀ q, 0 < coreExtractionScaleSequence k η master terminal L q := by
  intro q
  unfold coreExtractionScaleSequence
  have hiterate : ∀ steps : ℕ,
      0 < (coreExtractionScaleStep k η master)^[steps] terminal := by
    intro steps
    induction steps with
    | zero => simpa using hterminal
    | succ steps ih =>
        rw [Function.iterate_succ_apply']
        exact coreExtractionScaleStep_pos hk hη hmaster ih
  exact hiterate _

theorem coreExtractionScaleSequence_strictMono {k : ℕ} (hk : 3 ≤ k)
    {η master terminal : ℝ} (hη : 0 < η) (hmaster : 0 < master)
    (hterminal : 0 < terminal) (L : ℕ) :
    StrictMono (coreExtractionScaleSequence k η master terminal L) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro q
  rw [coreExtractionScaleSequence_succ]
  exact coreExtractionScaleStep_lt
    (coreExtractionScaleSequence_pos hk hη hmaster hterminal L q.succ)

theorem coreExtractionScaleSequence_last
    (k : ℕ) (η master terminal : ℝ) (L : ℕ) :
    coreExtractionScaleSequence k η master terminal L (Fin.last L) = terminal := by
  simp [coreExtractionScaleSequence]

/-- The complete scalar package used by the finite recursion.  It records a
single master constant, a bounded number of seed stages, every scale from the
initial through terminal stage, the mixed-mass threshold and constant,
and a fixed weighted-degree tail scale.

`tailScale` is deliberately fixed before the input `δ` is quantified.  Thus
`weightedDegreeTails` is applied once at `tailScale`; an input
`δ < finalDelta₀ ≤ tailScale` supplies the stronger objective hypothesis.
The resulting threshold is uniform in the input near-extremality parameter,
as required by paper Lemma `lemma:kth-order-recursion`. -/
structure CoreExtractionParameters (k : ℕ) (η ζ : ℝ) where
  /-- The single replacement for every occurrence of the paper's `C_k`. -/
  master : ℝ
  master_eq : master = coreExtractionMasterConstant k
  master_pos : 0 < master
  /-- Uniform lower cluster-size coefficient; this depends only on `k,η`. -/
  clusterScale : ℝ
  clusterScale_eq : clusterScale = η / (2 * master)
  clusterScale_pos : 0 < clusterScale
  /-- Input `beta` passed to `vertexLevelMixedMass`. -/
  mixedInput : ℝ
  mixedInput_pos : 0 < mixedInput
  mixedInput_lt_threshold :
    mixedInput < dominantColorBeta₀ k (η / master)
  /-- Strict error reserve for the raw `ζ`-level recursion. -/
  mixedError_lt :
    dominantColorConstant k * Real.sqrt mixedInput / (η / master) ^ 2 < ζ / 20
  /-- A stronger density-error reserve for the integer gap in reduced-degree
  regularity. -/
  mixedError_regularity :
    dominantColorConstant k * Real.sqrt mixedInput / (η / master) ^ 2 <
      η ^ 4 / master ^ 4
  /-- The continuation threshold of the bounded seed iteration. -/
  tau : ℝ
  tau_pos : 0 < tau
  tau_lt_one : tau < 1
  tau_lt_zeta : tau < ζ / 100
  /-- The stronger output-budget form actually supplied by the construction.
  Keeping the master factor here absorbs every fixed `k`-dependent
  multiplicity in the terminal quotient and boundary estimates. -/
  master_mul_tau_lt_zeta : master * tau < ζ / 100
  tau_lt_eta : master * tau < η / 100
  /-- A high-power reserve for the explicit reduced-degree error. -/
  tau_regularity : master * tau < η ^ 6 / master ^ 4
  mixedInput_eq : mixedInput = master * tau
  /-- A strict natural bound for all successful seed stages. -/
  stageBound : ℕ
  stageBound_pos : 0 < stageBound
  stageBound_covers : master / tau + 1 < stageBound
  /-- The hierarchy `β₀ < ⋯ < β_L`, including both endpoints. -/
  betaSeq : Fin (stageBound + 1) → ℝ
  betaSeq_pos : ∀ q, 0 < betaSeq q
  betaSeq_strictMono : StrictMono betaSeq
  betaSeq_lt_tau : ∀ q, betaSeq q < tau
  /-- Square reserve used to pass from one local-Turán scale to the next. -/
  betaStep_square : ∀ q : Fin stageBound,
    master * betaSeq q.castSucc < (η * betaSeq q.succ) ^ 2
  /-- Fixed-master strengthening of the preceding reserve. -/
  betaStep_square_strong : ∀ q : Fin stageBound,
    master ^ 2 * betaSeq q.castSucc < (η * betaSeq q.succ) ^ 2
  /-- Square reserve involving the actual chosen ES modulus. -/
  betaStep_ES_square : ∀ q : Fin stageBound,
    master * betaSeq q.castSucc <
      (η * coreExtractionESModulus k (betaSeq q.succ)) ^ 2
  /-- Fixed-master strengthening for the local-Turán approximate maximum. -/
  betaStep_ES_square_strong : ∀ q : Fin stageBound,
    master ^ 2 * betaSeq q.castSucc <
      (η * coreExtractionESModulus k (betaSeq q.succ)) ^ 2
  /-- Linear reserve that directly discharges the `12 β_q` ES comparison. -/
  betaStep_ES_linear : ∀ q : Fin stageBound,
    12 * betaSeq q.castSucc < coreExtractionESModulus k (betaSeq q.succ)
  /-- Terminal overlap/quotient loss, including the finite stage bound. -/
  betaLast_overlap :
    master * (stageBound + 1 : ℝ) ^ 2 *
        Real.sqrt (betaSeq (Fin.last stageBound)) < tau / 2
  /-- A stronger terminal reserve for the per-cluster errors entering the
  reduced-degree bridge.  The extra `η` is essential when the input density
  parameter is arbitrarily small. -/
  betaLast_overlap_strong :
    master * (stageBound + 1 : ℝ) ^ 2 *
        Real.sqrt (betaSeq (Fin.last stageBound)) < η * tau / 100000
  betaLast_sixth :
    master * betaSeq (Fin.last stageBound) < tau ^ 6
  /-- Fixed parameter at which the corrected weighted-degree tails are run. -/
  tailScale : ℝ
  tailScale_mem : tailScale ∈ Set.Ioo (0 : ℝ) 1
  /-- Final near-extremality range, kept below the fixed tail parameter. -/
  finalDelta₀ : ℝ
  finalDelta₀_mem : finalDelta₀ ∈ Set.Ioo (0 : ℝ) 1
  finalDelta₀_le_tailScale : finalDelta₀ ≤ tailScale
  /-- Exceptional-set reserve at the fixed tail scale. -/
  tail_exceptional :
    10 * (delta k : ℝ) * tailScale ^ (1 / 4 : ℝ) ≤ (betaSeq 0) ^ 4
  /-- Restricted weighted-degree reserve. -/
  tail_restricted :
    12 * (delta k : ℝ) ^ 2 * tailScale ^ (1 / 4 : ℝ) ≤ betaSeq 0

theorem dominantColorConstant_eq_two_hundred_mul (k : ℕ) :
    dominantColorConstant k = 200 * k := by
  simp [dominantColorConstant, mixedMassConstant]
  ring

set_option maxHeartbeats 800000 in
-- The nested minima and full backwards hierarchy make this construction costly to elaborate.
/-- Existence of a complete, explicit core-extraction parameter package.

The outer witness `c = η / (2 * coreExtractionMasterConstant k)` is chosen
before `ζ`; consequently the eventual paper-facing cluster lower bound is
uniform in its error parameter.  The mixed input uses the actual threshold
`dominantColorBeta₀` and actual constant
`dominantColorConstant k = 200 * k`.  The scale hierarchy includes all
indices `0,…,L`, and its backwards construction uses the chosen
Erdős--Simonovits modulus at every adjacent pair.

The tail theorem is applied at one fixed scale; the mixed-mass threshold
is strict, and the output error allocation is explicit. -/
theorem exists_coreExtractionParameters (k : ℕ) (hk : 3 ≤ k)
    (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ζ ∈ Set.Ioo (0 : ℝ) (η / 60),
        ∃ P : CoreExtractionParameters k η ζ, P.clusterScale = c := by
  let K := coreExtractionMasterConstant k
  have hK : 0 < K := coreExtractionMasterConstant_pos k
  have hKone : 1 < K := one_lt_coreExtractionMasterConstant k
  let c := η / (2 * K)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos hη.1 (mul_pos (by norm_num) hK)
  refine ⟨c, hc, ?_⟩
  intro ζ hζ
  have hηKpos : 0 < η / K := div_pos hη.1 hK
  have hηKlt : η / K < 1 := by
    have hηKltη : η / K < η := by
      rw [div_lt_iff₀ hK]
      nlinarith [mul_pos hη.1 (sub_pos.2 hKone)]
    exact hηKltη.trans hη.2
  have hηK : η / K ∈ Set.Ioo (0 : ℝ) 1 := ⟨hηKpos, hηKlt⟩
  let mixedThreshold := dominantColorBeta₀ k (η / K)
  have hmixedThreshold : 0 < mixedThreshold := by
    dsimp [mixedThreshold]
    exact dominantColorBeta₀_pos hk hηK
  let D := dominantColorConstant k
  have hDone : 1 ≤ D := by
    dsimp [D]
    exact dominantColorConstant_ge_one hk
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hDone
  let errorRoot := (ζ / 20) * (η / K) ^ 2 / D
  have herrorRoot : 0 < errorRoot := by
    dsimp [errorRoot]
    exact div_pos
      (mul_pos (div_pos hζ.1 (by norm_num)) (sq_pos_of_pos hηKpos)) hD
  let regularityRoot := (η ^ 4 / K ^ 4) * (η / K) ^ 2 / D
  have hregularityRoot : 0 < regularityRoot := by
    dsimp [regularityRoot]
    exact div_pos
      (mul_pos (div_pos (pow_pos hη.1 4) (pow_pos hK 4))
        (sq_pos_of_pos hηKpos)) hD
  let tauRegularityCap := η ^ 6 / K ^ 4
  have htauRegularityCap : 0 < tauRegularityCap := by
    dsimp [tauRegularityCap]
    exact div_pos (pow_pos hη.1 6) (pow_pos hK 4)
  let mixedCap :=
    min mixedThreshold
      (min (errorRoot ^ 2)
        (min (regularityRoot ^ 2)
          (min (ζ / 100) (min (η / 100) tauRegularityCap))))
  have hmixedCap : 0 < mixedCap := by
    dsimp [mixedCap]
    simp only [lt_min_iff]
    exact ⟨hmixedThreshold, sq_pos_of_pos herrorRoot,
      sq_pos_of_pos hregularityRoot, div_pos hζ.1 (by norm_num),
      div_pos hη.1 (by norm_num), htauRegularityCap⟩
  let betaMix := mixedCap / 2
  have hbetaMix : 0 < betaMix := div_pos hmixedCap (by norm_num)
  have hbetaMixCap : betaMix < mixedCap := by
    dsimp [betaMix]
    exact half_lt_self hmixedCap
  have hbetaMixThreshold : betaMix < dominantColorBeta₀ k (η / K) := by
    exact hbetaMixCap.trans_le (min_le_left _ _)
  have hbetaMixErrorSq : betaMix < errorRoot ^ 2 := by
    exact hbetaMixCap.trans_le (by simp [mixedCap])
  have hbetaMixRegularitySq : betaMix < regularityRoot ^ 2 := by
    exact hbetaMixCap.trans_le (by simp [mixedCap])
  have hsqrtBetaMix : Real.sqrt betaMix < errorRoot :=
    (Real.sqrt_lt' herrorRoot).2 hbetaMixErrorSq
  have hmixedError :
      dominantColorConstant k * Real.sqrt betaMix / (η / K) ^ 2 < ζ / 20 := by
    have hηKsq : 0 < (η / K) ^ 2 := sq_pos_of_pos hηKpos
    rw [div_lt_iff₀ hηKsq]
    calc
      dominantColorConstant k * Real.sqrt betaMix <
          dominantColorConstant k * errorRoot :=
        mul_lt_mul_of_pos_left hsqrtBetaMix hD
      _ = (ζ / 20) * (η / K) ^ 2 := by
        simpa [errorRoot, D] using
          (mul_div_cancel₀ ((ζ / 20) * (η / K) ^ 2) hD.ne')
  have hsqrtBetaMixRegularity : Real.sqrt betaMix < regularityRoot :=
    (Real.sqrt_lt' hregularityRoot).2 hbetaMixRegularitySq
  have hmixedRegularity :
      dominantColorConstant k * Real.sqrt betaMix / (η / K) ^ 2 <
        η ^ 4 / K ^ 4 := by
    have hηKsq : 0 < (η / K) ^ 2 := sq_pos_of_pos hηKpos
    rw [div_lt_iff₀ hηKsq]
    calc
      dominantColorConstant k * Real.sqrt betaMix <
          dominantColorConstant k * regularityRoot :=
        mul_lt_mul_of_pos_left hsqrtBetaMixRegularity hD
      _ = (η ^ 4 / K ^ 4) * (η / K) ^ 2 := by
        simpa [regularityRoot, D] using
          (mul_div_cancel₀ ((η ^ 4 / K ^ 4) * (η / K) ^ 2) hD.ne')
  have hbetaMixZeta : betaMix < ζ / 100 := by
    exact hbetaMixCap.trans_le (by simp [mixedCap])
  have hbetaMixEta : betaMix < η / 100 := by
    exact hbetaMixCap.trans_le (by simp [mixedCap])
  have hbetaMixTauRegularity : betaMix < η ^ 6 / K ^ 4 := by
    exact hbetaMixCap.trans_le (by simp [mixedCap, tauRegularityCap])
  let τ := betaMix / K
  have hτ : 0 < τ := div_pos hbetaMix hK
  have hτBeta : τ < betaMix := by
    dsimp [τ]
    rw [div_lt_iff₀ hK]
    nlinarith [mul_pos hbetaMix (sub_pos.2 hKone)]
  have hτone : τ < 1 := by
    have hthresholdOne : dominantColorBeta₀ k (η / K) ≤ 1 := min_le_left _ _
    exact hτBeta.trans (hbetaMixThreshold.trans_le hthresholdOne)
  have hτZeta : τ < ζ / 100 := hτBeta.trans hbetaMixZeta
  have hKτ : K * τ = betaMix := by
    dsimp [τ]
    field_simp [hK.ne']
  have hKτZeta : K * τ < ζ / 100 := by
    rw [hKτ]
    exact hbetaMixZeta
  have hτEta : K * τ < η / 100 := hKτ.trans_lt hbetaMixEta
  have hτRegularity : K * τ < η ^ 6 / K ^ 4 :=
    hKτ.trans_lt hbetaMixTauRegularity
  obtain ⟨L, hL⟩ := exists_nat_gt (K / τ + 1)
  have hLpos : 0 < L := by
    by_contra hnot
    have hLzero : L = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hLzero] at hL
    norm_num at hL
    have : 0 < K / τ := div_pos hK hτ
    linarith
  let terminalRoot :=
    η * τ / (200000 * K * (L + 1 : ℝ) ^ 2)
  have hterminalRoot : 0 < terminalRoot := by
    dsimp [terminalRoot]
    exact div_pos (mul_pos hη.1 hτ)
      (mul_pos (mul_pos (by norm_num) hK)
        (sq_pos_of_pos (by positivity)))
  let terminal :=
    min (τ / 2)
      (min (τ ^ 6 / (2 * K)) (terminalRoot ^ 2 / 2))
  have hterminal : 0 < terminal := by
    dsimp [terminal]
    simp only [lt_min_iff]
    exact ⟨div_pos hτ (by norm_num),
      div_pos (pow_pos hτ 6) (mul_pos (by norm_num) hK),
      div_pos (sq_pos_of_pos hterminalRoot) (by norm_num)⟩
  have hterminalTau : terminal < τ := by
    exact (min_le_left _ _).trans_lt (half_lt_self hτ)
  have hterminalSixth : K * terminal < τ ^ 6 := by
    have hle : terminal ≤ τ ^ 6 / (2 * K) :=
      (min_le_right _ _).trans (min_le_left _ _)
    calc
      K * terminal ≤ K * (τ ^ 6 / (2 * K)) :=
        mul_le_mul_of_nonneg_left hle hK.le
      _ = τ ^ 6 / 2 := by field_simp [hK.ne']
      _ < τ ^ 6 := half_lt_self (pow_pos hτ 6)
  have hterminalRootSq : terminal < terminalRoot ^ 2 := by
    have hle : terminal ≤ terminalRoot ^ 2 / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    exact hle.trans_lt (half_lt_self (sq_pos_of_pos hterminalRoot))
  have hsqrtTerminal : Real.sqrt terminal < terminalRoot :=
    (Real.sqrt_lt' hterminalRoot).2 hterminalRootSq
  have hterminalOverlapStrong :
      K * (L + 1 : ℝ) ^ 2 * Real.sqrt terminal < η * τ / 100000 := by
    have hcoef : 0 < K * (L + 1 : ℝ) ^ 2 := by positivity
    have hmul := mul_lt_mul_of_pos_left hsqrtTerminal hcoef
    dsimp [terminalRoot] at hmul
    have hscaled :
        K * (L + 1 : ℝ) ^ 2 *
            (η * τ / (200000 * K * (L + 1 : ℝ) ^ 2)) =
          η * τ / 200000 := by
      field_simp [hK.ne']
    rw [hscaled] at hmul
    have hητ : 0 < η * τ := mul_pos hη.1 hτ
    exact hmul.trans (by nlinarith)
  have hterminalOverlap :
      K * (L + 1 : ℝ) ^ 2 * Real.sqrt terminal < τ / 2 := by
    refine hterminalOverlapStrong.trans ?_
    have hητ : η * τ < τ := by
      nlinarith [mul_pos (sub_pos.mpr hη.2) hτ]
    calc
      η * τ / 100000 < τ / 100000 := by
        nlinarith only [hητ]
      _ < τ / 2 := by
        nlinarith only [hτ]
  let betaSeq := coreExtractionScaleSequence k η K terminal L
  have hbetaSeqPos : ∀ q, 0 < betaSeq q := by
    dsimp [betaSeq]
    exact coreExtractionScaleSequence_pos hk hη.1 hK hterminal L
  have hbetaSeqMono : StrictMono betaSeq := by
    dsimp [betaSeq]
    exact coreExtractionScaleSequence_strictMono hk hη.1 hK hterminal L
  have hbetaLast : betaSeq (Fin.last L) = terminal := by
    dsimp [betaSeq]
    exact coreExtractionScaleSequence_last k η K terminal L
  have hbetaSeqTau : ∀ q, betaSeq q < τ := by
    intro q
    exact (hbetaSeqMono.monotone (Fin.le_last q)).trans_lt
      (hbetaLast.trans_lt hterminalTau)
  have hbetaStepSquare : ∀ q : Fin L,
      K * betaSeq q.castSucc < (η * betaSeq q.succ) ^ 2 := by
    intro q
    dsimp [betaSeq]
    rw [coreExtractionScaleSequence_succ]
    exact coreExtractionScaleStep_master_mul_lt hk hη.1 hK
      (coreExtractionScaleSequence_pos hk hη.1 hK hterminal L q.succ)
  have hbetaStepSquareStrong : ∀ q : Fin L,
      K ^ 2 * betaSeq q.castSucc < (η * betaSeq q.succ) ^ 2 := by
    intro q
    dsimp [betaSeq]
    rw [coreExtractionScaleSequence_succ]
    exact coreExtractionScaleStep_master_sq_mul_lt hk hη.1 hK
      (coreExtractionScaleSequence_pos hk hη.1 hK hterminal L q.succ)
  have hbetaStepESSquare : ∀ q : Fin L,
      K * betaSeq q.castSucc <
        (η * coreExtractionESModulus k (betaSeq q.succ)) ^ 2 := by
    intro q
    dsimp [betaSeq]
    rw [coreExtractionScaleSequence_succ]
    exact coreExtractionScaleStep_ES_master_mul_lt hk hη.1 hK
      (coreExtractionScaleSequence_pos hk hη.1 hK hterminal L q.succ)
  have hbetaStepESSquareStrong : ∀ q : Fin L,
      K ^ 2 * betaSeq q.castSucc <
        (η * coreExtractionESModulus k (betaSeq q.succ)) ^ 2 := by
    intro q
    dsimp [betaSeq]
    rw [coreExtractionScaleSequence_succ]
    exact coreExtractionScaleStep_ES_master_sq_mul_lt hk hη.1 hK
      (coreExtractionScaleSequence_pos hk hη.1 hK hterminal L q.succ)
  have hbetaStepESLinear : ∀ q : Fin L,
      12 * betaSeq q.castSucc < coreExtractionESModulus k (betaSeq q.succ) := by
    intro q
    dsimp [betaSeq]
    rw [coreExtractionScaleSequence_succ]
    exact twelve_mul_coreExtractionScaleStep_lt_ES hk hη.1 hK
      (coreExtractionScaleSequence_pos hk hη.1 hK hterminal L q.succ)
  let betaInit := betaSeq 0
  have hbetaInit : 0 < betaInit := hbetaSeqPos 0
  have hdeltaNat : 0 < delta k := by
    rw [delta]
    omega
  have hdeltaReal : 0 < (delta k : ℝ) := by exact_mod_cast hdeltaNat
  let tailRoot :=
    min (1 / 2 : ℝ)
      (min (betaInit ^ 4 / (20 * (delta k : ℝ)))
        (betaInit / (24 * (delta k : ℝ) ^ 2)))
  have htailRoot : 0 < tailRoot := by
    dsimp [tailRoot]
    simp only [lt_min_iff]
    exact ⟨by norm_num, by positivity, by positivity⟩
  have htailRootOne : tailRoot < 1 :=
    (min_le_left _ _).trans_lt (by norm_num)
  let tailScale := tailRoot ^ 4
  have htailScale : 0 < tailScale := pow_pos htailRoot 4
  have htailScaleOne : tailScale < 1 := by
    dsimp [tailScale]
    exact pow_lt_one₀ htailRoot.le htailRootOne (by norm_num)
  have htailQuarter : tailScale ^ (1 / 4 : ℝ) = tailRoot := by
    dsimp [tailScale]
    simpa [one_div] using
      Real.pow_rpow_inv_natCast htailRoot.le (by norm_num : (4 : ℕ) ≠ 0)
  have htailExceptional :
      10 * (delta k : ℝ) * tailScale ^ (1 / 4 : ℝ) ≤ betaInit ^ 4 := by
    rw [htailQuarter]
    have hle : tailRoot ≤ betaInit ^ 4 / (20 * (delta k : ℝ)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    calc
      10 * (delta k : ℝ) * tailRoot ≤
          10 * (delta k : ℝ) *
            (betaInit ^ 4 / (20 * (delta k : ℝ))) :=
        mul_le_mul_of_nonneg_left hle
          (mul_nonneg (by norm_num) hdeltaReal.le)
      _ = betaInit ^ 4 / 2 := by field_simp [hdeltaReal.ne']; ring
      _ ≤ betaInit ^ 4 := (half_le_self (pow_nonneg hbetaInit.le 4))
  have htailRestricted :
      12 * (delta k : ℝ) ^ 2 * tailScale ^ (1 / 4 : ℝ) ≤ betaInit := by
    rw [htailQuarter]
    have hle : tailRoot ≤ betaInit / (24 * (delta k : ℝ) ^ 2) :=
      (min_le_right _ _).trans (min_le_right _ _)
    calc
      12 * (delta k : ℝ) ^ 2 * tailRoot ≤
          12 * (delta k : ℝ) ^ 2 *
            (betaInit / (24 * (delta k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hle
          (mul_nonneg (by norm_num) (sq_nonneg (delta k : ℝ)))
      _ = betaInit / 2 := by field_simp [hdeltaReal.ne']; ring
      _ ≤ betaInit := half_le_self hbetaInit.le
  let finalDelta₀ := tailScale / 2
  have hfinalDelta₀ : 0 < finalDelta₀ := div_pos htailScale (by norm_num)
  have hfinalDelta₀One : finalDelta₀ < 1 :=
    (half_lt_self htailScale).trans htailScaleOne
  have hfinalDelta₀Tail : finalDelta₀ ≤ tailScale := by
    dsimp [finalDelta₀]
    linarith
  let P : CoreExtractionParameters k η ζ := {
    master := K
    master_eq := rfl
    master_pos := hK
    clusterScale := c
    clusterScale_eq := rfl
    clusterScale_pos := hc
    mixedInput := betaMix
    mixedInput_pos := hbetaMix
    mixedInput_lt_threshold := hbetaMixThreshold
    mixedError_lt := hmixedError
    mixedError_regularity := hmixedRegularity
    tau := τ
    tau_pos := hτ
    tau_lt_one := hτone
    tau_lt_zeta := hτZeta
    master_mul_tau_lt_zeta := hKτZeta
    tau_lt_eta := hτEta
    tau_regularity := hτRegularity
    mixedInput_eq := hKτ.symm
    stageBound := L
    stageBound_pos := hLpos
    stageBound_covers := hL
    betaSeq := betaSeq
    betaSeq_pos := hbetaSeqPos
    betaSeq_strictMono := hbetaSeqMono
    betaSeq_lt_tau := hbetaSeqTau
    betaStep_square := hbetaStepSquare
    betaStep_square_strong := hbetaStepSquareStrong
    betaStep_ES_square := hbetaStepESSquare
    betaStep_ES_square_strong := hbetaStepESSquareStrong
    betaStep_ES_linear := hbetaStepESLinear
    betaLast_overlap := by simpa [hbetaLast] using hterminalOverlap
    betaLast_overlap_strong := by
      simpa [hbetaLast] using hterminalOverlapStrong
    betaLast_sixth := by simpa [hbetaLast] using hterminalSixth
    tailScale := tailScale
    tailScale_mem := ⟨htailScale, htailScaleOne⟩
    finalDelta₀ := finalDelta₀
    finalDelta₀_mem := ⟨hfinalDelta₀, hfinalDelta₀One⟩
    finalDelta₀_le_tailScale := hfinalDelta₀Tail
    tail_exceptional := by simpa [betaInit] using htailExceptional
    tail_restricted := by simpa [betaInit] using htailRestricted
  }
  exact ⟨P, rfl⟩

namespace CoreExtractionParameters

/-- The explicit real error attached to hierarchy level `q`, including one
constant slot for all ceiling and deleted-seed losses. -/
noncomputable def levelError {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ) (q : Fin (P.stageBound + 1))
    (n : ℕ) : ℝ :=
  (P.master / 100) * Real.sqrt (P.betaSeq q) * (n : ℝ) + P.master

/-- The common error used after all stage-dependent estimates have been
weakened to the terminal hierarchy level. -/
noncomputable def terminalError {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ) (n : ℕ) : ℝ :=
  P.levelError (Fin.last P.stageBound) n

theorem levelError_pos {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ)
    (q : Fin (P.stageBound + 1)) (n : ℕ) :
    0 < P.levelError q n := by
  unfold levelError
  have hnonneg :
      0 ≤ (P.master / 100) * Real.sqrt (P.betaSeq q) * (n : ℝ) :=
    mul_nonneg
      (mul_nonneg (div_nonneg P.master_pos.le (by norm_num))
        (Real.sqrt_nonneg _))
      (Nat.cast_nonneg n)
  linarith [P.master_pos]

theorem levelError_mono {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ)
    {q r : Fin (P.stageBound + 1)} (hqr : q ≤ r) (n : ℕ) :
    P.levelError q n ≤ P.levelError r n := by
  unfold levelError
  have hbeta : P.betaSeq q ≤ P.betaSeq r :=
    P.betaSeq_strictMono.monotone hqr
  have hsqrt : Real.sqrt (P.betaSeq q) ≤ Real.sqrt (P.betaSeq r) :=
    Real.sqrt_le_sqrt hbeta
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmaster : 0 ≤ P.master / 100 :=
    div_nonneg P.master_pos.le (by norm_num)
  gcongr

theorem levelError_le_terminal {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ)
    (q : Fin (P.stageBound + 1)) (n : ℕ) :
    P.levelError q n ≤ P.terminalError n := by
  exact P.levelError_mono (Fin.le_last q) n

theorem betaSeq_lt_one {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ)
    (q : Fin (P.stageBound + 1)) : P.betaSeq q < 1 :=
  (P.betaSeq_lt_tau q).trans P.tau_lt_one

theorem betaSeq_le_sqrt {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ)
    (q : Fin (P.stageBound + 1)) :
    P.betaSeq q ≤ Real.sqrt (P.betaSeq q) := by
  have hβ0 := (P.betaSeq_pos q).le
  have hβ1 := P.betaSeq_lt_one q
  have hsqrt0 := Real.sqrt_nonneg (P.betaSeq q)
  have hsqrtSq := Real.sq_sqrt hβ0
  have hsqrt1 : Real.sqrt (P.betaSeq q) ≤ 1 := by
    exact (Real.sqrt_le_one).2 hβ1.le
  nlinarith

/-- The fixed near-extremality parameter used by every local-Turán call in
the seed iteration.  The second summand absorbs the objective loss from the
one-time tail cleaning. -/
noncomputable def localDelta {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ) : ℝ :=
  P.tailScale + (P.betaSeq 0) ^ 4

/-- The common local-Turán parameter lies in `(0,1)`.  The upper bound uses
the corrected tail exceptional-set reserve and the much stronger
`master * tau < eta / 100` hierarchy bound. -/
theorem localDelta_mem {k : ℕ} (hk : 3 ≤ k) {η ζ : ℝ}
    (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k η ζ) :
    P.localDelta ∈ Set.Ioo (0 : ℝ) 1 := by
  have hmasterOne : 1 ≤ P.master := by
    rw [P.master_eq]
    exact (one_lt_coreExtractionMasterConstant k).le
  have htauLe : P.tau ≤ P.master * P.tau := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmasterOne) P.tau_pos.le]
  have htauHundred : P.tau < 1 / 100 := by
    calc
      P.tau ≤ P.master * P.tau := htauLe
      _ < η / 100 := P.tau_lt_eta
      _ < 1 / 100 := div_lt_div_of_pos_right hη.2 (by norm_num)
  have hbetaPos : 0 < P.betaSeq 0 := P.betaSeq_pos 0
  have hbetaHundred : P.betaSeq 0 < 1 / 100 :=
    (P.betaSeq_lt_tau 0).trans htauHundred
  have hbetaOne : P.betaSeq 0 ≤ 1 := by linarith
  have hbetaFourthLe : (P.betaSeq 0) ^ 4 ≤ P.betaSeq 0 := by
    have hsqLe : (P.betaSeq 0) ^ 2 ≤ P.betaSeq 0 := by
      nlinarith [mul_nonneg hbetaPos.le (sub_nonneg.mpr hbetaOne)]
    have hsqOne : (P.betaSeq 0) ^ 2 ≤ 1 := hsqLe.trans hbetaOne
    have hfourthLeSq : ((P.betaSeq 0) ^ 2) ^ 2 ≤
        (P.betaSeq 0) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (P.betaSeq 0))
        (sub_nonneg.mpr hsqOne)]
    nlinarith
  let root := P.tailScale ^ (1 / 4 : ℝ)
  have hrootPos : 0 < root := by
    exact quarterPower_pos P.tailScale_mem.1
  have hdeltaReal : (1 : ℝ) ≤ (delta k : ℝ) := by
    exact_mod_cast (show 1 ≤ delta k by unfold delta; omega)
  have hcoefficient : 1 < 10 * (delta k : ℝ) := by nlinarith
  have hrootLtScaled : root < 10 * (delta k : ℝ) * root := by
    nlinarith [mul_pos (sub_pos.mpr hcoefficient) hrootPos]
  have hrootLtBeta : root < (P.betaSeq 0) ^ 4 :=
    hrootLtScaled.trans_le (by simpa [root] using P.tail_exceptional)
  have hrootOne : root ≤ 1 := by
    exact ((hrootLtBeta.trans_le hbetaFourthLe).trans_le hbetaOne).le
  have hrootFourthLe : root ^ 4 ≤ root := by
    have hsqLe : root ^ 2 ≤ root := by
      nlinarith [mul_nonneg hrootPos.le (sub_nonneg.mpr hrootOne)]
    have hsqOne : root ^ 2 ≤ 1 := hsqLe.trans hrootOne
    have hfourthLeSq : (root ^ 2) ^ 2 ≤ root ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg root) (sub_nonneg.mpr hsqOne)]
    nlinarith
  have htailEq : root ^ 4 = P.tailScale := by
    simpa [root] using quarterPower_fourth P.tailScale_mem.1.le
  have htailLtBeta : P.tailScale < (P.betaSeq 0) ^ 4 := by
    rw [← htailEq]
    exact hrootFourthLe.trans_lt hrootLtBeta
  constructor
  · unfold localDelta
    exact add_pos P.tailScale_mem.1 (pow_pos hbetaPos 4)
  · unfold localDelta
    have hsumBeta :
        P.tailScale + (P.betaSeq 0) ^ 4 < 2 * P.betaSeq 0 := by
      nlinarith
    linarith

/-- The cleaning scale itself is dominated by the initial fourth-power
reserve. -/
theorem tailScale_le_betaSeq_zero_fourth {k : ℕ} (hk : 3 ≤ k)
    {η ζ : ℝ} (P : CoreExtractionParameters k η ζ) :
    P.tailScale ≤ (P.betaSeq 0) ^ 4 := by
  let root := P.tailScale ^ (1 / 4 : ℝ)
  have hrootPos : 0 < root := quarterPower_pos P.tailScale_mem.1
  have hdeltaReal : (1 : ℝ) ≤ (delta k : ℝ) := by
    exact_mod_cast (show 1 ≤ delta k by unfold delta; omega)
  have hrootLeScaled : root ≤ 10 * (delta k : ℝ) * root := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr (by nlinarith : (1 : ℝ) ≤ 10 * (delta k : ℝ)))
      hrootPos.le]
  have hrootLeBeta : root ≤ (P.betaSeq 0) ^ 4 :=
    hrootLeScaled.trans (by simpa [root] using P.tail_exceptional)
  have hbetaOne : P.betaSeq 0 ≤ 1 := (P.betaSeq_lt_one 0).le
  have hbetaFourthLe : (P.betaSeq 0) ^ 4 ≤ P.betaSeq 0 := by
    have hsqLe : (P.betaSeq 0) ^ 2 ≤ P.betaSeq 0 := by
      nlinarith [mul_nonneg (P.betaSeq_pos 0).le (sub_nonneg.mpr hbetaOne)]
    have hsqOne : (P.betaSeq 0) ^ 2 ≤ 1 := hsqLe.trans hbetaOne
    have hfourthLeSq : ((P.betaSeq 0) ^ 2) ^ 2 ≤
        (P.betaSeq 0) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (P.betaSeq 0))
        (sub_nonneg.mpr hsqOne)]
    nlinarith
  have hrootOne : root ≤ 1 :=
    (hrootLeBeta.trans hbetaFourthLe).trans hbetaOne
  have hrootFourthLe : root ^ 4 ≤ root := by
    have hsqLe : root ^ 2 ≤ root := by
      nlinarith [mul_nonneg hrootPos.le (sub_nonneg.mpr hrootOne)]
    have hsqOne : root ^ 2 ≤ 1 := hsqLe.trans hrootOne
    have hfourthLeSq : (root ^ 2) ^ 2 ≤ root ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg root) (sub_nonneg.mpr hsqOne)]
    nlinarith
  calc
    P.tailScale = root ^ 4 := by
      symm
      simpa [root] using quarterPower_fourth P.tailScale_mem.1.le
    _ ≤ root := hrootFourthLe
    _ ≤ (P.betaSeq 0) ^ 4 := hrootLeBeta

/-- At every hierarchy level, the square root of the common local parameter
is bounded by twice that level's beta. -/
theorem sqrt_localDelta_lt_two_mul_betaSeq {k : ℕ} (hk : 3 ≤ k)
    {η ζ : ℝ} (P : CoreExtractionParameters k η ζ)
    (q : Fin (P.stageBound + 1)) :
    Real.sqrt P.localDelta < 2 * P.betaSeq q := by
  have hbetaZeroLe : P.betaSeq 0 ≤ P.betaSeq q :=
    P.betaSeq_strictMono.monotone (Fin.zero_le q)
  have hfourthMono : (P.betaSeq 0) ^ 4 ≤ (P.betaSeq q) ^ 4 := by
    exact pow_le_pow_left₀ (P.betaSeq_pos 0).le hbetaZeroLe 4
  have hlocalUpper : P.localDelta ≤ 2 * (P.betaSeq q) ^ 4 := by
    unfold localDelta
    have htail := P.tailScale_le_betaSeq_zero_fourth hk
    nlinarith
  have hbetaPos : 0 < P.betaSeq q := P.betaSeq_pos q
  have hbetaOne : P.betaSeq q < 1 := P.betaSeq_lt_one q
  have hbetaFourthLtSq : (P.betaSeq q) ^ 4 < (P.betaSeq q) ^ 2 := by
    have hsqPos : 0 < (P.betaSeq q) ^ 2 := sq_pos_of_pos hbetaPos
    have hsqOne : (P.betaSeq q) ^ 2 < 1 := by
      nlinarith [mul_pos hbetaPos (sub_pos.mpr hbetaOne)]
    nlinarith [mul_pos hsqPos (sub_pos.mpr hsqOne)]
  apply (Real.sqrt_lt' (mul_pos (by norm_num) hbetaPos)).2
  calc
    P.localDelta ≤ 2 * (P.betaSeq q) ^ 4 := hlocalUpper
    _ < (2 * P.betaSeq q) ^ 2 := by nlinarith [sq_nonneg (P.betaSeq q)]

/-- The master constant has ample room for the numerical split in the
local-Turán/ES comparison. -/
theorem one_ninety_two_le_master {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ) : (192 : ℝ) ≤ P.master := by
  rw [P.master_eq, coreExtractionMasterConstant]
  have hkOne : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hpow : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 4 := one_le_pow₀ hkOne
  norm_num at hpow ⊢
  nlinarith

/-- Approximate-maximum coefficient used in a stage-`q` local-Turán call.
The factor `96` leaves half of the adjacent ES modulus for the fixed
near-extremality error. -/
noncomputable def localTuranAlpha {k : ℕ} {η ζ : ℝ}
    (P : CoreExtractionParameters k η ζ) (q : Fin P.stageBound) : ℝ :=
  P.master / 96 * Real.sqrt (P.betaSeq q.castSucc)

/-- The strong adjacent ES reserve, with square roots taken explicitly. -/
theorem master_mul_sqrt_beta_lt_ES {k : ℕ} (hk : 3 ≤ k)
    {η ζ : ℝ} (hη : 0 < η) (P : CoreExtractionParameters k η ζ)
    (q : Fin P.stageBound) :
    P.master * Real.sqrt (P.betaSeq q.castSucc) <
      η * coreExtractionESModulus k (P.betaSeq q.succ) := by
  have hleft : 0 ≤ P.master * Real.sqrt (P.betaSeq q.castSucc) :=
    mul_nonneg P.master_pos.le (Real.sqrt_nonneg _)
  have hright : 0 <
      η * coreExtractionESModulus k (P.betaSeq q.succ) :=
    mul_pos hη (coreExtractionESModulus_pos hk (P.betaSeq_pos q.succ))
  apply (sq_lt_sq₀ hleft hright.le).mp
  calc
    (P.master * Real.sqrt (P.betaSeq q.castSucc)) ^ 2 =
        P.master ^ 2 * P.betaSeq q.castSucc := by
      rw [mul_pow, Real.sq_sqrt (P.betaSeq_pos q.castSucc).le]
    _ < (η * coreExtractionESModulus k (P.betaSeq q.succ)) ^ 2 :=
      P.betaStep_ES_square_strong q

/-- The analogous square-root consequence for the adjacent beta scale. -/
theorem master_mul_sqrt_beta_lt_next {k : ℕ} {η ζ : ℝ}
    (hη : 0 < η) (P : CoreExtractionParameters k η ζ)
    (q : Fin P.stageBound) :
    P.master * Real.sqrt (P.betaSeq q.castSucc) <
      η * P.betaSeq q.succ := by
  have hleft : 0 ≤ P.master * Real.sqrt (P.betaSeq q.castSucc) :=
    mul_nonneg P.master_pos.le (Real.sqrt_nonneg _)
  have hright : 0 < η * P.betaSeq q.succ :=
    mul_pos hη (P.betaSeq_pos q.succ)
  apply (sq_lt_sq₀ hleft hright.le).mp
  calc
    (P.master * Real.sqrt (P.betaSeq q.castSucc)) ^ 2 =
        P.master ^ 2 * P.betaSeq q.castSucc := by
      rw [mul_pow, Real.sq_sqrt (P.betaSeq_pos q.castSucc).le]
    _ < (η * P.betaSeq q.succ) ^ 2 := P.betaStep_square_strong q

theorem localTuranAlpha_mem {k : ℕ} {η ζ : ℝ}
    (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k η ζ) (q : Fin P.stageBound) :
    P.localTuranAlpha q ∈ Set.Icc (0 : ℝ) 1 := by
  have hnextPos : 0 < P.betaSeq q.succ := P.betaSeq_pos q.succ
  have hnextOne : P.betaSeq q.succ < 1 := P.betaSeq_lt_one q.succ
  have hetaNext : η * P.betaSeq q.succ < 1 := by
    calc
      η * P.betaSeq q.succ < 1 * P.betaSeq q.succ :=
        mul_lt_mul_of_pos_right hη.2 hnextPos
      _ < 1 := by simpa using hnextOne
  have hmasterSqrt := P.master_mul_sqrt_beta_lt_next hη.1 q
  unfold localTuranAlpha
  constructor
  · exact mul_nonneg
      (div_nonneg P.master_pos.le (by norm_num : (0 : ℝ) ≤ 96))
      (Real.sqrt_nonneg _)
  · have hscaled :
        P.master / 96 * Real.sqrt (P.betaSeq q.castSucc) < 1 / 96 := by
      have := div_lt_div_of_pos_right
        (hmasterSqrt.trans hetaNext) (by norm_num : (0 : ℝ) < 96)
      simpa [div_mul_eq_mul_div, mul_assoc] using this
    linarith

/-- The actual adjacent-index scalar comparison used after `locallyTuran`:
the local-Turán error at level `q.castSucc` is strictly below the chosen ES
modulus for tolerance `q.succ`. -/
theorem localTuranCoefficient_lt_ES {k : ℕ} (hk : 3 ≤ k)
    {η ζ : ℝ} (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k η ζ) (q : Fin P.stageBound) :
    12 * (Real.sqrt P.localDelta / (η / 4) +
        P.localTuranAlpha q / (η / 4)) <
      coreExtractionESModulus k (P.betaSeq q.succ) := by
  have hsqrtLocal := P.sqrt_localDelta_lt_two_mul_betaSeq hk q.castSucc
  have hbetaSqrt : P.betaSeq q.castSucc ≤
      Real.sqrt (P.betaSeq q.castSucc) := P.betaSeq_le_sqrt q.castSucc
  have hmaster : (192 : ℝ) ≤ P.master := P.one_ninety_two_le_master
  have hlocalShare : 96 * Real.sqrt P.localDelta <
      P.master * Real.sqrt (P.betaSeq q.castSucc) := by
    have hfirst : 96 * Real.sqrt P.localDelta <
        192 * P.betaSeq q.castSucc := by
      nlinarith
    have hsecond : 192 * P.betaSeq q.castSucc ≤
        P.master * Real.sqrt (P.betaSeq q.castSucc) := by
      calc
        192 * P.betaSeq q.castSucc ≤
            P.master * P.betaSeq q.castSucc :=
          mul_le_mul_of_nonneg_right hmaster (P.betaSeq_pos q.castSucc).le
        _ ≤ P.master * Real.sqrt (P.betaSeq q.castSucc) :=
          mul_le_mul_of_nonneg_left hbetaSqrt P.master_pos.le
    exact hfirst.trans_le hsecond
  have hESShare := P.master_mul_sqrt_beta_lt_ES hk hη.1 q
  have hidentity :
      12 * (Real.sqrt P.localDelta / (η / 4) +
          P.localTuranAlpha q / (η / 4)) * η =
        48 * Real.sqrt P.localDelta +
          (P.master / 2) * Real.sqrt (P.betaSeq q.castSucc) := by
    unfold localTuranAlpha
    field_simp [hη.1.ne'] <;> ring
  have hmul :
      12 * (Real.sqrt P.localDelta / (η / 4) +
          P.localTuranAlpha q / (η / 4)) * η <
        coreExtractionESModulus k (P.betaSeq q.succ) * η := by
    rw [hidentity]
    nlinarith
  by_contra hnot
  have hge : coreExtractionESModulus k (P.betaSeq q.succ) ≤
      12 * (Real.sqrt P.localDelta / (η / 4) +
        P.localTuranAlpha q / (η / 4)) := le_of_not_gt hnot
  have hmulge := mul_le_mul_of_nonneg_right hge hη.1.le
  exact (not_lt_of_ge hmulge) hmul

end CoreExtractionParameters

/-! ## The Erdős--Simonovits seed partition -/

section CoreSeedPartition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The partition of a red neighborhood produced at one seed stage.

The parts live on the actual red-neighborhood subtype.  Thus `cover` and
`pairwiseDisjoint` are a genuine partition statement, with no ambient
membership side conditions.  The graph whose internal edges are counted is
the red--green neighborhood graph: its edges are exactly the nonblue pairs
inside the red neighborhood. -/
structure CoreSeedPartition
    (k : ℕ) (C : ColoredGraph V) (x : V) (ε : ℝ) where
  /-- The `Δ = k - 2` parts of the red neighborhood of the seed. -/
  parts : Fin (delta k) → Finset {v // v ∈ C.redNeighborFinset x}
  /-- Distinct indexed parts are disjoint. -/
  pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (delta k))) parts
  /-- The indexed parts cover the whole red-neighborhood subtype. -/
  cover :
    (Finset.univ : Finset (Fin (delta k))).biUnion parts = Finset.univ
  /-- At most `ε m²` red or green edges lie within the parts, where
  `m` is the red degree of the seed. -/
  internalRedGreenSmall :
    (∑ i : Fin (delta k),
        (((redGreenNeighborhoodGraph C x).edgeFinset ∩
          (parts i).sym2).card : ℝ)) ≤
      ε * (C.redDegree x : ℝ) ^ 2
  /-- Every part has size within `ε m` of `m / Δ`. -/
  balanced : ∀ i : Fin (delta k),
    |((parts i).card : ℝ) -
        (C.redDegree x : ℝ) / (delta k : ℝ)| ≤
      ε * (C.redDegree x : ℝ)

namespace CoreSeedPartition

/-- A subtype part, mapped back to the ambient vertex type. -/
def ambientPart {k : ℕ} {C : ColoredGraph V} {x : V} {ε : ℝ}
    (P : CoreSeedPartition k C x ε) (i : Fin (delta k)) : Finset V :=
  (P.parts i).map (Function.Embedding.subtype _)

@[simp]
theorem coe_mem_ambientPart {k : ℕ} {C : ColoredGraph V} {x : V} {ε : ℝ}
    (P : CoreSeedPartition k C x ε) (i : Fin (delta k))
    (v : {w // w ∈ C.redNeighborFinset x}) :
    (v : V) ∈ P.ambientPart i ↔ v ∈ P.parts i := by
  simp [ambientPart]

@[simp]
theorem card_ambientPart {k : ℕ} {C : ColoredGraph V} {x : V} {ε : ℝ}
    (P : CoreSeedPartition k C x ε) (i : Fin (delta k)) :
    (P.ambientPart i).card = (P.parts i).card := by
  simp [ambientPart]

/-- Every ambient part is contained in the seed's red neighborhood. -/
theorem ambientPart_subset_redNeighborFinset
    {k : ℕ} {C : ColoredGraph V} {x : V} {ε : ℝ}
    (P : CoreSeedPartition k C x ε) (i : Fin (delta k)) :
    P.ambientPart i ⊆ C.redNeighborFinset x := by
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
  exact u.property

/-- The ambient images of distinct subtype parts remain disjoint. -/
theorem ambientParts_pairwiseDisjoint
    {k : ℕ} {C : ColoredGraph V} {x : V} {ε : ℝ}
    (P : CoreSeedPartition k C x ε) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (delta k))) P.ambientPart := by
  intro i _ j _ hij
  change Disjoint
    ((P.parts i).map (Function.Embedding.subtype _))
    ((P.parts j).map (Function.Embedding.subtype _))
  exact (Finset.disjoint_map _).2
    (P.pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)

/-- The ambient images cover exactly the seed's red-neighbor finset. -/
theorem ambientParts_cover
    {k : ℕ} {C : ColoredGraph V} {x : V} {ε : ℝ}
    (P : CoreSeedPartition k C x ε) :
    (Finset.univ : Finset (Fin (delta k))).biUnion P.ambientPart =
      C.redNeighborFinset x := by
  apply Finset.Subset.antisymm
  · intro v hv
    rcases Finset.mem_biUnion.mp hv with ⟨i, _, hvi⟩
    exact P.ambientPart_subset_redNeighborFinset i hvi
  · intro v hv
    let u : {w // w ∈ C.redNeighborFinset x} := ⟨v, hv⟩
    have hu : u ∈ (Finset.univ :
        Finset {w // w ∈ C.redNeighborFinset x}) := Finset.mem_univ u
    rw [← P.cover] at hu
    rcases Finset.mem_biUnion.mp hu with ⟨i, hi, hui⟩
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    exact Finset.mem_map.mpr ⟨u, hui, rfl⟩

/-- The ambient part cardinalities add up to the red degree of the seed. -/
theorem sum_card_ambientParts
    {k : ℕ} {C : ColoredGraph V} {x : V} {ε : ℝ}
    (P : CoreSeedPartition k C x ε) :
    ∑ i, (P.ambientPart i).card = C.redDegree x := by
  calc
    ∑ i, (P.ambientPart i).card =
        (clusterUnion P.ambientPart).card :=
      (card_clusterUnion P.ambientPart P.ambientParts_pairwiseDisjoint).symm
    _ = (C.redNeighborFinset x).card :=
      congrArg Finset.card P.ambientParts_cover
    _ = C.redDegree x := rfl

/-- The balance estimate, phrased for the ambient images. -/
theorem ambientPart_balanced
    {k : ℕ} {C : ColoredGraph V} {x : V} {ε : ℝ}
    (P : CoreSeedPartition k C x ε) (i : Fin (delta k)) :
    |((P.ambientPart i).card : ℝ) -
        (C.redDegree x : ℝ) / (delta k : ℝ)| ≤
      ε * (C.redDegree x : ℝ) := by
  simpa using P.balanced i

end CoreSeedPartition

/-- The red--green graph in a red neighborhood is already clique-free for
every `k ≥ 3`.  The existing local-Turán API only needs the `k ≥ 4`
case; the strengthened lower endpoint here isolates the direct `k = 3`
seed-partition argument. -/
theorem redGreenNeighborhoodGraph_cliqueFree_coreSeed {k : ℕ} (hk : 3 ≤ k)
    {C : ColoredGraph V} (hC : C.FkFree k) (x : V) :
    (redGreenNeighborhoodGraph C x).CliqueFree (delta k + 1) := by
  classical
  intro t ht
  let emb : {v // v ∈ C.redNeighborFinset x} ↪ V :=
    Function.Embedding.subtype _
  let leaves : Finset V := t.map emb
  have hcard : leaves.card = k - 1 := by
    rw [show leaves.card = t.card by simp [leaves], ht.card_eq]
    unfold delta
    omega
  have hxleaves : x ∉ leaves := by
    intro hx
    rcases Finset.mem_map.mp hx with ⟨u, hu, hux⟩
    have hne := (C.mem_neighborFinset .red x u).mp u.property |>.1
    exact hne hux.symm
  have hred : ∀ y ∈ leaves, C.color x y = .red := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨u, hu, huy⟩
    subst y
    exact (C.mem_neighborFinset .red x u).mp u.property |>.2
  have hleaf : ∀ y ∈ leaves, ∀ z ∈ leaves, y ≠ z →
      (C.color y z).IsLeafColor := by
    intro y hy z hz hyz
    rcases Finset.mem_map.mp hy with ⟨u, hu, huy⟩
    rcases Finset.mem_map.mp hz with ⟨v, hv, hvz⟩
    subst y
    subst z
    have huv : u ≠ v := by
      intro huv
      apply hyz
      exact congrArg Subtype.val huv
    have hadj := ht.isClique (by simpa using hu) (by simpa using hv) huv
    exact (EdgeColor.isLeafColor_iff_ne_blue _).2
      ((redGreenNeighborhoodGraph_adj C x u v).1 hadj).2
  exact hC (containsFk_of_forbiddenConfig (by omega)
    ⟨hxleaves, hcard, hred, hleaf⟩)

/-- A uniform constructor for the seed partition.  For `k ≥ 4`, the size
threshold and conclusion are those of the arbitrary-finite
Erdős--Simonovits adapter.  For `k = 3`, `Δ = 1` and forbidden-pattern
freeness makes the red--green neighborhood graph empty, so the one-part
partition works with threshold zero. -/
theorem exists_coreSeedPartition {k : ℕ} (hk : 3 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ,
      ∀ {W : Type*} [Fintype W] [DecidableEq W],
        ∀ (C : ColoredGraph W) (_hC : C.FkFree k) (x : W),
          n₀ ≤ C.redDegree x →
          (SimpleGraph.turanNumber (C.redDegree x) (delta k) : ℝ) -
                coreExtractionESModulus k ε * (C.redDegree x : ℝ) ^ 2 ≤
              ((redGreenNeighborhoodGraph C x).edgeFinset.card : ℝ) →
          Nonempty (CoreSeedPartition k C x ε) := by
  classical
  by_cases hk4 : 4 ≤ k
  · obtain ⟨n₀, hES⟩ := coreExtractionESModulus_spec hk4 hε
    refine ⟨n₀, ?_⟩
    intro W _ _ C hC x hsize hnear
    let G := redGreenNeighborhoodGraph C x
    have hclique : G.CliqueFree (delta k + 1) :=
      redGreenNeighborhoodGraph_cliqueFree hk4 hC x
    have hsize' : n₀ ≤
        Fintype.card {v // v ∈ C.redNeighborFinset x} := by
      rw [card_redNeighborhood]
      exact hsize
    have hnear' :
        (SimpleGraph.turanNumber
              (Fintype.card {v // v ∈ C.redNeighborFinset x})
              (delta k) : ℝ) -
            coreExtractionESModulus k ε *
              (Fintype.card {v // v ∈ C.redNeighborFinset x} : ℝ) ^ 2 ≤
          (G.edgeFinset.card : ℝ) := by
      rw [card_redNeighborhood]
      simpa [G] using hnear
    obtain ⟨parts, hdisj, hcover, hinter, hbalanced⟩ :=
      hES hsize' G hclique hnear'
    exact ⟨{
      parts := parts
      pairwiseDisjoint := hdisj
      cover := hcover
      internalRedGreenSmall := by
        dsimp [G] at hinter
        rw [card_redNeighborhood] at hinter
        exact hinter
      balanced := by
        rw [card_redNeighborhood] at hbalanced
        exact hbalanced
    }⟩
  · have hk_eq : k = 3 := by omega
    subst k
    refine ⟨0, ?_⟩
    intro W _ _ C hC x _hsize _hnear
    have hclique : (redGreenNeighborhoodGraph C x).CliqueFree 2 := by
      simpa [delta] using
        (redGreenNeighborhoodGraph_cliqueFree_coreSeed (k := 3) (by omega) hC x)
    have hbot : redGreenNeighborhoodGraph C x = ⊥ :=
      SimpleGraph.cliqueFree_two.mp hclique
    let parts : Fin (delta 3) →
        Finset {v // v ∈ C.redNeighborFinset x} := fun _ ↦ Finset.univ
    exact ⟨{
      parts := parts
      pairwiseDisjoint := by
        intro i _ j _ hij
        apply (hij ?_).elim
        apply Fin.ext
        have hi : i.val < 1 := by simpa [delta] using i.isLt
        have hj : j.val < 1 := by simpa [delta] using j.isLt
        omega
      cover := by
        change (Finset.univ : Finset (Fin 1)).biUnion
          (fun _ ↦ (Finset.univ :
            Finset {v // v ∈ C.redNeighborFinset x})) = Finset.univ
        simp
      internalRedGreenSmall := by
        have hedgeEmpty :
            (redGreenNeighborhoodGraph C x).edgeFinset = ∅ := by
          ext e
          induction e using Sym2.inductionOn with
          | _ u v => simp [SimpleGraph.mem_edgeFinset, hbot]
        rw [hedgeEmpty]
        have hnonneg : 0 ≤ ε * (C.redDegree x : ℝ) ^ 2 :=
          mul_nonneg hε.le (sq_nonneg _)
        simpa [parts, delta] using hnonneg
      balanced := by
        intro i
        have hcardUniv :
            (Finset.univ :
              Finset {v // v ∈ C.redNeighborFinset x}).card =
                C.redDegree x := by
          rw [Finset.card_univ, card_redNeighborhood]
        have hnonneg : 0 ≤ ε * (C.redDegree x : ℝ) :=
          mul_nonneg hε.le (Nat.cast_nonneg _)
        have hpartCard : (parts i).card = C.redDegree x := by
          change (Finset.univ :
            Finset {v // v ∈ C.redNeighborFinset x}).card = C.redDegree x
          exact hcardUniv
        rw [hpartCard]
        norm_num [delta]
        exact hnonneg
    }⟩

end CoreSeedPartition

/--
The complete finite output of the `Δ`-regular core-extraction recursion.

Here `exceptional` is the paper's `U₀`, `clusters i` are its sets `Uᵢ`,
`reducedGraph` is the `Δ`-regular red reduced graph, and
`coreExtractionRemainder exceptional clusters` is the paper's remainder `T`.
The two disjointness fields say exactly that `U₀,U₁,…,Uₗ` are mutually
disjoint.  The remaining fields expose, rather than package into auxiliary
predicates, all six conclusions of `lemma:kth-order-recursion`.
-/
structure CoreExtractionResult
    (k n : ℕ) (C : ColoredGraph (Fin n)) (η δ ξ c : ℝ) where
  /-- Number `ℓ` of nonexceptional clusters. -/
  clusterCount : ℕ
  /-- The recursion extracts at least `k - 1` clusters. -/
  clusterCount_ge : k - 1 ≤ clusterCount
  /-- The exceptional set `U₀`. -/
  exceptional : Finset (Fin n)
  /-- The nonexceptional clusters `Uᵢ`, indexed by `Fin ℓ`. -/
  clusters : Fin clusterCount → Finset (Fin n)
  /-- Distinct nonexceptional clusters are disjoint. -/
  clusters_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin clusterCount)) clusters
  /-- The exceptional set is disjoint from every nonexceptional cluster. -/
  exceptional_disjoint_clusters : ∀ i, Disjoint exceptional (clusters i)
  /-- The red reduced graph on the cluster index set. -/
  reducedGraph : SimpleGraph (Fin clusterCount)
  /-- Decidable adjacency for the finite reduced graph. -/
  reducedGraphAdjDecidable : DecidableRel reducedGraph.Adj
  /-- Every reduced-graph vertex has degree `Δ = k - 2`. -/
  reducedGraph_regular :
    letI := reducedGraphAdjDecidable
    ∀ i, reducedGraph.degree i = delta k
  /-- Each cluster has blue density at least `1 - ξ`. -/
  blueDense : ∀ i,
    (1 - ξ) * (Nat.choose (clusters i).card 2 : ℝ) ≤
      (C.blueEdgeCountIn (clusters i) : ℝ)
  /-- Every cluster has size at least `c n`. -/
  clusterLowerBound : ∀ i,
    c * (n : ℝ) ≤ ((clusters i).card : ℝ)
  /-- Any two cluster sizes differ by at most `ξ n`. -/
  clusterBalanced : ∀ i j,
    |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| ≤ ξ * (n : ℝ)
  /-- The exceptional set has size at most `ξ n`. -/
  exceptionalSmall : (exceptional.card : ℝ) ≤ ξ * (n : ℝ)
  /-- The nonexceptional cluster union occupies at least `(η - ξ)n` vertices. -/
  clusterUnionLarge :
    (η - ξ) * (n : ℝ) ≤
      ((coreExtractionClusterUnion clusters).card : ℝ)
  /-- Reduced edges correspond to red-dense cluster pairs. -/
  redDenseOnEdges : ∀ i j,
    reducedGraph.Adj i j →
      1 - ξ ≤ C.colorDensity .red (clusters i) (clusters j)
  /-- Distinct reduced nonedges correspond to green-dense cluster pairs. -/
  greenDenseOnNonedges : ∀ i j,
    i ≠ j → ¬ reducedGraph.Adj i j →
      1 - ξ ≤ C.colorDensity .green (clusters i) (clusters j)
  /-- At most `ξ n²` red or blue edges cross from the core to its remainder. -/
  boundarySmall :
    (C.colorEdgeCountBetween .red
          (coreExtractionCore exceptional clusters)
          (coreExtractionRemainder exceptional clusters) : ℝ) +
        (C.colorEdgeCountBetween .blue
          (coreExtractionCore exceptional clusters)
          (coreExtractionRemainder exceptional clusters) : ℝ) ≤
      ξ * (n : ℝ) ^ 2
  /-- The weighted objective restricted to the remainder is still near-extremal. -/
  remainderNearExtremal :
    -((δ + ξ) * (n : ℝ) ^ 2) ≤
      (C.redEdgeCountIn
          (coreExtractionRemainder exceptional clusters) : ℝ) -
        (delta k : ℝ) *
          (C.blueEdgeCountIn
            (coreExtractionRemainder exceptional clusters) : ℝ)

/-- Internal output of the core recursion before the paper's `ξ / 3`
rescaling.  All local density, balance, exceptional-set, and boundary errors
are `ζ`; the three accumulated losses are exposed as `3 * ζ` in the covered
mass and the remainder objective. -/
structure CoreExtractionRawResult
    (k n : ℕ) (C : ColoredGraph (Fin n)) (η δ ζ c : ℝ) where
  clusterCount : ℕ
  clusterCount_ge : k - 1 ≤ clusterCount
  exceptional : Finset (Fin n)
  clusters : Fin clusterCount → Finset (Fin n)
  clusters_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin clusterCount)) clusters
  exceptional_disjoint_clusters : ∀ i, Disjoint exceptional (clusters i)
  reducedGraph : SimpleGraph (Fin clusterCount)
  reducedGraphAdjDecidable : DecidableRel reducedGraph.Adj
  reducedGraph_regular :
    letI := reducedGraphAdjDecidable
    ∀ i, reducedGraph.degree i = delta k
  blueDense : ∀ i,
    (1 - ζ) * (Nat.choose (clusters i).card 2 : ℝ) ≤
      (C.blueEdgeCountIn (clusters i) : ℝ)
  clusterLowerBound : ∀ i,
    c * (n : ℝ) ≤ ((clusters i).card : ℝ)
  clusterBalanced : ∀ i j,
    |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| ≤ ζ * (n : ℝ)
  exceptionalSmall : (exceptional.card : ℝ) ≤ ζ * (n : ℝ)
  clusterUnionLarge :
    (η - 3 * ζ) * (n : ℝ) ≤
      ((coreExtractionClusterUnion clusters).card : ℝ)
  redDenseOnEdges : ∀ i j,
    reducedGraph.Adj i j →
      1 - ζ ≤ C.colorDensity .red (clusters i) (clusters j)
  greenDenseOnNonedges : ∀ i j,
    i ≠ j → ¬ reducedGraph.Adj i j →
      1 - ζ ≤ C.colorDensity .green (clusters i) (clusters j)
  boundarySmall :
    (C.colorEdgeCountBetween .red
          (coreExtractionCore exceptional clusters)
          (coreExtractionRemainder exceptional clusters) : ℝ) +
        (C.colorEdgeCountBetween .blue
          (coreExtractionCore exceptional clusters)
          (coreExtractionRemainder exceptional clusters) : ℝ) ≤
      ζ * (n : ℝ) ^ 2
  remainderNearExtremal :
    -((δ + 3 * ζ) * (n : ℝ) ^ 2) ≤
      (C.redEdgeCountIn
          (coreExtractionRemainder exceptional clusters) : ℝ) -
        (delta k : ℝ) *
          (C.blueEdgeCountIn
            (coreExtractionRemainder exceptional clusters) : ℝ)

namespace CoreExtractionRawResult

/-- Weaken a raw recursion output to the paper-facing error parameter.  The
two hypotheses are exactly the local and accumulated error allocations; the
eventual wrapper uses `ζ = ξ / 3`. -/
noncomputable def toCoreExtractionResult
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ ξ c : ℝ}
    (R : CoreExtractionRawResult k n C η δ ζ c)
    (hlocal : ζ ≤ ξ) (haccumulated : 3 * ζ ≤ ξ) :
    CoreExtractionResult k n C η δ ξ c := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnSq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  exact {
    clusterCount := R.clusterCount
    clusterCount_ge := R.clusterCount_ge
    exceptional := R.exceptional
    clusters := R.clusters
    clusters_pairwiseDisjoint := R.clusters_pairwiseDisjoint
    exceptional_disjoint_clusters := R.exceptional_disjoint_clusters
    reducedGraph := R.reducedGraph
    reducedGraphAdjDecidable := R.reducedGraphAdjDecidable
    reducedGraph_regular := R.reducedGraph_regular
    blueDense := fun i ↦ by
      have hchoose : 0 ≤ (Nat.choose (R.clusters i).card 2 : ℝ) := by positivity
      exact (mul_le_mul_of_nonneg_right (by linarith) hchoose).trans
        (R.blueDense i)
    clusterLowerBound := R.clusterLowerBound
    clusterBalanced := fun i j ↦
      (R.clusterBalanced i j).trans
        (mul_le_mul_of_nonneg_right hlocal hn)
    exceptionalSmall := R.exceptionalSmall.trans
      (mul_le_mul_of_nonneg_right hlocal hn)
    clusterUnionLarge := by
      refine (mul_le_mul_of_nonneg_right ?_ hn).trans R.clusterUnionLarge
      linarith
    redDenseOnEdges := fun i j hij ↦
      (by linarith [R.redDenseOnEdges i j hij])
    greenDenseOnNonedges := fun i j hij hnon ↦
      (by linarith [R.greenDenseOnNonedges i j hij hnon])
    boundarySmall := R.boundarySmall.trans
      (mul_le_mul_of_nonneg_right hlocal hnSq)
    remainderNearExtremal := by
      have hcoeff : δ + 3 * ζ ≤ δ + ξ := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcoeff hnSq
      have hlower :
          -((δ + ξ) * (n : ℝ) ^ 2) ≤
            -((δ + 3 * ζ) * (n : ℝ) ^ 2) := by
        linarith
      exact hlower.trans R.remainderNearExtremal
  }

/-- The exact arithmetic used by the final wrapper. -/
theorem third_local {ξ : ℝ} (hξ : 0 ≤ ξ) : ξ / 3 ≤ ξ := by
  linarith

theorem three_mul_third (ξ : ℝ) : 3 * (ξ / 3) ≤ ξ := by
  ring_nf
  exact le_rfl

end CoreExtractionRawResult

/-! ## The red dominant-color reduced graph -/

/-- The reduced graph used in core extraction: two distinct cluster indices
are adjacent exactly when their red density is at least `1/2`. -/
noncomputable def coreExtractionReducedGraph
    {V I : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (clusters : I → Finset V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ 1 / 2 ≤ C.colorDensity .red (clusters i) (clusters j)
  symm.symm i j hij := by
    refine ⟨hij.1.symm, ?_⟩
    rw [C.colorDensity_comm]
    exact hij.2
  loopless.irrefl i hi := hi.1 rfl

@[simp]
theorem coreExtractionReducedGraph_adj
    {V I : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (clusters : I → Finset V) (i j : I) :
    (coreExtractionReducedGraph C clusters).Adj i j ↔
      i ≠ j ∧ 1 / 2 ≤ C.colorDensity .red (clusters i) (clusters j) :=
  Iff.rfl

/-- Once Goal 2c supplies a red-or-green dominant color, thresholding the red
density at `1/2` gives the exact red/green dichotomy used by the reduced
graph.  The diagonal is excluded explicitly. -/
theorem coreExtractionReducedGraph_dichotomy
    {V I : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    {mu : ℝ} (hmu : mu < 1 / 2)
    (hdominant : ∀ i j, i ≠ j →
      1 - mu ≤ max (C.colorDensity .red (clusters i) (clusters j))
        (C.colorDensity .green (clusters i) (clusters j))) :
    (∀ i j, (coreExtractionReducedGraph C clusters).Adj i j →
      1 - mu ≤ C.colorDensity .red (clusters i) (clusters j)) ∧
    (∀ i j, i ≠ j → ¬(coreExtractionReducedGraph C clusters).Adj i j →
      C.colorDensity .red (clusters i) (clusters j) ≤ mu ∧
      1 - mu ≤ C.colorDensity .green (clusters i) (clusters j)) := by
  have hcolorSum (i j : I) (hij : i ≠ j) :
      C.colorDensity .red (clusters i) (clusters j) +
          C.colorDensity .green (clusters i) (clusters j) +
            C.colorDensity .blue (clusters i) (clusters j) = 1 :=
    C.red_add_green_add_blue_colorDensity (hnonempty i) (hnonempty j)
      (hdisj (Set.mem_univ i) (Set.mem_univ j) hij)
  have hblueNonneg (i j : I) :
      0 ≤ C.colorDensity .blue (clusters i) (clusters j) := by
    unfold colorDensity
    positivity
  constructor
  · intro i j hij
    rcases (le_max_iff.mp (hdominant i j hij.1)) with hred | hgreen
    · exact hred
    · have hredUpper :
          C.colorDensity .red (clusters i) (clusters j) ≤ mu := by
        nlinarith [hcolorSum i j hij.1, hblueNonneg i j]
      nlinarith [hij.2]
  · intro i j hij hnonadj
    have hredHalf : C.colorDensity .red (clusters i) (clusters j) < 1 / 2 := by
      rw [coreExtractionReducedGraph_adj] at hnonadj
      push_neg at hnonadj
      exact hnonadj hij
    rcases (le_max_iff.mp (hdominant i j hij)) with hred | hgreen
    · exfalso
      nlinarith
    · refine ⟨?_, hgreen⟩
      nlinarith [hcolorSum i j hij, hblueNonneg i j]

/-! ## Stages F6--F7: dominant colors and the reduced graph -/

/-- The eight finite cluster-family hypotheses consumed by
`vertexLevelMixedMassExplicit`, kept as transparent fields for the
core-extraction recursion.  The scalar admissibility assumptions on
`k`, `eta`, and `beta` remain theorem arguments, rather than being duplicated
inside each finite certificate. -/
structure CoreExtractionMixedMassCertificate
    (n₀ k n t : ℕ) (C : ColoredGraph (Fin n)) (eta beta : ℝ)
    (clusters : Fin t → Finset (Fin n)) where
  /-- (1) The ambient order is beyond the Goal 2c threshold. -/
  ambientLarge : n₀ ≤ n
  /-- (2) The coloring excludes the forbidden colored pattern. -/
  coloring_mem_Ck : C ∈ Ck k n
  /-- (3) There are at least `k - 1` clusters. -/
  clusterCount_ge : k - 1 ≤ t
  /-- (4) The cluster family is pairwise disjoint. -/
  clusters_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin t)) clusters
  /-- (5) Every cluster has the required linear lower bound. -/
  clusterLowerBound : ∀ i,
    eta * (n : ℝ) ≤ ((clusters i).card : ℝ)
  /-- (6) Cluster sizes differ by at most `beta * n`. -/
  clusterBalanced : ∀ i j,
    |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| ≤
      beta * (n : ℝ)
  /-- (7) Blue density between distinct clusters is at most `beta`. -/
  blueSparseBetween : ∀ i j, i ≠ j →
    C.colorDensity .blue (clusters i) (clusters j) ≤ beta
  /-- (8) Every cluster vertex has high own-cluster blue degree, low
  off-cluster blue degree, and small restricted weighted degree. -/
  vertexControls : ∀ i v, v ∈ clusters i →
    (1 - beta) * ((clusters i).card : ℝ) ≤
        (C.blueDegreeIn v (clusters i) : ℝ) ∧
    (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
        beta * (n : ℝ) ∧
    |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
        beta * (n : ℝ)

/-- Stages F6--F7 in one reusable adapter.  The eight fields of
`CoreExtractionMixedMassCertificate` are fed verbatim to Goal 2c with its
actual constant `dominantColorConstant k`.  Thresholding red density at
`1/2` then gives red-dense reduced edges and, for distinct reduced nonedges,
both a red upper bound and a green lower bound.

The returned ambient threshold is enlarged to at least one solely to derive
cluster nonemptiness from the linear size hypothesis. -/
theorem exists_coreExtractionReducedGraphDichotomyThreshold
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) (beta : ℝ)
    (hbeta : beta ∈ Set.Ioo (0 : ℝ) (dominantColorBeta₀ k eta)) :
    ∃ n₀ : ℕ,
      ∀ {n t : ℕ} {C : ColoredGraph (Fin n)}
        {clusters : Fin t → Finset (Fin n)},
        CoreExtractionMixedMassCertificate n₀ k n t C eta beta clusters →
          (let mu :=
              dominantColorConstant k * Real.sqrt beta / eta ^ 2
           (∀ i j, (coreExtractionReducedGraph C clusters).Adj i j →
              1 - mu ≤ C.colorDensity .red (clusters i) (clusters j)) ∧
           (∀ i j, i ≠ j →
              ¬(coreExtractionReducedGraph C clusters).Adj i j →
                C.colorDensity .red (clusters i) (clusters j) ≤ mu ∧
                1 - mu ≤
                  C.colorDensity .green (clusters i) (clusters j))) := by
  obtain ⟨nGoal2c, hGoal2c⟩ :=
    vertexLevelMixedMassExplicit k hk eta heta beta hbeta
  refine ⟨max 1 nGoal2c, ?_⟩
  intro n t C clusters A
  have hnGoal2c : nGoal2c ≤ n :=
    (le_max_right 1 nGoal2c).trans A.ambientLarge
  have hnOne : 1 ≤ n :=
    (le_max_left 1 nGoal2c).trans A.ambientLarge
  have hnpos : 0 < n := by omega
  have hnonempty (i : Fin t) : (clusters i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hi
    have hsize := A.clusterLowerBound i
    rw [hi, Finset.card_empty, Nat.cast_zero] at hsize
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    nlinarith [mul_pos heta.1 hnR]
  have hdominant : ∀ i j, i ≠ j →
      1 - dominantColorConstant k * Real.sqrt beta / eta ^ 2 ≤
        max (C.colorDensity .red (clusters i) (clusters j))
          (C.colorDensity .green (clusters i) (clusters j)) :=
    hGoal2c n hnGoal2c C A.coloring_mem_Ck t A.clusterCount_ge clusters
      A.clusters_pairwiseDisjoint A.clusterLowerBound A.clusterBalanced
      A.blueSparseBetween A.vertexControls
  obtain ⟨_, _, _, hscaleSmall, _, _, hscale⟩ :=
    dominantColorParameterBounds hk heta hbeta
  have hmu :
      dominantColorConstant k * Real.sqrt beta / eta ^ 2 < 1 / 2 := by
    rw [← hscale]
    nlinarith
  simpa only using
    coreExtractionReducedGraph_dichotomy C clusters
      A.clusters_pairwiseDisjoint hnonempty hmu hdominant

/-! ## Stage F1: fixed-scale tails and seed cleaning -/

/-- The first, cleaned state of the core-extraction recursion.

`goodSet` is the fixed-`tailScale` weighted-degree tail set.  A global
maximum-red-degree vertex is then inserted before cleaning; this is why the
cleaned weighted-degree estimate has one additional contribution, bounded
by `Δ = k - 2`.  The objective and red-degree losses are deliberately left
in their exact cardinal form for the later parameter bookkeeping.

The fixed tail scale is chosen before the input near-extremality parameter.
-/
structure CleanedCoreStart
    (k n : ℕ) (C : ColoredGraph (Fin n)) (η tailScale : ℝ) where
  /-- Vertices whose original weighted degree is not in the lower tail. -/
  goodSet : Finset (Fin n)
  goodSet_eq :
    goodSet = Finset.univ.filter fun v ↦
      -(tailScale ^ (1 / 4 : ℝ)) * (n : ℝ) ≤
        (weightedDegree k C v : ℝ)
  /-- A global maximum-red-degree vertex, retained even if it lies in the
  exceptional tail. -/
  seed : Fin n
  seed_max_red : ∀ v, C.redDegree v ≤ C.redDegree seed
  seed_red_lower : η * (n : ℝ) ≤ (C.redDegree seed : ℝ)
  /-- The tail set together with the maximum-red-degree seed. -/
  retained : Finset (Fin n)
  retained_eq : retained = insert seed goodSet
  seed_mem_retained : seed ∈ retained
  goodSet_subset_retained : goodSet ⊆ retained
  /-- The coloring obtained by making every edge outside `retained` green. -/
  cleaned : ColoredGraph (Fin n)
  cleaned_eq : cleaned = C.greenOutside retained
  cleaned_mem_Ck : cleaned ∈ Ck k n
  /-- The global upper-tail conclusion, retained verbatim. -/
  weightedDegree_upper : ∀ v,
    (weightedDegree k C v : ℝ) ≤
      8 * (delta k : ℝ) * Real.sqrt tailScale * (n : ℝ)
  /-- Lower-tail cardinal estimate. -/
  goodSet_compl_small :
    ((Finset.univ \ goodSet).card : ℝ) ≤
      10 * (delta k : ℝ) * tailScale ^ (1 / 4 : ℝ) * (n : ℝ)
  /-- Inserting the seed can only decrease the deleted set. -/
  retained_compl_small :
    ((Finset.univ \ retained).card : ℝ) ≤
      10 * (delta k : ℝ) * tailScale ^ (1 / 4 : ℝ) * (n : ℝ)
  /-- Restricted weighted-degree estimate on `goodSet`. -/
  goodSet_weightedDegree : ∀ v ∈ goodSet,
    |(weightedDegreeIn k C v goodSet : ℝ)| ≤
      12 * (delta k : ℝ) ^ 2 * tailScale ^ (1 / 4 : ℝ) * (n : ℝ)
  /-- After inserting the seed, at most one new edge contribution is added. -/
  cleaned_goodSet_weightedDegree : ∀ v ∈ goodSet,
    |(weightedDegree k cleaned v : ℝ)| ≤
      12 * (delta k : ℝ) ^ 2 * tailScale ^ (1 / 4 : ℝ) * (n : ℝ) +
        (delta k : ℝ)
  /-- No cleaned red degree exceeds the original seed red degree. -/
  cleaned_red_le_seed_original : ∀ v,
    cleaned.redDegree v ≤ C.redDegree seed
  /-- The seed loses at most one red neighbor per deleted vertex. -/
  seed_red_loss :
    C.redDegree seed ≤
      cleaned.redDegree seed + (Finset.univ \ retained).card
  /-- Consequently the cleaned seed remains large. -/
  cleaned_seed_red_lower :
    η * (n : ℝ) - ((Finset.univ \ retained).card : ℝ) ≤
      (cleaned.redDegree seed : ℝ)
  /-- The original maximum becomes an approximate maximum after cleaning. -/
  cleaned_seed_nearMax : ∀ v,
    cleaned.redDegree v ≤
      cleaned.redDegree seed + (Finset.univ \ retained).card
  /-- Exact integer objective loss under cleaning. -/
  objective_loss :
    objective k C -
        (((Finset.univ \ retained).card * n : ℕ) : ℤ) ≤
      objective k cleaned
  /-- The fixed-scale near-extremality estimate after cleaning. -/
  cleaned_nearExtremal :
    -(tailScale * (n : ℝ) ^ 2) -
        ((Finset.univ \ retained).card : ℝ) * (n : ℝ) ≤
      (objective k cleaned : ℝ)

namespace CleanedCoreStart

/-- The cleaned objective estimate at the common local-Turán parameter.
The `betaSeq 0` fourth-power term absorbs exactly the deleted-vertex loss
using the weighted-degree exceptional-set estimate. -/
theorem cleaned_nearExtremal_localDelta
    {k n : ℕ} {η ζ : ℝ} {C : ColoredGraph (Fin n)}
    (P : CoreExtractionParameters k η ζ)
    (A : CleanedCoreStart k n C η P.tailScale) :
    -(P.localDelta * (n : ℝ) ^ 2) ≤
      (objective k A.cleaned : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdeleted :
      ((Finset.univ \ A.retained).card : ℝ) ≤
        (P.betaSeq 0) ^ 4 * (n : ℝ) := by
    calc
      ((Finset.univ \ A.retained).card : ℝ) ≤
          10 * (delta k : ℝ) * P.tailScale ^ (1 / 4 : ℝ) *
            (n : ℝ) := A.retained_compl_small
      _ ≤ (P.betaSeq 0) ^ 4 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right P.tail_exceptional hn
  have hdeletedScaled :
      ((Finset.univ \ A.retained).card : ℝ) * (n : ℝ) ≤
        (P.betaSeq 0) ^ 4 * (n : ℝ) ^ 2 := by
    calc
      ((Finset.univ \ A.retained).card : ℝ) * (n : ℝ) ≤
          ((P.betaSeq 0) ^ 4 * (n : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hdeleted hn
      _ = (P.betaSeq 0) ^ 4 * (n : ℝ) ^ 2 := by ring
  have hcleaned := A.cleaned_nearExtremal
  unfold CoreExtractionParameters.localDelta
  nlinarith

end CleanedCoreStart

/-- A vertex outside the retained set has no red neighbor after cleaning. -/
private theorem greenOutside_redDegree_of_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (S : Finset V) {v : V} (hv : v ∉ S) :
    (C.greenOutside S).redDegree v = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro w hw
  have hw' := (C.greenOutside S).mem_neighborFinset .red v w |>.1 hw
  have hgreen := C.greenOutside_color_of_not_both S hw'.1 (by simp [hv])
  rw [hgreen] at hw'
  exact (by simpa using hw'.2)

/-- Adding one vertex changes a restricted weighted degree by at most one
edge contribution, whose absolute value is at most `Δ` when `k ≥ 3`. -/
private theorem abs_weightedDegreeIn_insert_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 3 ≤ k) (C : ColoredGraph V)
    (v seed : V) (S : Finset V) :
    |(weightedDegreeIn k C v (insert seed S) : ℝ)| ≤
      |(weightedDegreeIn k C v S : ℝ)| + (delta k : ℝ) := by
  classical
  have hDeltaNat : 1 ≤ delta k := by
    unfold delta
    omega
  have hDelta : (1 : ℝ) ≤ (delta k : ℝ) := by exact_mod_cast hDeltaNat
  by_cases hseed : seed ∈ S
  · rw [Finset.insert_eq_of_mem hseed]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  · have hdisj : Disjoint S {seed} := by
      simp [hseed]
    have hred := C.degreeIn_union_of_disjoint .red v hdisj
    have hblue := C.degreeIn_union_of_disjoint .blue v hdisj
    have hsplitZ :
        weightedDegreeIn k C v (insert seed S) =
          weightedDegreeIn k C v S + weightedDegreeIn k C v {seed} := by
      rw [show insert seed S = S ∪ {seed} by ext; simp [or_comm]]
      unfold weightedDegreeIn
      change
        (C.degreeIn .red v (S ∪ {seed}) : ℤ) -
            (delta k : ℤ) * (C.degreeIn .blue v (S ∪ {seed}) : ℤ) =
          ((C.degreeIn .red v S : ℤ) -
              (delta k : ℤ) * (C.degreeIn .blue v S : ℤ)) +
            ((C.degreeIn .red v {seed} : ℤ) -
              (delta k : ℤ) * (C.degreeIn .blue v {seed} : ℤ))
      rw [hred, hblue]
      push_cast
      ring
    have hsingleUpperZ := weightedDegreeIn_le_card k C v {seed}
    have hsingleLowerZ := neg_delta_mul_card_le_weightedDegreeIn k C v {seed}
    have hsingle : |(weightedDegreeIn k C v {seed} : ℝ)| ≤ (delta k : ℝ) := by
      rw [abs_le]
      constructor
      · have hsingleLowerZ' :
            -(delta k : ℤ) ≤ weightedDegreeIn k C v {seed} := by
          simpa using hsingleLowerZ
        exact_mod_cast hsingleLowerZ'
      · have hupper : (weightedDegreeIn k C v {seed} : ℝ) ≤ 1 := by
          have hsingleUpperZ' : weightedDegreeIn k C v {seed} ≤ (1 : ℤ) := by
            simpa using hsingleUpperZ
          exact_mod_cast hsingleUpperZ'
        exact hupper.trans hDelta
    rw [hsplitZ]
    push_cast
    exact (abs_add_le _ _).trans (add_le_add_right hsingle _)

/-- Apply the weighted-degree tails once, at a scale fixed before
the input `δ`, and perform the maximum-red-degree seed cleaning.

The returned threshold depends on `tailScale`, not on the subsequently
quantified `δ`.
-/
theorem exists_cleanedCoreStart_tailThreshold
    (k : ℕ) (hk : 3 ≤ k) (η tailScale : ℝ)
    (htailScale : tailScale ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ nTail : ℕ, ∀ n ≥ nTail, ∀ δ ∈ Set.Ioc (0 : ℝ) tailScale,
      ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
        -(δ * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
        (∃ x, η * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
        Nonempty (CleanedCoreStart k n C η tailScale) := by
  obtain ⟨nTail, htails⟩ := weightedDegreeTails k hk tailScale htailScale
  refine ⟨nTail, ?_⟩
  intro n hn δ hδ C hC hnear hhigh
  have hnSq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
  have hnearTail :
      -(tailScale * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ.2) hnSq]
  let X : Finset (Fin n) := Finset.univ.filter fun v ↦
    -(tailScale ^ (1 / 4 : ℝ)) * (n : ℝ) ≤
      (weightedDegree k C v : ℝ)
  have htail :
      (∀ v, (weightedDegree k C v : ℝ) ≤
          8 * (delta k : ℝ) * Real.sqrt tailScale * (n : ℝ)) ∧
        ((Finset.univ \ X).card : ℝ) ≤
          10 * (delta k : ℝ) * tailScale ^ (1 / 4 : ℝ) * (n : ℝ) ∧
        ∀ v ∈ X, |(weightedDegreeIn k C v X : ℝ)| ≤
          12 * (delta k : ℝ) ^ 2 * tailScale ^ (1 / 4 : ℝ) * (n : ℝ) := by
    simpa only [X] using htails n hn C hC hnearTail
  rcases htail with ⟨hupper, hXsmall, hXweighted⟩
  obtain ⟨highVertex, hhighVertex⟩ := hhigh
  obtain ⟨seed, _hseedUniv, hseedMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n)) C.redDegree
      ⟨highVertex, Finset.mem_univ _⟩
  have hseedMaxAll : ∀ v, C.redDegree v ≤ C.redDegree seed := by
    intro v
    exact hseedMax v (Finset.mem_univ v)
  have hseedHigh : η * (n : ℝ) ≤ (C.redDegree seed : ℝ) := by
    have hmaxCast : (C.redDegree highVertex : ℝ) ≤
        (C.redDegree seed : ℝ) := by
      exact_mod_cast hseedMaxAll highVertex
    exact hhighVertex.trans hmaxCast
  let retained : Finset (Fin n) := insert seed X
  let cleaned : ColoredGraph (Fin n) := C.greenOutside retained
  have hseedRetained : seed ∈ retained := by simp [retained]
  have hXRetained : X ⊆ retained := by
    intro v hv
    simp [retained, hv]
  have hcompSubset : Finset.univ \ retained ⊆ Finset.univ \ X := by
    intro v hv
    rw [Finset.mem_sdiff] at hv ⊢
    exact ⟨Finset.mem_univ v, fun hvX ↦ hv.2 (hXRetained hvX)⟩
  have hretainedSmall :
      ((Finset.univ \ retained).card : ℝ) ≤
        10 * (delta k : ℝ) * tailScale ^ (1 / 4 : ℝ) * (n : ℝ) := by
    have hcards : ((Finset.univ \ retained).card : ℝ) ≤
        ((Finset.univ \ X).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hcompSubset
    exact hcards.trans hXsmall
  have hcleanedCk : cleaned ∈ Ck k n := by
    dsimp [cleaned]
    exact greenOutside_mem_Ck (by omega) hC retained
  have hcleanedWeighted : ∀ v ∈ X,
      |(weightedDegree k cleaned v : ℝ)| ≤
        12 * (delta k : ℝ) ^ 2 * tailScale ^ (1 / 4 : ℝ) * (n : ℝ) +
          (delta k : ℝ) := by
    intro v hv
    have hvRetained := hXRetained hv
    rw [show cleaned = C.greenOutside retained by rfl,
      weightedDegree_greenOutside_of_mem k C retained hvRetained]
    exact (abs_weightedDegreeIn_insert_le k hk C v seed X).trans
      (add_le_add (hXweighted v hv) le_rfl)
  have hcleanedLeSeed : ∀ v, cleaned.redDegree v ≤ C.redDegree seed := by
    intro v
    by_cases hv : v ∈ retained
    · have hsplit :
          C.redDegreeIn v retained + C.redDegreeIn v retainedᶜ =
            C.redDegree v :=
        degreeIn_add_degreeIn_compl C .red v retained
      have hrestricted : C.redDegreeIn v retained ≤ C.redDegree v := by
        calc
          C.redDegreeIn v retained ≤
              C.redDegreeIn v retained + C.redDegreeIn v retainedᶜ :=
            Nat.le_add_right _ _
          _ = C.redDegree v := hsplit
      rw [show cleaned = C.greenOutside retained by rfl,
        C.greenOutside_redDegree_of_mem retained hv]
      exact hrestricted.trans (hseedMaxAll v)
    · rw [show cleaned = C.greenOutside retained by rfl,
        greenOutside_redDegree_of_not_mem C retained hv]
      exact Nat.zero_le _
  have hseedLoss :
      C.redDegree seed ≤
        cleaned.redDegree seed + (Finset.univ \ retained).card := by
    have hsplit :
        C.redDegreeIn seed retained + C.redDegreeIn seed retainedᶜ =
          C.redDegree seed :=
      degreeIn_add_degreeIn_compl C .red seed retained
    have houtside : C.redDegreeIn seed retainedᶜ ≤ retainedᶜ.card :=
      degreeIn_le_card C .red seed retainedᶜ
    have hlossRestricted :
        C.redDegree seed ≤
          C.redDegreeIn seed retained + retainedᶜ.card := by
      rw [← hsplit]
      exact Nat.add_le_add_left houtside _
    rw [Finset.compl_eq_univ_sdiff] at hlossRestricted
    rw [show cleaned = C.greenOutside retained by rfl,
      C.greenOutside_redDegree_of_mem retained hseedRetained]
    exact hlossRestricted
  have hseedCleanedLower :
      η * (n : ℝ) - ((Finset.univ \ retained).card : ℝ) ≤
        (cleaned.redDegree seed : ℝ) := by
    have hseedLossCast : (C.redDegree seed : ℝ) ≤
        (cleaned.redDegree seed : ℝ) +
          ((Finset.univ \ retained).card : ℝ) := by
      exact_mod_cast hseedLoss
    linarith
  have hcleanedNearMax : ∀ v,
      cleaned.redDegree v ≤
        cleaned.redDegree seed + (Finset.univ \ retained).card := by
    intro v
    exact (hcleanedLeSeed v).trans hseedLoss
  have hobjectiveLoss :
      objective k C -
          (((Finset.univ \ retained).card * n : ℕ) : ℤ) ≤
        objective k cleaned := by
    simpa only [cleaned, Fintype.card_fin] using
      objective_sub_compl_mul_card_le_objective_greenOutside k C retained
  have hobjectiveLossReal :
      (objective k C : ℝ) -
          ((Finset.univ \ retained).card : ℝ) * (n : ℝ) ≤
        (objective k cleaned : ℝ) := by
    exact_mod_cast hobjectiveLoss
  have hcleanedNear :
      -(tailScale * (n : ℝ) ^ 2) -
          ((Finset.univ \ retained).card : ℝ) * (n : ℝ) ≤
        (objective k cleaned : ℝ) := by
    linarith
  exact ⟨{
    goodSet := X
    goodSet_eq := rfl
    seed := seed
    seed_max_red := hseedMaxAll
    seed_red_lower := hseedHigh
    retained := retained
    retained_eq := rfl
    seed_mem_retained := hseedRetained
    goodSet_subset_retained := hXRetained
    cleaned := cleaned
    cleaned_eq := rfl
    cleaned_mem_Ck := hcleanedCk
    weightedDegree_upper := hupper
    goodSet_compl_small := hXsmall
    retained_compl_small := hretainedSmall
    goodSet_weightedDegree := hXweighted
    cleaned_goodSet_weightedDegree := hcleanedWeighted
    cleaned_red_le_seed_original := hcleanedLeSeed
    seed_red_loss := hseedLoss
    cleaned_seed_red_lower := hseedCleanedLower
    cleaned_seed_nearMax := hcleanedNearMax
    objective_loss := hobjectiveLoss
    cleaned_nearExtremal := hcleanedNear
  }⟩

/-- Single-level local-Turán bridge for the seed iteration.

At hierarchy level `q`, an eligible seed is controlled at the
current index `q.castSucc`; the resulting near-Turán neighborhood is strong
enough for Erdős--Simonovits with the adjacent output tolerance `q.succ`.
The conclusion is exactly the near-Turán hypothesis consumed by
`exists_coreSeedStage_of_nearTuran`. -/
theorem exists_localTuranBridge_atLevel
    (k : ℕ) (hk : 4 ≤ k) (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    {ζ : ℝ} (P : CoreExtractionParameters k η ζ)
    (q : Fin P.stageBound) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n),
      ∀ A : CleanedCoreStart k n C η P.tailScale, ∀ seed : Fin n,
        (∀ v : Fin n,
          (A.cleaned.redDegree v : ℝ) ≤
            (A.cleaned.redDegree seed : ℝ) + P.levelError q.castSucc n) →
        (η / 4) * (n : ℝ) ≤ (A.cleaned.redDegree seed : ℝ) →
        (SimpleGraph.turanNumber (A.cleaned.redDegree seed) (delta k) : ℝ) -
              coreExtractionESModulus k (P.betaSeq q.succ) *
                (A.cleaned.redDegree seed : ℝ) ^ 2 ≤
            ((redGreenNeighborhoodGraph A.cleaned seed).edgeFinset.card : ℝ) := by
  have hk3 : 3 ≤ k := by omega
  have hdelta := P.localDelta_mem hk3 hη
  have halpha := P.localTuranAlpha_mem hη q
  obtain ⟨nLocal, hLocal⟩ :=
    locallyTuran k hk P.localDelta (P.localTuranAlpha q) hdelta halpha
  let nAbsorb : ℕ :=
    Nat.ceil (2400 / Real.sqrt (P.betaSeq q.castSucc))
  refine ⟨max nLocal nAbsorb, ?_⟩
  intro n hn C A seed hnearMax hseedLarge
  have hnLocal : nLocal ≤ n := (le_max_left _ _).trans hn
  have hnAbsorb : nAbsorb ≤ n := (le_max_right _ _).trans hn
  have hsqrtPos : 0 < Real.sqrt (P.betaSeq q.castSucc) :=
    Real.sqrt_pos.2 (P.betaSeq_pos q.castSucc)
  have habsorbCast :
      2400 / Real.sqrt (P.betaSeq q.castSucc) ≤ (n : ℝ) := by
    calc
      2400 / Real.sqrt (P.betaSeq q.castSucc) ≤
          (nAbsorb : ℕ) := by
        exact Nat.le_ceil _
      _ ≤ (n : ℝ) := by exact_mod_cast hnAbsorb
  have habsorb :
      (2400 : ℝ) ≤ Real.sqrt (P.betaSeq q.castSucc) * (n : ℝ) := by
    calc
      (2400 : ℝ) ≤ (n : ℝ) * Real.sqrt (P.betaSeq q.castSucc) :=
        (div_le_iff₀ hsqrtPos).mp habsorbCast
      _ = Real.sqrt (P.betaSeq q.castSucc) * (n : ℝ) := by ring
  have hlevelAlpha :
      P.levelError q.castSucc n ≤ P.localTuranAlpha q * (n : ℝ) := by
    unfold CoreExtractionParameters.levelError
      CoreExtractionParameters.localTuranAlpha
    have hmasterPos := P.master_pos
    have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsqrtNonneg := Real.sqrt_nonneg (P.betaSeq q.castSucc)
    nlinarith [mul_nonneg hsqrtNonneg hnNonneg]
  have hmax : ∀ v : Fin n,
      (A.cleaned.redDegree v : ℝ) ≤
        (A.cleaned.redDegree seed : ℝ) +
          P.localTuranAlpha q * (n : ℝ) := by
    intro v
    exact (hnearMax v).trans
      (add_le_add (le_refl (A.cleaned.redDegree seed : ℝ)) hlevelAlpha)
  have htheta : η / 4 ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · exact div_pos hη.1 (by norm_num)
    · exact (div_le_self hη.1.le (by norm_num)).trans hη.2.le
  have hnear := A.cleaned_nearExtremal_localDelta P
  have hturan := hLocal n hnLocal A.cleaned A.cleaned_mem_Ck hnear seed hmax
    (η / 4) htheta hseedLarge
  have hcoefficient := P.localTuranCoefficient_lt_ES hk3 hη q
  have hdegreeSq : 0 ≤ (A.cleaned.redDegree seed : ℝ) ^ 2 := sq_nonneg _
  calc
    (SimpleGraph.turanNumber (A.cleaned.redDegree seed) (delta k) : ℝ) -
          coreExtractionESModulus k (P.betaSeq q.succ) *
            (A.cleaned.redDegree seed : ℝ) ^ 2 ≤
        (SimpleGraph.turanNumber (A.cleaned.redDegree seed) (delta k) : ℝ) -
          (12 * (Real.sqrt P.localDelta / (η / 4) +
            P.localTuranAlpha q / (η / 4))) *
              (A.cleaned.redDegree seed : ℝ) ^ 2 := by
      nlinarith
    _ ≤ ((redGreenNeighborhoodGraph A.cleaned seed).edgeFinset.card : ℝ) :=
      hturan

/-! ## Stage F2: seed partitions and finite typical-set cleaning -/

section CoreSeedStageCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The restricted degree sum of a finite simple graph counts every edge
internal to the restricting set twice.  This version is used directly on
the red--green graph of a seed neighborhood. -/
theorem sum_internalNeighborCard_eq_two_mul_edgeCard
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∑ v ∈ S, (G.neighborFinset v ∩ S).card =
      2 * (G.edgeFinset ∩ S.sym2).card := by
  classical
  let H : SimpleGraph V := {
    Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
    symm.symm x y h := ⟨h.1.symm, h.2.2, h.2.1⟩
    loopless.irrefl x h := G.irrefl h.1 }
  have hdeg {v : V} (hv : v ∈ S) :
      H.degree v = (G.neighborFinset v ∩ S).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp [H, hv]
  have hdegZero {v : V} (hv : v ∉ S) : H.degree v = 0 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
    ext w
    simp [H, hv]
  have hedge : H.edgeFinset = G.edgeFinset ∩ S.sym2 := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y => simp [H]
  calc
    ∑ v ∈ S, (G.neighborFinset v ∩ S).card =
        ∑ v ∈ S, H.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (hdeg hv).symm
    _ = ∑ v, H.degree v := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro v _ hv
      exact hdegZero hv
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    _ = 2 * (G.edgeFinset ∩ S.sym2).card := by rw [hedge]

/-- Controlled vertices having at most `cap` red--green neighbors inside
their seed part.  Equivalently, these are the high-internal-blue vertices
used in the paper's sets `W_i^(q)`. -/
def coreSeedTypicalSubtype (G : SimpleGraph V) [DecidableRel G.Adj]
    (S control : Finset V) (cap : ℕ) : Finset V :=
  S.filter fun v ↦ v ∈ control ∧ (G.neighborFinset v ∩ S).card ≤ cap

@[simp]
theorem mem_coreSeedTypicalSubtype
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S control : Finset V) (cap : ℕ) (v : V) :
    v ∈ coreSeedTypicalSubtype G S control cap ↔
      v ∈ S ∧ v ∈ control ∧
        (G.neighborFinset v ∩ S).card ≤ cap := by
  simp [coreSeedTypicalSubtype]

/-- The exact finite Markov estimate behind the typical-set construction.
The denominator `cap + 1` is the integer gap between selected and discarded
vertices; no asymptotic notation or rounding convention is hidden here. -/
theorem coreSeedTypicalSubtype_card_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S control : Finset V) (cap : ℕ) (edgeError d controlLoss : ℝ)
    (hedge : ((G.edgeFinset ∩ S.sym2).card : ℝ) ≤ edgeError * d ^ 2)
    (hcontrol : ((S.filter fun v ↦ v ∉ control).card : ℝ) ≤
      controlLoss) :
    (S.card : ℝ) - controlLoss -
        2 * edgeError * d ^ 2 / (cap + 1 : ℝ) ≤
      ((coreSeedTypicalSubtype G S control cap).card : ℝ) := by
  classical
  let T := coreSeedTypicalSubtype G S control cap
  let B := S.filter fun v ↦ cap < (G.neighborFinset v ∩ S).card
  let E := S.filter fun v ↦ v ∉ control
  have hBsum : B.card * (cap + 1) ≤
      ∑ v ∈ S, (G.neighborFinset v ∩ S).card := by
    calc
      B.card * (cap + 1) = ∑ _v ∈ B, (cap + 1) := by simp
      _ ≤ ∑ v ∈ B, (G.neighborFinset v ∩ S).card := by
        apply Finset.sum_le_sum
        intro v hv
        have hv' := Finset.mem_filter.mp hv
        omega
      _ ≤ ∑ v ∈ S, (G.neighborFinset v ∩ S).card := by
        apply Finset.sum_le_sum_of_subset
        intro v hv
        exact (Finset.mem_filter.mp hv).1
  rw [sum_internalNeighborCard_eq_two_mul_edgeCard G S] at hBsum
  have hBsumReal : (B.card : ℝ) * (cap + 1 : ℝ) ≤
      2 * ((G.edgeFinset ∩ S.sym2).card : ℝ) := by
    exact_mod_cast hBsum
  have hBnumerator : (B.card : ℝ) * (cap + 1 : ℝ) ≤
      2 * edgeError * d ^ 2 := by
    calc
      (B.card : ℝ) * (cap + 1 : ℝ) ≤
          2 * ((G.edgeFinset ∩ S.sym2).card : ℝ) := hBsumReal
      _ ≤ 2 * (edgeError * d ^ 2) :=
        mul_le_mul_of_nonneg_left hedge (by norm_num)
      _ = 2 * edgeError * d ^ 2 := by ring
  have hcap : (0 : ℝ) < (cap + 1 : ℝ) := by positivity
  have hB : (B.card : ℝ) ≤
      2 * edgeError * d ^ 2 / (cap + 1 : ℝ) := by
    rw [le_div_iff₀ hcap]
    simpa [mul_comm] using hBnumerator
  have hdiff : S \ T ⊆ E ∪ B := by
    intro v hv
    have hvS := (Finset.mem_sdiff.mp hv).1
    have hvT := (Finset.mem_sdiff.mp hv).2
    by_cases hvcontrol : v ∈ control
    · have hvlarge : cap < (G.neighborFinset v ∩ S).card := by
        by_contra hnot
        apply hvT
        exact (mem_coreSeedTypicalSubtype G S control cap v).2
          ⟨hvS, hvcontrol, by omega⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvS, hvlarge⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvS, hvcontrol⟩)
  have hcardDiff := Finset.card_le_card hdiff
  have hcardUnion := Finset.card_union_le E B
  have hbase := Finset.card_le_card_sdiff_add_card (s := S) (t := T)
  have hcardNat : S.card ≤ T.card + E.card + B.card := by omega
  have hcardReal : (S.card : ℝ) ≤
      (T.card : ℝ) + (E.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast hcardNat
  have hE : (E.card : ℝ) ≤ controlLoss := by simpa [E] using hcontrol
  linarith

/-- Inside a part of a red neighborhood, blue neighbors and red--green
neighbors partition all other vertices of the part. -/
theorem blueDegreeIn_add_redGreenInternalDegree
    (C : ColoredGraph V) (x : V)
    (S : Finset {v // v ∈ C.redNeighborFinset x})
    (u : {v // v ∈ C.redNeighborFinset x}) (hu : u ∈ S) :
    C.blueDegreeIn (u : V) (S.map (Function.Embedding.subtype _)) +
        (((redGreenNeighborhoodGraph C x).neighborFinset u) ∩ S).card =
      S.card - 1 := by
  classical
  let emb : {v // v ∈ C.redNeighborFinset x} ↪ V :=
    Function.Embedding.subtype _
  let blue : Finset {v // v ∈ C.redNeighborFinset x} :=
    (S.erase u).filter fun v ↦ C.color (u : V) (v : V) = .blue
  let nonblue : Finset {v // v ∈ C.redNeighborFinset x} :=
    (S.erase u).filter fun v ↦ C.color (u : V) (v : V) ≠ .blue
  have hpartition : blue ∪ nonblue = S.erase u := by
    ext v
    by_cases hcolor : C.color (u : V) (v : V) = .blue <;>
      simp [blue, nonblue, hcolor]
  have hdisj : Disjoint blue nonblue := by
    simp [blue, nonblue, Finset.disjoint_filter]
  have hblue : C.blueDegreeIn (u : V) (S.map emb) = blue.card := by
    have hblueFin : blue.map emb =
        C.neighborFinset .blue (u : V) ∩ S.map emb := by
      ext v
      rw [Finset.mem_map, Finset.mem_inter]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' := Finset.mem_filter.mp hw
        have hwErase := Finset.mem_erase.mp hw'.1
        refine ⟨(C.mem_neighborFinset .blue (u : V) (w : V)).2
            ⟨?_, hw'.2⟩, Finset.mem_map.mpr ⟨w, hwErase.2, rfl⟩⟩
        intro huw
        exact hwErase.1 (Subtype.ext huw).symm
      · rintro ⟨hvblue, hvS⟩
        rcases Finset.mem_map.mp hvS with ⟨w, hwS, rfl⟩
        have hwblue := (C.mem_neighborFinset .blue (u : V) (w : V)).1 hvblue
        refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hwS⟩,
          hwblue.2⟩, rfl⟩
        intro hwu
        exact hwblue.1 (congrArg Subtype.val hwu.symm)
    unfold blueDegreeIn degreeIn neighborFinsetIn
    rw [← hblueFin, Finset.card_map]
  have hnonblue :
      (((redGreenNeighborhoodGraph C x).neighborFinset u) ∩ S).card =
        nonblue.card := by
    congr 1
    ext v
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    simp only [redGreenNeighborhoodGraph_adj]
    simp [nonblue, ne_comm, and_assoc, and_comm]
  rw [hblue, hnonblue, ← Finset.card_union_of_disjoint hdisj, hpartition,
    Finset.card_erase_of_mem hu]

/-- Weighted-degree and red-degree control turn a high internal blue degree
into a low blue degree outside the part. -/
theorem externalBlueDegree_le_of_controls (k : ℕ) (hk : 3 ≤ k)
    (C : ColoredGraph V) (v : V) (S : Finset V) (inside : ℕ)
    (reference redError weightedError : ℝ)
    (hinside : inside ≤ C.blueDegreeIn v S)
    (hred : (C.redDegree v : ℝ) ≤ reference + redError)
    (hweighted : |(weightedDegree k C v : ℝ)| ≤ weightedError) :
    (C.blueDegreeIn v Sᶜ : ℝ) ≤
      (reference + redError + weightedError) / (delta k : ℝ) - inside := by
  have hDeltaNat : 0 < delta k := by unfold delta; omega
  have hDelta : (0 : ℝ) < (delta k : ℝ) := by exact_mod_cast hDeltaNat
  have hDlower := (abs_le.mp hweighted).1
  have hweightedIdentity : (weightedDegree k C v : ℝ) =
      (C.redDegree v : ℝ) - (delta k : ℝ) * (C.blueDegree v : ℝ) := by
    unfold weightedDegree
    push_cast
    rfl
  have hsplitNat := degreeIn_add_degreeIn_compl C .blue v S
  have hsplit : (C.blueDegreeIn v S : ℝ) +
      (C.blueDegreeIn v Sᶜ : ℝ) = (C.blueDegree v : ℝ) := by
    exact_mod_cast hsplitNat
  have hinsideReal : (inside : ℝ) ≤ (C.blueDegreeIn v S : ℝ) := by
    exact_mod_cast hinside
  rw [hweightedIdentity] at hDlower
  rw [le_sub_iff_add_le, le_div_iff₀ hDelta]
  nlinarith

/-- Weighted-degree control and a high internal blue degree give the
corresponding explicit lower bound on total red degree. -/
theorem totalRedDegree_lower_of_controls (k : ℕ) (C : ColoredGraph V)
    (v : V) (S : Finset V) (inside : ℕ) (weightedError : ℝ)
    (hinside : inside ≤ C.blueDegreeIn v S)
    (hweighted : |(weightedDegree k C v : ℝ)| ≤ weightedError) :
    (delta k : ℝ) * inside - weightedError ≤ (C.redDegree v : ℝ) := by
  have hDlower := (abs_le.mp hweighted).1
  have hweightedIdentity : (weightedDegree k C v : ℝ) =
      (C.redDegree v : ℝ) - (delta k : ℝ) * (C.blueDegree v : ℝ) := by
    unfold weightedDegree
    push_cast
    rfl
  have hdegreeIn : C.blueDegreeIn v S ≤ C.blueDegree v := by
    change C.degreeIn .blue v S ≤ C.degree .blue v
    unfold degree degreeIn neighborFinsetIn
    exact Finset.card_le_card Finset.inter_subset_left
  have hinsideTotal : inside ≤ C.blueDegree v := hinside.trans hdegreeIn
  have hinsideReal : (inside : ℝ) ≤ (C.blueDegree v : ℝ) := by
    exact_mod_cast hinsideTotal
  have hDelta : (0 : ℝ) ≤ (delta k : ℝ) := by positivity
  rw [hweightedIdentity] at hDlower
  nlinarith

/-! ### The integral nonblue cap -/

/-- The exact natural cap used when discarding atypical vertices from a seed
part.  It is the ceiling of `√ε m`, so the finite Markov denominator is never
silently replaced by a real number. -/
noncomputable def coreSeedNonblueCap (ε : ℝ) (m : ℕ) : ℕ :=
  ⌈Real.sqrt ε * (m : ℝ)⌉₊

theorem coreSeedNonblueCap_lower {ε : ℝ} {m : ℕ} :
    Real.sqrt ε * (m : ℝ) ≤ (coreSeedNonblueCap ε m : ℝ) := by
  exact Nat.le_ceil _

theorem coreSeedNonblueCap_lt_add_one {ε : ℝ} (hε : 0 ≤ ε) (m : ℕ) :
    (coreSeedNonblueCap ε m : ℝ) <
      Real.sqrt ε * (m : ℝ) + 1 := by
  exact Nat.ceil_lt_add_one (mul_nonneg (Real.sqrt_nonneg ε) (Nat.cast_nonneg m))

/-- With the ceiling cap, the exact finite Markov loss is at most
`2 √ε m`. -/
theorem coreSeed_markovQuotient_le {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 0 < m) :
    2 * ε * (m : ℝ) ^ 2 /
        (coreSeedNonblueCap ε m + 1 : ℝ) ≤
      2 * Real.sqrt ε * (m : ℝ) := by
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hx : 0 < Real.sqrt ε * (m : ℝ) := mul_pos hsqrt hmR
  have hcap := coreSeedNonblueCap_lower (ε := ε) (m := m)
  have hden : 0 < (coreSeedNonblueCap ε m + 1 : ℝ) := by positivity
  have hdenLower :
      Real.sqrt ε * (m : ℝ) ≤
        (coreSeedNonblueCap ε m + 1 : ℝ) := by
    exact hcap.trans (by norm_num)
  rw [div_le_iff₀ hden]
  have hmul := mul_le_mul_of_nonneg_left hdenLower (by positivity :
    0 ≤ 2 * Real.sqrt ε * (m : ℝ))
  have hsquare : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
  nlinarith

end CoreSeedStageCounting

section CoreSeedStage

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The controlled vertices of a seed's red neighborhood, viewed on its
subtype. -/
def coreSeedControlSubtype (C : ColoredGraph V) (x : V)
    (control : Finset V) : Finset {v // v ∈ C.redNeighborFinset x} :=
  Finset.univ.filter fun v ↦ (v : V) ∈ control

/-- The ambient typical set in part `i` of a seed partition. -/
def coreSeedTypicalSet {k : ℕ} {C : ColoredGraph V} {x : V}
    {edgeError : ℝ} (P : CoreSeedPartition k C x edgeError)
    (control : Finset V) (cap : ℕ) (i : Fin (delta k)) : Finset V :=
  (coreSeedTypicalSubtype (redGreenNeighborhoodGraph C x) (P.parts i)
      (coreSeedControlSubtype C x control) cap).map
    (Function.Embedding.subtype _)

/-- The complete output of one seed stage before the overlap quotient.

The natural parameter `cap` is the allowed number of red--green neighbors
inside a part.  Thus `part.card - 1 - cap` is an exact lower bound on the
internal blue degree.  The three final fields are the finite, explicit
versions of the paper's high-internal-blue, low-external-blue, and
high-total-red estimates. -/
structure CoreSeedStage
    (k : ℕ) (C : ColoredGraph V) (edgeError : ℝ)
    (control : Finset V) (cap : ℕ)
    (reference redError weightedError controlLoss : ℝ) where
  /-- The seed vertex. -/
  seed : V
  /-- The genuine `Δ`-part partition of the seed's red neighborhood. -/
  partition : CoreSeedPartition k C seed edgeError
  /-- The red neighborhood, retained explicitly for later iteration unions. -/
  redNeighborhood : Finset V
  redNeighborhood_eq : redNeighborhood = C.redNeighborFinset seed
  /-- The partition parts mapped back to the ambient vertex type. -/
  parts : Fin (delta k) → Finset V
  parts_eq : parts = partition.ambientPart
  parts_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (delta k))) parts
  parts_cover :
    (Finset.univ : Finset (Fin (delta k))).biUnion parts = redNeighborhood
  /-- The exact Erdős--Simonovits internal-edge conclusion. -/
  internalRedGreenSmall :
    (∑ i : Fin (delta k),
      (((redGreenNeighborhoodGraph C seed).edgeFinset ∩
        (partition.parts i).sym2).card : ℝ)) ≤
      edgeError * (C.redDegree seed : ℝ) ^ 2
  /-- The exact part-balance conclusion in ambient form. -/
  partBalanced : ∀ i,
    |((parts i).card : ℝ) -
        (C.redDegree seed : ℝ) / (delta k : ℝ)| ≤
      edgeError * (C.redDegree seed : ℝ)
  /-- The controlled high-blue subsets `W_i`. -/
  typical : Fin (delta k) → Finset V
  typical_eq : typical = coreSeedTypicalSet partition control cap
  typical_subset_part : ∀ i, typical i ⊆ parts i
  typical_controlled : ∀ i, typical i ⊆ control
  /-- Exact Markov size bound, combined with part balance. -/
  typicalLower : ∀ i,
    (C.redDegree seed : ℝ) / (delta k : ℝ) -
        edgeError * (C.redDegree seed : ℝ) - controlLoss -
          2 * edgeError * (C.redDegree seed : ℝ) ^ 2 /
            (cap + 1 : ℝ) ≤
      ((typical i).card : ℝ)
  /-- Every typical vertex has high blue degree inside its own part. -/
  highInternalBlue : ∀ i, ∀ v ∈ typical i,
    (parts i).card - 1 - cap ≤ C.blueDegreeIn v (parts i)
  /-- Every typical vertex has explicitly bounded blue degree off its part. -/
  lowExternalBlue : ∀ i, ∀ v ∈ typical i,
    (C.blueDegreeIn v (parts i)ᶜ : ℝ) ≤
      (reference + redError + weightedError) / (delta k : ℝ) -
        (((parts i).card - 1 - cap : ℕ) : ℝ)
  /-- Every typical vertex has the corresponding explicit red-degree lower
  bound. -/
  highTotalRed : ∀ i, ∀ v ∈ typical i,
    (delta k : ℝ) * (((parts i).card - 1 - cap : ℕ) : ℝ) -
        weightedError ≤ (C.redDegree v : ℝ)

set_option maxHeartbeats 800000 in
-- Dependent subtype maps and exact cast chains make this constructor costly to elaborate.
/-- Construct all typical subsets of an Erdős--Simonovits seed partition by
one exact finite Markov argument.

`controlLoss` records the vertices of each subtype part outside the set on
which red and weighted degrees are controlled.  In the first paper stage it
is at most one, because only the inserted maximum-red-degree seed may lie
outside the fixed weighted-degree good set. -/
theorem exists_coreSeedStage_of_partition (k : ℕ) (hk : 3 ≤ k)
    (C : ColoredGraph V) (seed : V) (edgeError : ℝ)
    (P : CoreSeedPartition k C seed edgeError)
    (control : Finset V) (cap : ℕ)
    (reference redError weightedError controlLoss : ℝ)
    (hcontrolLoss : ∀ i,
      (((P.parts i).filter
        fun v : {w // w ∈ C.redNeighborFinset seed} ↦
          (v : V) ∉ control).card : ℝ) ≤ controlLoss)
    (hred : ∀ v ∈ control,
      (C.redDegree v : ℝ) ≤ reference + redError)
    (hweighted : ∀ v ∈ control,
      |(weightedDegree k C v : ℝ)| ≤ weightedError) :
    ∃ S : CoreSeedStage k C edgeError control cap
      reference redError weightedError controlLoss, S.seed = seed := by
  classical
  let parts : Fin (delta k) → Finset V := P.ambientPart
  let typical : Fin (delta k) → Finset V :=
    coreSeedTypicalSet P control cap
  have hpartDisjoint :
      Set.PairwiseDisjoint (Set.univ : Set (Fin (delta k))) parts :=
    P.ambientParts_pairwiseDisjoint
  have hpartCover :
      (Finset.univ : Finset (Fin (delta k))).biUnion parts =
        C.redNeighborFinset seed := P.ambientParts_cover
  have htypicalSubset : ∀ i, typical i ⊆ parts i := by
    intro i v hv
    rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
    exact Finset.mem_map.mpr ⟨u,
      (mem_coreSeedTypicalSubtype _ _ _ _ _).1 hu |>.1, rfl⟩
  have htypicalControl : ∀ i, typical i ⊆ control := by
    intro i v hv
    rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
    have huControl :=
      (mem_coreSeedTypicalSubtype _ _ _ _ _).1 hu |>.2.1
    simpa [coreSeedControlSubtype] using huControl
  have htypicalLower : ∀ i,
      (C.redDegree seed : ℝ) / (delta k : ℝ) -
          edgeError * (C.redDegree seed : ℝ) - controlLoss -
            2 * edgeError * (C.redDegree seed : ℝ) ^ 2 /
              (cap + 1 : ℝ) ≤
        ((typical i).card : ℝ) := by
    intro i
    have hedgeI :
        (((redGreenNeighborhoodGraph C seed).edgeFinset ∩
          (P.parts i).sym2).card : ℝ) ≤
            edgeError * (C.redDegree seed : ℝ) ^ 2 := by
      calc
        (((redGreenNeighborhoodGraph C seed).edgeFinset ∩
            (P.parts i).sym2).card : ℝ) ≤
            ∑ j : Fin (delta k),
              (((redGreenNeighborhoodGraph C seed).edgeFinset ∩
                (P.parts j).sym2).card : ℝ) := by
          exact Finset.single_le_sum
            (f := fun j : Fin (delta k) ↦
              (((redGreenNeighborhoodGraph C seed).edgeFinset ∩
                (P.parts j).sym2).card : ℝ))
            (fun _ _ ↦ Nat.cast_nonneg _) (Finset.mem_univ i)
        _ ≤ edgeError * (C.redDegree seed : ℝ) ^ 2 :=
          P.internalRedGreenSmall
    have hcontrolI :
        (((P.parts i).filter
          fun v : {w // w ∈ C.redNeighborFinset seed} ↦
            v ∉ coreSeedControlSubtype C seed control).card : ℝ) ≤
              controlLoss := by
      simpa [coreSeedControlSubtype] using hcontrolLoss i
    have hmarkov := coreSeedTypicalSubtype_card_lower
      (redGreenNeighborhoodGraph C seed) (P.parts i)
      (coreSeedControlSubtype C seed control) cap edgeError
      (C.redDegree seed : ℝ) controlLoss hedgeI hcontrolI
    have hbalance := P.balanced i
    have hpartLower :
        (C.redDegree seed : ℝ) / (delta k : ℝ) -
            edgeError * (C.redDegree seed : ℝ) ≤
          ((P.parts i).card : ℝ) := by
      rw [abs_le] at hbalance
      linarith
    have htypCard : (typical i).card =
        (coreSeedTypicalSubtype (redGreenNeighborhoodGraph C seed)
          (P.parts i) (coreSeedControlSubtype C seed control) cap).card := by
      simp [typical, coreSeedTypicalSet]
    rw [htypCard]
    linarith
  have hhighBlue : ∀ i, ∀ v ∈ typical i,
      (parts i).card - 1 - cap ≤ C.blueDegreeIn v (parts i) := by
    intro i v hv
    rcases Finset.mem_map.mp hv with ⟨u, hu, rfl⟩
    have huData := (mem_coreSeedTypicalSubtype _ _ _ _ _).1 hu
    have hsum := blueDegreeIn_add_redGreenInternalDegree
      C seed (P.parts i) u huData.1
    have hsum' : C.blueDegreeIn (u : V) (P.ambientPart i) +
        (((redGreenNeighborhoodGraph C seed).neighborFinset u) ∩
          P.parts i).card = (P.parts i).card - 1 := by
      simpa [CoreSeedPartition.ambientPart] using hsum
    have hcap := huData.2.2
    change (P.ambientPart i).card - 1 - cap ≤
      C.blueDegreeIn (u : V) (P.ambientPart i)
    rw [P.card_ambientPart]
    omega
  have hlowExternal : ∀ i, ∀ v ∈ typical i,
      (C.blueDegreeIn v (parts i)ᶜ : ℝ) ≤
        (reference + redError + weightedError) / (delta k : ℝ) -
          (((parts i).card - 1 - cap : ℕ) : ℝ) := by
    intro i v hv
    exact externalBlueDegree_le_of_controls k hk C v (parts i)
      ((parts i).card - 1 - cap) reference redError weightedError
      (hhighBlue i v hv) (hred v (htypicalControl i hv))
      (hweighted v (htypicalControl i hv))
  have hhighRed : ∀ i, ∀ v ∈ typical i,
      (delta k : ℝ) * (((parts i).card - 1 - cap : ℕ) : ℝ) -
          weightedError ≤ (C.redDegree v : ℝ) := by
    intro i v hv
    exact totalRedDegree_lower_of_controls k C v (parts i)
      ((parts i).card - 1 - cap) weightedError
      (hhighBlue i v hv) (hweighted v (htypicalControl i hv))
  exact ⟨{
    seed := seed
    partition := P
    redNeighborhood := C.redNeighborFinset seed
    redNeighborhood_eq := rfl
    parts := parts
    parts_eq := rfl
    parts_pairwiseDisjoint := hpartDisjoint
    parts_cover := hpartCover
    internalRedGreenSmall := P.internalRedGreenSmall
    partBalanced := by simpa [parts] using P.balanced
    typical := typical
    typical_eq := rfl
    typical_subset_part := htypicalSubset
    typical_controlled := htypicalControl
    typicalLower := htypicalLower
    highInternalBlue := hhighBlue
    lowExternalBlue := hlowExternal
    highTotalRed := hhighRed
  }, rfl⟩

/-- A near-Turán red neighborhood produces a complete seed stage after one
application of the uniform seed-partition theorem and the exact Markov
constructor above.

The partition theorem itself contains the separate arguments for `k = 3`
(the red neighborhood is a blue clique) and `k ≥ 4` (Erdős--Simonovits).
Thus callers use this single interface in every iteration stage. -/
theorem exists_coreSeedStage_of_nearTuran (k : ℕ) (hk : 3 ≤ k)
    (edgeError : ℝ) (hEdgeError : 0 < edgeError) :
    ∃ nSeed : ℕ,
      ∀ {W : Type*} [Fintype W] [DecidableEq W],
      ∀ (C : ColoredGraph W) (hC : C.FkFree k) (seed : W),
        nSeed ≤ C.redDegree seed →
        (SimpleGraph.turanNumber (C.redDegree seed) (delta k) : ℝ) -
              coreExtractionESModulus k edgeError *
                (C.redDegree seed : ℝ) ^ 2 ≤
            ((redGreenNeighborhoodGraph C seed).edgeFinset.card : ℝ) →
        ∀ (control : Finset W) (cap : ℕ)
          (reference redError weightedError controlLoss : ℝ),
          (((Finset.univ :
              Finset {v // v ∈ C.redNeighborFinset seed}).filter
                fun v : {w // w ∈ C.redNeighborFinset seed} ↦
                  (v : W) ∉ control).card : ℝ) ≤ controlLoss →
          (∀ v ∈ control,
            (C.redDegree v : ℝ) ≤ reference + redError) →
          (∀ v ∈ control,
            |(weightedDegree k C v : ℝ)| ≤ weightedError) →
          ∃ S : CoreSeedStage k C edgeError control cap
            reference redError weightedError controlLoss, S.seed = seed := by
  classical
  obtain ⟨nSeed, hpartition⟩ :=
    exists_coreSeedPartition (k := k) hk hEdgeError
  refine ⟨nSeed, ?_⟩
  intro W
  intro _instFintype
  intro _instDecidableEq
  intro C
  intro hC
  intro seed
  intro hsize
  intro hnear
  intro control
  intro cap
  intro reference
  intro redError
  intro weightedError
  intro controlLoss
  intro hcontrol
  intro hred
  intro hweighted
  obtain ⟨P⟩ := hpartition (W := W) C hC seed hsize hnear
  apply exists_coreSeedStage_of_partition k hk C seed edgeError P control cap
    reference redError weightedError controlLoss
  · intro i
    calc
      (((P.parts i).filter
          fun v : {w // w ∈ C.redNeighborFinset seed} ↦
            (v : W) ∉ control).card : ℝ) ≤
          (((Finset.univ :
            Finset {w // w ∈ C.redNeighborFinset seed}).filter
              fun v : {w // w ∈ C.redNeighborFinset seed} ↦
                (v : W) ∉ control).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (by
          intro v hv
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2⟩)
      _ ≤ controlLoss := hcontrol
  · exact hred
  · exact hweighted

end CoreSeedStage

/-! ## Uniform seed-stage estimates -/

section UniformCoreSeedStage

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A seed stage after all estimates have been transferred from the current
seed degree to one common real reference size.  This is the exact finite
version of the paper's uniform estimates (Aj-sizes-uniform)--(Wj-good-3).

Keeping the parts as well as their typical subsets is useful twice: the
parts certify the overlap dichotomy, while the typical subsets are the
members of the eventual overlap quotient. -/
structure UniformCoreSeedStage
    (k : ℕ) (C : ColoredGraph V) (control : Finset V)
    (reference error : ℝ) where
  seed : V
  redNeighborhood : Finset V
  redNeighborhood_eq : redNeighborhood = C.redNeighborFinset seed
  parts : Fin (delta k) → Finset V
  parts_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (delta k))) parts
  parts_cover :
    (Finset.univ : Finset (Fin (delta k))).biUnion parts = redNeighborhood
  typical : Fin (delta k) → Finset V
  typical_subset_part : ∀ i, typical i ⊆ parts i
  typical_controlled : ∀ i, typical i ⊆ control
  /-- The integral cap on red--green neighbors inside a stage part. -/
  internalNonblueCap : ℕ
  seedRedNearReference :
    |(C.redDegree seed : ℝ) - reference| ≤ error
  partBalanced : ∀ i,
    |((parts i).card : ℝ) - reference / (delta k : ℝ)| ≤ error
  typicalBalanced : ∀ i,
    |((typical i).card : ℝ) - reference / (delta k : ℝ)| ≤ error
  partTypicalLoss : ∀ i,
    (((parts i \ typical i).card : ℕ) : ℝ) ≤ 2 * error
  highInternalBlue : ∀ i, ∀ v ∈ typical i,
    reference / (delta k : ℝ) - error ≤
      (C.blueDegreeIn v (parts i) : ℝ)
  lowInternalNonblue : ∀ i, ∀ v ∈ typical i,
    C.redDegreeIn v (parts i) + C.greenDegreeIn v (parts i) ≤
      internalNonblueCap
  lowExternalBlue : ∀ i, ∀ v ∈ typical i,
    (C.blueDegreeIn v (parts i)ᶜ : ℝ) ≤ error
  highTotalRed : ∀ i, ∀ v ∈ typical i,
    reference - error ≤ (C.redDegree v : ℝ)
  totalBlueUpper : ∀ i, ∀ v ∈ typical i,
    (C.blueDegree v : ℝ) ≤ reference / (delta k : ℝ) + 2 * error

/-- Casting a truncated natural subtraction loses no more than the amount
subtracted.  It is the small bridge needed to turn the integral Markov cap
into the real uniform stage error. -/
theorem cast_sub_one_sub_lower (a b : ℕ) :
    (a : ℝ) - ((b + 1 : ℕ) : ℝ) ≤ ((a - 1 - b : ℕ) : ℝ) := by
  by_cases h : b + 1 ≤ a
  · have heq : a - 1 - b = a - (b + 1) := by omega
    rw [heq, Nat.cast_sub h]
  · have ha : a ≤ b := by omega
    have haR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast ha
    have heq : a - 1 - b = 0 := by omega
    rw [heq, Nat.cast_zero]
    norm_num
    linarith

/-- Transfer a raw `CoreSeedStage` to a common reference size.

The hypotheses are only scalar error allocations.  Every combinatorial
statement is inherited from the raw seed constructor.  `thresholdLoss` is
kept separate because the same lower bound on `part.card - 1 - cap` feeds
both the external-blue and total-red estimates. -/
noncomputable def CoreSeedStage.toUniform
    {k : ℕ} (hk : 3 ≤ k) {C : ColoredGraph V}
    {edgeError : ℝ} {control : Finset V} {cap : ℕ}
    {rawReference redError weightedError controlLoss : ℝ}
    (S : CoreSeedStage k C edgeError control cap
      rawReference redError weightedError controlLoss)
    (reference error seedError thresholdLoss : ℝ)
    (hseed : |(C.redDegree S.seed : ℝ) - reference| ≤ seedError)
    (hseedError : seedError ≤ error)
    (hpart : edgeError * (C.redDegree S.seed : ℝ) +
        seedError / (delta k : ℝ) ≤ error)
    (htypical : seedError / (delta k : ℝ) +
        edgeError * (C.redDegree S.seed : ℝ) + controlLoss +
          2 * edgeError * (C.redDegree S.seed : ℝ) ^ 2 /
            (cap + 1 : ℝ) ≤ error)
    (hthreshold : seedError / (delta k : ℝ) +
        edgeError * (C.redDegree S.seed : ℝ) + (cap + 1 : ℝ) ≤
          thresholdLoss)
    (hthresholdError : thresholdLoss ≤ error)
    (hexternal :
      (rawReference + redError + weightedError - reference) /
          (delta k : ℝ) + thresholdLoss ≤ error)
    (hred : (delta k : ℝ) * thresholdLoss + weightedError ≤ error) :
    UniformCoreSeedStage k C control reference error := by
  classical
  have hdeltaNat : 0 < delta k := by
    unfold delta
    omega
  have hdelta : 0 < (delta k : ℝ) := by exact_mod_cast hdeltaNat
  let d : ℝ := C.redDegree S.seed
  have hseedBounds : -seedError ≤ d - reference ∧
      d - reference ≤ seedError := by
    simpa [d, abs_le] using (show |d - reference| ≤ seedError from hseed)
  have hseedDivLower :
      reference / (delta k : ℝ) - seedError / (delta k : ℝ) ≤
        d / (delta k : ℝ) := by
    have := (div_le_div_iff_of_pos_right hdelta).2 hseedBounds.1
    rw [sub_div] at this
    have hadd := add_le_add_left this (reference / (delta k : ℝ))
    have hdirect : reference / (delta k : ℝ) -
        seedError / (delta k : ℝ) ≤ d / (delta k : ℝ) := by
      calc
        reference / (delta k : ℝ) - seedError / (delta k : ℝ) =
            -seedError / (delta k : ℝ) + reference / (delta k : ℝ) := by ring
        _ ≤ (d / (delta k : ℝ) - reference / (delta k : ℝ)) +
            reference / (delta k : ℝ) := hadd
        _ = d / (delta k : ℝ) := by ring
    exact hdirect
  have hseedDivUpper :
      d / (delta k : ℝ) ≤
        reference / (delta k : ℝ) + seedError / (delta k : ℝ) := by
    have := (div_le_div_iff_of_pos_right hdelta).2 hseedBounds.2
    rw [sub_div] at this
    have hadd := add_le_add_left this (reference / (delta k : ℝ))
    calc
      d / (delta k : ℝ) = reference / (delta k : ℝ) +
          (d / (delta k : ℝ) - reference / (delta k : ℝ)) := by ring
      _ ≤ reference / (delta k : ℝ) + seedError / (delta k : ℝ) :=
        by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
  have hpartBounds (i : Fin (delta k)) :
      -edgeError * d ≤ ((S.parts i).card : ℝ) - d / (delta k : ℝ) ∧
      ((S.parts i).card : ℝ) - d / (delta k : ℝ) ≤ edgeError * d := by
    simpa [d, abs_le] using S.partBalanced i
  have hpartBalanced (i : Fin (delta k)) :
      |((S.parts i).card : ℝ) - reference / (delta k : ℝ)| ≤ error := by
    rw [abs_le]
    constructor
    · have hp := (hpartBounds i).1
      linarith
    · have hp := (hpartBounds i).2
      linarith
  have htypicalLower (i : Fin (delta k)) :
      reference / (delta k : ℝ) - error ≤ ((S.typical i).card : ℝ) := by
    have hs := S.typicalLower i
    dsimp [d] at hseedDivLower htypical hs ⊢
    linarith
  have htypicalUpper (i : Fin (delta k)) :
      ((S.typical i).card : ℝ) ≤ reference / (delta k : ℝ) + error := by
    have hcardNat : (S.typical i).card ≤ (S.parts i).card :=
      Finset.card_le_card (S.typical_subset_part i)
    have hcard : ((S.typical i).card : ℝ) ≤ ((S.parts i).card : ℝ) := by
      exact_mod_cast hcardNat
    have hp := (abs_le.mp (hpartBalanced i)).2
    linarith
  have htypicalBalanced (i : Fin (delta k)) :
      |((S.typical i).card : ℝ) - reference / (delta k : ℝ)| ≤ error := by
    rw [abs_le]
    exact ⟨by linarith [htypicalLower i], by linarith [htypicalUpper i]⟩
  have hpartTypicalLoss (i : Fin (delta k)) :
      (((S.parts i \ S.typical i).card : ℕ) : ℝ) ≤ 2 * error := by
    have hsubset := S.typical_subset_part i
    have hcardNat := Finset.card_sdiff_add_card_eq_card hsubset
    have hcard :
        (((S.parts i \ S.typical i).card : ℕ) : ℝ) +
            ((S.typical i).card : ℝ) = ((S.parts i).card : ℝ) := by
      exact_mod_cast hcardNat
    have hp := (abs_le.mp (hpartBalanced i)).2
    have ht := htypicalLower i
    linarith
  have hthresholdLower (i : Fin (delta k)) :
      reference / (delta k : ℝ) - thresholdLoss ≤
        (((S.parts i).card - 1 - cap : ℕ) : ℝ) := by
    have hcast := cast_sub_one_sub_lower (S.parts i).card cap
    have hp := (hpartBounds i).1
    have htoPart :
        reference / (delta k : ℝ) - thresholdLoss ≤
          ((S.parts i).card : ℝ) - (cap + 1 : ℝ) := by
      change -edgeError * d ≤
        ((S.parts i).card : ℝ) - d / (delta k : ℝ) at hp
      change seedError / (delta k : ℝ) + edgeError * d +
        (cap + 1 : ℝ) ≤ thresholdLoss at hthreshold
      linarith [hseedDivLower]
    exact htoPart.trans (by simpa using hcast)
  have hhighInternal (i : Fin (delta k)) (v : V) (hv : v ∈ S.typical i) :
      reference / (delta k : ℝ) - error ≤
        (C.blueDegreeIn v (S.parts i) : ℝ) := by
    have hblue : (((S.parts i).card - 1 - cap : ℕ) : ℝ) ≤
        (C.blueDegreeIn v (S.parts i) : ℝ) := by
      exact_mod_cast S.highInternalBlue i v hv
    have hbase : reference / (delta k : ℝ) - error ≤
        (((S.parts i).card - 1 - cap : ℕ) : ℝ) := by
      linarith [hthresholdLower i, hthresholdError]
    exact hbase.trans hblue
  have hnonblue (i : Fin (delta k)) (v : V) (hv : v ∈ S.typical i) :
      C.redDegreeIn v (S.parts i) + C.greenDegreeIn v (S.parts i) ≤ cap := by
    have hvpart := S.typical_subset_part i hv
    have hcolors := C.redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_mem hvpart
    have hblue := S.highInternalBlue i v hv
    omega
  have hlowExternal (i : Fin (delta k)) (v : V) (hv : v ∈ S.typical i) :
      (C.blueDegreeIn v (S.parts i)ᶜ : ℝ) ≤ error := by
    have hout := S.lowExternalBlue i v hv
    have hth := hthresholdLower i
    rw [sub_div] at hexternal
    linarith
  have hhighRed (i : Fin (delta k)) (v : V) (hv : v ∈ S.typical i) :
      reference - error ≤ (C.redDegree v : ℝ) := by
    have hr := S.highTotalRed i v hv
    have hth := hthresholdLower i
    have hmul := mul_le_mul_of_nonneg_left hth hdelta.le
    have hlower :
        reference - (delta k : ℝ) * thresholdLoss ≤
          (delta k : ℝ) *
            (((S.parts i).card - 1 - cap : ℕ) : ℝ) := by
      calc
        reference - (delta k : ℝ) * thresholdLoss =
            (delta k : ℝ) *
              (reference / (delta k : ℝ) - thresholdLoss) := by
                field_simp [hdelta.ne']
        _ ≤ (delta k : ℝ) *
              (((S.parts i).card - 1 - cap : ℕ) : ℝ) := hmul
    linarith
  have htotalBlue (i : Fin (delta k)) (v : V) (hv : v ∈ S.typical i) :
      (C.blueDegree v : ℝ) ≤ reference / (delta k : ℝ) + 2 * error := by
    have hsplit := C.degreeIn_add_degreeIn_compl .blue v (S.parts i)
    have hsplitR :
        (C.blueDegreeIn v (S.parts i) : ℝ) +
            (C.blueDegreeIn v (S.parts i)ᶜ : ℝ) =
          (C.blueDegree v : ℝ) := by
      exact_mod_cast hsplit
    have hinNat := degreeIn_le_card C .blue v (S.parts i)
    have hin : (C.blueDegreeIn v (S.parts i) : ℝ) ≤
        ((S.parts i).card : ℝ) := by exact_mod_cast hinNat
    have hp := (abs_le.mp (hpartBalanced i)).2
    linarith [hlowExternal i v hv]
  exact {
    seed := S.seed
    redNeighborhood := S.redNeighborhood
    redNeighborhood_eq := S.redNeighborhood_eq
    parts := S.parts
    parts_pairwiseDisjoint := S.parts_pairwiseDisjoint
    parts_cover := S.parts_cover
    typical := S.typical
    typical_subset_part := S.typical_subset_part
    typical_controlled := S.typical_controlled
    internalNonblueCap := cap
    seedRedNearReference := hseed.trans hseedError
    partBalanced := hpartBalanced
    typicalBalanced := htypicalBalanced
    partTypicalLoss := hpartTypicalLoss
    highInternalBlue := hhighInternal
    lowInternalNonblue := hnonblue
    lowExternalBlue := hlowExternal
    highTotalRed := hhighRed
    totalBlueUpper := htotalBlue
  }

/-- Every uniform seed-stage estimate remains true after enlarging its common
error.  The integral nonblue cap and all underlying finite sets are unchanged. -/
noncomputable def UniformCoreSeedStage.weakenError
    {k : ℕ} {C : ColoredGraph V} {control : Finset V}
    {reference error error' : ℝ}
    (S : UniformCoreSeedStage k C control reference error)
    (herror : error ≤ error') :
    UniformCoreSeedStage k C control reference error' := by
  exact {
    seed := S.seed
    redNeighborhood := S.redNeighborhood
    redNeighborhood_eq := S.redNeighborhood_eq
    parts := S.parts
    parts_pairwiseDisjoint := S.parts_pairwiseDisjoint
    parts_cover := S.parts_cover
    typical := S.typical
    typical_subset_part := S.typical_subset_part
    typical_controlled := S.typical_controlled
    internalNonblueCap := S.internalNonblueCap
    seedRedNearReference := S.seedRedNearReference.trans herror
    partBalanced := fun i ↦ (S.partBalanced i).trans herror
    typicalBalanced := fun i ↦ (S.typicalBalanced i).trans herror
    partTypicalLoss := fun i ↦
      (S.partTypicalLoss i).trans
        (mul_le_mul_of_nonneg_left herror (by norm_num : (0 : ℝ) ≤ 2))
    highInternalBlue := fun i v hv ↦ by
      exact (sub_le_sub_left herror (reference / (delta k : ℝ))).trans
        (S.highInternalBlue i v hv)
    lowInternalNonblue := S.lowInternalNonblue
    lowExternalBlue := fun i v hv ↦ (S.lowExternalBlue i v hv).trans herror
    highTotalRed := fun i v hv ↦ by
      exact (sub_le_sub_left herror reference).trans (S.highTotalRed i v hv)
    totalBlueUpper := fun i v hv ↦ by
      exact (S.totalBlueUpper i v hv).trans
        (add_le_add_right (mul_le_mul_of_nonneg_left herror
          (by norm_num : (0 : ℝ) ≤ 2))
          (reference / (delta k : ℝ)))
  }

end UniformCoreSeedStage

/-- A homogeneous list element for the bounded seed iteration.  The level is
stored with the stage, while the stage retains the sharper error belonging to
that level's *output* index `level.succ`. -/
structure IndexedUniformCoreSeedStage
    {k n : ℕ} {η ζ : ℝ} (P : CoreExtractionParameters k η ζ)
    (C : ColoredGraph (Fin n)) (control : Finset (Fin n))
    (reference : ℝ) where
  level : Fin P.stageBound
  stage : UniformCoreSeedStage k C control reference
    (P.levelError level.succ n)
  /-- A common integral cap retained for terminal overlap bookkeeping. -/
  terminalNonblueCap : stage.internalNonblueCap ≤
    coreSeedNonblueCap (P.betaSeq (Fin.last P.stageBound)) n

namespace IndexedUniformCoreSeedStage

/-- Forget the sharper level error and view an indexed stage with the common
terminal error used after the seed iteration has stopped. -/
noncomputable def terminalStage
    {k n : ℕ} {η ζ : ℝ} {P : CoreExtractionParameters k η ζ}
    {C : ColoredGraph (Fin n)} {control : Finset (Fin n)}
    {reference : ℝ}
    (S : IndexedUniformCoreSeedStage P C control reference) :
    UniformCoreSeedStage k C control reference (P.terminalError n) :=
  S.stage.weakenError (P.levelError_le_terminal S.level.succ n)

end IndexedUniformCoreSeedStage

/-! ### Scalar allocations for one concrete seed stage -/

/-- The fixed master constant dominates every linear loss in `Δ`. -/
theorem CoreExtractionParameters.ten_thousand_mul_delta_add_one_le_master
    {k : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    10000 * ((delta k : ℝ) + 1) ≤ P.master := by
  have hdelta : (delta k : ℝ) + 1 ≤ (k + 1 : ℕ) := by
    unfold delta
    exact_mod_cast (show k - 2 + 1 ≤ k + 1 by omega)
  have hkOne : (1 : ℝ) ≤ (k + 1 : ℕ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hpowThree : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 3 :=
    one_le_pow₀ hkOne
  have hpow : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 4 := by
    calc
      ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hpowThree (Nat.cast_nonneg _)
      _ = ((k + 1 : ℕ) : ℝ) ^ 4 := by ring
  have hbound : (delta k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) ^ 4 := by
    calc
      (delta k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) := by
        simpa [Nat.cast_add] using hdelta
      _ ≤ ((k + 1 : ℕ) : ℝ) ^ 4 := hpow
  rw [P.master_eq, coreExtractionMasterConstant]
  exact mul_le_mul_of_nonneg_left (by simpa [Nat.cast_add] using hbound)
    (by norm_num)

/-- A single explicit ambient threshold that absorbs the constant terms in
the passage from the current hierarchy error to the next one. -/
noncomputable def CoreExtractionParameters.coreSeedScalarThreshold
    {k : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta)
    (q : Fin P.stageBound) : ℕ :=
  ⌈P.master / Real.sqrt (P.betaSeq q.succ)⌉₊

/-- The threshold loss allocated to the integral subtraction
`part.card - 1 - cap`.  Half of the next-level error is divided by `Δ`,
leaving the other half for weighted-degree and external-blue losses. -/
noncomputable def CoreExtractionParameters.coreSeedThresholdLoss
    {k : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta)
    (q : Fin P.stageBound) (n : ℕ) : ℝ :=
  P.levelError q.succ n / (2 * (delta k : ℝ))

/-- The seven scalar inequalities consumed by `CoreSeedStage.toUniform` for
the concrete choices made in the seed recursion. -/
structure CoreSeedStageScalarCertificate
    {k : ℕ} (n : ℕ) {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta)
    (q : Fin P.stageBound) (seedDegree : ℕ) (deleted : ℝ) where
  seedError_le : P.levelError q.castSucc n ≤ P.levelError q.succ n
  partAllocation :
    P.betaSeq q.succ * (seedDegree : ℝ) +
        P.levelError q.castSucc n / (delta k : ℝ) ≤
      P.levelError q.succ n
  typicalAllocation :
    P.levelError q.castSucc n / (delta k : ℝ) +
        P.betaSeq q.succ * (seedDegree : ℝ) + 1 +
          2 * P.betaSeq q.succ * (seedDegree : ℝ) ^ 2 /
            (coreSeedNonblueCap (P.betaSeq q.succ) seedDegree + 1 : ℝ) ≤
      P.levelError q.succ n
  thresholdAllocation :
    P.levelError q.castSucc n / (delta k : ℝ) +
        P.betaSeq q.succ * (seedDegree : ℝ) +
          (coreSeedNonblueCap (P.betaSeq q.succ) seedDegree + 1 : ℝ) ≤
      P.coreSeedThresholdLoss q n
  threshold_le_error :
    P.coreSeedThresholdLoss q n ≤ P.levelError q.succ n
  externalAllocation :
    (deleted + (P.betaSeq 0 * (n : ℝ) + (delta k : ℝ))) /
          (delta k : ℝ) + P.coreSeedThresholdLoss q n ≤
      P.levelError q.succ n
  redAllocation :
    (delta k : ℝ) * P.coreSeedThresholdLoss q n +
        (P.betaSeq 0 * (n : ℝ) + (delta k : ℝ)) ≤
      P.levelError q.succ n

/-- The deleted tail is bounded by the initial fourth-power hierarchy slot. -/
theorem CleanedCoreStart.deleted_le_betaSeq_zero_fourth_mul
    {k n : ℕ} {eta zeta : ℝ} {C : ColoredGraph (Fin n)}
    (P : CoreExtractionParameters k eta zeta)
    (A : CleanedCoreStart k n C eta P.tailScale) :
    ((Finset.univ \ A.retained).card : ℝ) ≤
      (P.betaSeq 0) ^ 4 * (n : ℝ) := by
  calc
    ((Finset.univ \ A.retained).card : ℝ) ≤
        10 * (delta k : ℝ) * P.tailScale ^ (1 / 4 : ℝ) * (n : ℝ) :=
      A.retained_compl_small
    _ ≤ (P.betaSeq 0) ^ 4 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right P.tail_exceptional (Nat.cast_nonneg n)

/-- Every good vertex satisfies the concrete cleaned weighted-degree budget
used by the raw seed-stage constructor. -/
theorem CleanedCoreStart.goodSet_cleaned_weightedDegree_le
    {k n : ℕ} {eta zeta : ℝ} {C : ColoredGraph (Fin n)}
    (P : CoreExtractionParameters k eta zeta)
    (A : CleanedCoreStart k n C eta P.tailScale) {v : Fin n}
    (hv : v ∈ A.goodSet) :
    |(weightedDegree k A.cleaned v : ℝ)| ≤
      P.betaSeq 0 * (n : ℝ) + (delta k : ℝ) := by
  calc
    |(weightedDegree k A.cleaned v : ℝ)| ≤
        12 * (delta k : ℝ) ^ 2 * P.tailScale ^ (1 / 4 : ℝ) *
            (n : ℝ) + (delta k : ℝ) :=
      A.cleaned_goodSet_weightedDegree v hv
    _ ≤ P.betaSeq 0 * (n : ℝ) + (delta k : ℝ) := by
      have hmul :=
        mul_le_mul_of_nonneg_right P.tail_restricted (Nat.cast_nonneg n)
      linarith

/-- A cleaned red neighborhood contains at most one vertex outside the fixed
good set: the maximum-red-degree vertex inserted during cleaning. -/
theorem CleanedCoreStart.redNeighbors_outside_goodSet_card_le_one
    {k n : ℕ} {eta tailScale : ℝ} {C : ColoredGraph (Fin n)}
    (A : CleanedCoreStart k n C eta tailScale) (seed : Fin n) :
    (((Finset.univ :
        Finset {v // v ∈ A.cleaned.redNeighborFinset seed}).filter
          fun v : {w // w ∈ A.cleaned.redNeighborFinset seed} ↦
            (v : Fin n) ∉ A.goodSet).card : ℝ) ≤ 1 := by
  classical
  have hretained (u : {v // v ∈ A.cleaned.redNeighborFinset seed}) :
      (u : Fin n) ∈ A.retained := by
    have hred := (A.cleaned.mem_neighborFinset .red seed u).1 u.property
    have hredOutside :
        (C.greenOutside A.retained).color seed (u : Fin n) = .red := by
      simpa only [A.cleaned_eq] using hred.2
    by_contra hu
    have hgreen := C.greenOutside_color_of_not_both A.retained hred.1
      (by simp [hu])
    rw [hgreen] at hredOutside
    simpa using hredOutside
  have hcard :
      ((Finset.univ :
        Finset {v // v ∈ A.cleaned.redNeighborFinset seed}).filter
          fun v : {w // w ∈ A.cleaned.redNeighborFinset seed} ↦
            (v : Fin n) ∉ A.goodSet).card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro u v hu hv
    have huNot := (Finset.mem_filter.mp hu).2
    have hvNot := (Finset.mem_filter.mp hv).2
    have huRet := hretained u
    have hvRet := hretained v
    rw [A.retained_eq] at huRet hvRet
    have huEq : (u : Fin n) = A.seed := by simpa [huNot] using huRet
    have hvEq : (v : Fin n) = A.seed := by simpa [hvNot] using hvRet
    exact Subtype.ext (huEq.trans hvEq.symm)
  exact_mod_cast hcard

set_option maxHeartbeats 800000 in
-- The nested hierarchy witnesses and exact ceiling estimates exceed the default budget.
/-- The hierarchy and the explicit ceiling cap satisfy all scalar allocations
for a concrete seed.  The sole ambient threshold is
`coreSeedScalarThreshold`; its role is only to absorb the constant slot in
the preceding level error. -/
theorem CoreExtractionParameters.coreSeedStageScalarCertificate
    {k n seedDegree : ℕ} {eta zeta deleted : ℝ}
    (hk : 3 ≤ k) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k eta zeta) (q : Fin P.stageBound)
    (hn : P.coreSeedScalarThreshold q ≤ n)
    (hdegree : seedDegree ≤ n) (hdegreePos : 0 < seedDegree)
    (hdeletedNonneg : 0 ≤ deleted)
    (hdeleted : deleted ≤ (P.betaSeq 0) ^ 4 * (n : ℝ)) :
    CoreSeedStageScalarCertificate n P q seedDegree deleted := by
  let D : ℝ := delta k
  let x : ℝ := Real.sqrt (P.betaSeq q.succ)
  let y : ℝ := Real.sqrt (P.betaSeq q.castSucc)
  let N : ℝ := n
  let d : ℝ := seedDegree
  let K : ℝ := P.master
  let E₀ : ℝ := P.levelError q.castSucc n
  let E₁ : ℝ := P.levelError q.succ n
  let T : ℝ := P.coreSeedThresholdLoss q n
  have hDnat : 0 < delta k := by unfold delta; omega
  have hDcast : (0 : ℝ) < (delta k : ℝ) := by exact_mod_cast hDnat
  have hD : 0 < D := by simpa [D] using hDcast
  have hDoneNat : 1 ≤ delta k := hDnat
  have hDoneCast : (1 : ℝ) ≤ (delta k : ℝ) := by exact_mod_cast hDoneNat
  have hDone : 1 ≤ D := by simpa [D] using hDoneCast
  have hK : 0 < K := P.master_pos
  have hmaster : 10000 * (D + 1) ≤ K := by
    simpa [D, K] using P.ten_thousand_mul_delta_add_one_le_master
  have hKlarge : (10000 : ℝ) ≤ K := by nlinarith
  have hbetaPos : 0 < P.betaSeq q.succ := P.betaSeq_pos q.succ
  have hx : 0 < x := Real.sqrt_pos.2 hbetaPos
  have hxSq : x ^ 2 = P.betaSeq q.succ := by
    exact Real.sq_sqrt hbetaPos.le
  have hbetaLeX : P.betaSeq q.succ ≤ x := by
    simpa [x] using P.betaSeq_le_sqrt q.succ
  have hzeroLeNext : P.betaSeq 0 ≤ P.betaSeq q.succ :=
    P.betaSeq_strictMono.monotone (Fin.zero_le q.succ)
  have hzeroLeX : P.betaSeq 0 ≤ x := hzeroLeNext.trans hbetaLeX
  have hbetaZeroFourth : (P.betaSeq 0) ^ 4 ≤ P.betaSeq 0 := by
    have hb0 := (P.betaSeq_pos 0).le
    have hb1 := (P.betaSeq_lt_one 0).le
    have hsq : (P.betaSeq 0) ^ 2 ≤ P.betaSeq 0 := by
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb1)]
    have hsqOne : (P.betaSeq 0) ^ 2 ≤ 1 := hsq.trans hb1
    have hfourth : ((P.betaSeq 0) ^ 2) ^ 2 ≤ (P.betaSeq 0) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (P.betaSeq 0))
        (sub_nonneg.mpr hsqOne)]
    nlinarith
  have hN : 0 ≤ N := by positivity
  have hd : 0 ≤ d := by positivity
  have hdNCast : (seedDegree : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdegree
  have hdN : d ≤ N := by simpa [d, N] using hdNCast
  have hKN : K ≤ x * N := by
    have hceil : K / x ≤ (P.coreSeedScalarThreshold q : ℕ) := by
      simpa [CoreExtractionParameters.coreSeedScalarThreshold, K, x] using
        (Nat.le_ceil (K / x))
    have hceilNCast : ((P.coreSeedScalarThreshold q : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hceilN : ((P.coreSeedScalarThreshold q : ℕ) : ℝ) ≤ N := by
      simpa [N] using hceilNCast
    have hdiv : K / x ≤ N := hceil.trans hceilN
    have := (div_le_iff₀ hx).mp hdiv
    nlinarith
  have hprev : K * y ≤ x := by
    have hstep := P.master_mul_sqrt_beta_lt_next heta.1 q
    have hetaBeta : eta * P.betaSeq q.succ < P.betaSeq q.succ := by
      nlinarith [mul_pos (sub_pos.mpr heta.2) hbetaPos]
    have hstep' : K * y < eta * P.betaSeq q.succ := by
      simpa [K, y] using hstep
    have : K * y < x := hstep'.trans (hetaBeta.trans_le hbetaLeX)
    exact this.le
  have hE₀Upper : E₀ ≤ x * N / 100 + K := by
    have hmul := mul_le_mul_of_nonneg_right hprev hN
    change P.master / 100 * Real.sqrt (P.betaSeq q.castSucc) * (n : ℝ) +
        P.master ≤ x * N / 100 + K
    dsimp [K, y, N] at hmul ⊢
    nlinarith
  have hE₀Nonneg : 0 ≤ E₀ := (P.levelError_pos q.castSucc n).le
  have hE₁Nonneg : 0 ≤ E₁ := (P.levelError_pos q.succ n).le
  have hE₁Eq : E₁ = K / 100 * x * N + K := by
    simp [E₁, CoreExtractionParameters.levelError, K, x, N]
  have hE₀Div : E₀ / D ≤ E₀ := by
    exact div_le_self hE₀Nonneg hDone
  have hbetaDegree : P.betaSeq q.succ * d ≤ x * N := by
    exact mul_le_mul hbetaLeX hdN hd hx.le
  have hdeletedUpper : deleted ≤ x * N := by
    calc
      deleted ≤ (P.betaSeq 0) ^ 4 * (n : ℝ) := hdeleted
      _ ≤ P.betaSeq 0 * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hbetaZeroFourth (Nat.cast_nonneg n)
      _ ≤ x * N := by
        exact mul_le_mul hzeroLeX (le_rfl) hN hx.le
  have hweightedUpper :
      P.betaSeq 0 * (n : ℝ) + D ≤ x * N + D := by
    have := mul_le_mul_of_nonneg_right hzeroLeX hN
    simpa [N] using add_le_add_right this D
  have hcap := coreSeedNonblueCap_lt_add_one
    (P.betaSeq_pos q.succ).le seedDegree
  have hcapUpper :
      (coreSeedNonblueCap (P.betaSeq q.succ) seedDegree + 1 : ℝ) <
        x * N + 2 := by
    have hdMul := mul_le_mul_of_nonneg_left hdN hx.le
    have hadd : x * d + 1 ≤ x * N + 1 := by linarith
    have hcap' :
        (coreSeedNonblueCap (P.betaSeq q.succ) seedDegree : ℝ) <
          x * N + 1 := by
      simpa [x, d, N] using hcap.trans_le hadd
    norm_num [Nat.cast_add]
    nlinarith
  have hmarkov := coreSeed_markovQuotient_le
    (P.betaSeq_pos q.succ) hdegreePos
  have hmarkovUpper :
      2 * P.betaSeq q.succ * d ^ 2 /
          (coreSeedNonblueCap (P.betaSeq q.succ) seedDegree + 1 : ℝ) ≤
        2 * x * N := by
    have hmarkov' :
        2 * P.betaSeq q.succ * d ^ 2 /
            (coreSeedNonblueCap (P.betaSeq q.succ) seedDegree + 1 : ℝ) ≤
          2 * x * d := by simpa [x, d] using hmarkov
    have hmul : 2 * x * d ≤ 2 * x * N := by
      have hxmul := mul_le_mul_of_nonneg_left hdN hx.le
      nlinarith
    exact hmarkov'.trans hmul
  have hTNonneg : 0 ≤ T := by
    unfold T CoreExtractionParameters.coreSeedThresholdLoss
    positivity
  have hTEq : 2 * D * T = E₁ := by
    unfold T CoreExtractionParameters.coreSeedThresholdLoss E₁ D
    field_simp [hD.ne']
  have hTHalf : T ≤ E₁ / 2 := by
    have hmul : 0 ≤ (D - 1) * T := mul_nonneg (sub_nonneg.mpr hDone) hTNonneg
    nlinarith
  have hDZ : 10000 * D * (x * N) ≤ K * (x * N) := by
    have h := mul_le_mul_of_nonneg_right
      (show 10000 * D ≤ K by nlinarith [hmaster])
      (mul_nonneg hx.le hN)
    nlinarith
  have hDK : 10000 * D * K ≤ K * K := by
    have h := mul_le_mul_of_nonneg_right
      (show 10000 * D ≤ K by nlinarith [hmaster]) hK.le
    nlinarith
  have hKK : K * K ≤ K * (x * N) :=
    mul_le_mul_of_nonneg_left hKN hK.le
  have hlargeBudget : 100 * (x * N) + K ≤ E₁ := by
    rw [hE₁Eq]
    have hcoef : (100 : ℝ) ≤ K / 100 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hx.le hN)
    nlinarith
  refine ⟨P.levelError_mono (Fin.castSucc_le_succ q) n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [D, d, E₀, E₁] at hE₀Div hbetaDegree hlargeBudget ⊢
    linarith
  · dsimp [D, d, E₀, E₁] at hE₀Div hbetaDegree hmarkovUpper hlargeBudget ⊢
    linarith
  · change E₀ / D + P.betaSeq q.succ * d +
        (coreSeedNonblueCap (P.betaSeq q.succ) seedDegree + 1 : ℝ) ≤
      E₁ / (2 * D)
    rw [le_div_iff₀ (mul_pos (by norm_num) hD)]
    have hlhs : E₀ / D + P.betaSeq q.succ * d +
        (coreSeedNonblueCap (P.betaSeq q.succ) seedDegree + 1 : ℝ) ≤
          E₀ + x * N + (x * N + 2) := by
      linarith
    have hscaled :
        (E₀ + x * N + (x * N + 2)) * (2 * D) ≤ E₁ := by
      rw [hE₁Eq]
      nlinarith [hE₀Upper, hDZ, hDK, hKK]
    simpa [D, d, E₀, E₁] using
      (mul_le_mul_of_nonneg_right hlhs (mul_nonneg (by norm_num) hD.le) |>.trans hscaled)
  · dsimp [CoreExtractionParameters.coreSeedThresholdLoss, E₁, D]
      at hTNonneg hTEq hTHalf ⊢
    exact hTHalf.trans (by linarith [hE₁Nonneg])
  · have hnumeratorNonneg :
        0 ≤ deleted + (P.betaSeq 0 * (n : ℝ) + D) := by
      exact add_nonneg hdeletedNonneg
        (add_nonneg
          (mul_nonneg (P.betaSeq_pos 0).le (Nat.cast_nonneg n)) hD.le)
    have hdiv :
        (deleted + (P.betaSeq 0 * (n : ℝ) + D)) / D ≤
          deleted + (P.betaSeq 0 * (n : ℝ) + D) :=
      div_le_self hnumeratorNonneg hDone
    rw [show P.coreSeedThresholdLoss q n = T by rfl]
    dsimp [D, E₁] at hdiv hdeletedUpper hweightedUpper hTHalf hlargeBudget ⊢
    linarith
  · rw [show P.coreSeedThresholdLoss q n = T by rfl]
    have hDTEq : D * T = E₁ / 2 := by nlinarith [hTEq]
    rw [hDTEq]
    dsimp [D, E₁] at hweightedUpper hlargeBudget ⊢
    linarith

/-- Convert one eligible seed and one near-Turán certificate into an indexed
uniform seed stage.  This is the finite F2 bookkeeping step, separated from
the local-Turán argument so that the direct `k = 3` branch can reuse it.

The common reference is the *original* maximum red degree.  Consequently the
global cleaned upper bound and the supplied lower bound give the exact
current-level seed error. -/
theorem exists_indexedUniformCoreSeedStage_of_nearTuran
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta)
    (q : Fin P.stageBound) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n),
      ∀ A : CleanedCoreStart k n C eta P.tailScale, ∀ seed : Fin n,
        (C.redDegree A.seed : ℝ) - P.levelError q.castSucc n ≤
            (A.cleaned.redDegree seed : ℝ) →
        (eta / 4) * (n : ℝ) ≤ (A.cleaned.redDegree seed : ℝ) →
        (SimpleGraph.turanNumber (A.cleaned.redDegree seed) (delta k) : ℝ) -
              coreExtractionESModulus k (P.betaSeq q.succ) *
                (A.cleaned.redDegree seed : ℝ) ^ 2 ≤
            ((redGreenNeighborhoodGraph A.cleaned seed).edgeFinset.card : ℝ) →
        ∃ S : IndexedUniformCoreSeedStage P A.cleaned A.goodSet
            (C.redDegree A.seed : ℝ),
          S.level = q ∧ S.stage.seed = seed := by
  classical
  obtain ⟨nSeed, hstage⟩ :=
    exists_coreSeedStage_of_nearTuran k hk (P.betaSeq q.succ)
      (P.betaSeq_pos q.succ)
  let nES : ℕ := ⌈(4 * (nSeed : ℝ)) / eta⌉₊
  let n₀ := max (P.coreSeedScalarThreshold q) nES
  refine ⟨n₀, ?_⟩
  intro n hn C A seed hseedLower hseedLarge hnear
  have hnScalar : P.coreSeedScalarThreshold q ≤ n :=
    (le_max_left _ _).trans hn
  have hnES : nES ≤ n := (le_max_right _ _).trans hn
  have hsqrtPos : 0 < Real.sqrt (P.betaSeq q.succ) :=
    Real.sqrt_pos.2 (P.betaSeq_pos q.succ)
  have hnScalarPos : 0 < P.coreSeedScalarThreshold q := by
    unfold CoreExtractionParameters.coreSeedScalarThreshold
    exact Nat.ceil_pos.mpr (div_pos P.master_pos hsqrtPos)
  have hnPos : 0 < n := hnScalarPos.trans_le hnScalar
  have hseedDegreePos : 0 < A.cleaned.redDegree seed := by
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
    have hpositive : 0 < (eta / 4) * (n : ℝ) :=
      mul_pos (div_pos heta.1 (by norm_num)) hnReal
    have : (0 : ℝ) < (A.cleaned.redDegree seed : ℝ) :=
      hpositive.trans_le hseedLarge
    exact_mod_cast this
  have hseedDegreeLe : A.cleaned.redDegree seed ≤ n := by
    change (A.cleaned.redNeighborFinset seed).card ≤ n
    calc
      (A.cleaned.redNeighborFinset seed).card ≤
          (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hnSeedReal : (nSeed : ℝ) ≤ (A.cleaned.redDegree seed : ℝ) := by
    have hceil : (4 * (nSeed : ℝ)) / eta ≤ (nES : ℕ) := by
      dsimp [nES]
      exact Nat.le_ceil _
    have hnESReal : (nES : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnES
    have hratio := hceil.trans hnESReal
    have hmul := (div_le_iff₀ heta.1).mp hratio
    nlinarith
  have hnSeedNat : nSeed ≤ A.cleaned.redDegree seed := by exact_mod_cast hnSeedReal
  let deleted : ℝ := (Finset.univ \ A.retained).card
  have hdeletedNonneg : 0 ≤ deleted := by positivity
  have hdeleted : deleted ≤ (P.betaSeq 0) ^ 4 * (n : ℝ) := by
    simpa [deleted] using A.deleted_le_betaSeq_zero_fourth_mul P
  have hcontrol := A.redNeighbors_outside_goodSet_card_le_one seed
  have hred : ∀ v ∈ A.goodSet,
      (A.cleaned.redDegree v : ℝ) ≤
        (C.redDegree A.seed : ℝ) + deleted := by
    intro v hv
    have hleNat := A.cleaned_red_le_seed_original v
    have hle : (A.cleaned.redDegree v : ℝ) ≤
        (C.redDegree A.seed : ℝ) := by exact_mod_cast hleNat
    linarith
  have hweighted : ∀ v ∈ A.goodSet,
      |(weightedDegree k A.cleaned v : ℝ)| ≤
        P.betaSeq 0 * (n : ℝ) + (delta k : ℝ) := by
    intro v hv
    exact A.goodSet_cleaned_weightedDegree_le P hv
  obtain ⟨raw, hrawSeed⟩ := hstage A.cleaned A.cleaned_mem_Ck seed hnSeedNat hnear
    A.goodSet (coreSeedNonblueCap (P.betaSeq q.succ) (A.cleaned.redDegree seed))
    (C.redDegree A.seed : ℝ) deleted
    (P.betaSeq 0 * (n : ℝ) + (delta k : ℝ)) 1
    hcontrol hred hweighted
  have hseedUpper : (A.cleaned.redDegree seed : ℝ) ≤
      (C.redDegree A.seed : ℝ) := by
    exact_mod_cast A.cleaned_red_le_seed_original seed
  have hseed :
      |(A.cleaned.redDegree seed : ℝ) - (C.redDegree A.seed : ℝ)| ≤
        P.levelError q.castSucc n := by
    rw [abs_le]
    constructor <;> linarith
  have hseedRaw :
      |(A.cleaned.redDegree raw.seed : ℝ) - (C.redDegree A.seed : ℝ)| ≤
        P.levelError q.castSucc n := by
    simpa [hrawSeed] using hseed
  have B := P.coreSeedStageScalarCertificate hk heta q hnScalar
    hseedDegreeLe hseedDegreePos hdeletedNonneg hdeleted
  let uniform := raw.toUniform hk (C.redDegree A.seed : ℝ)
    (P.levelError q.succ n) (P.levelError q.castSucc n)
    (P.coreSeedThresholdLoss q n) hseedRaw B.seedError_le
    (by simpa only [hrawSeed] using B.partAllocation)
    (by simpa only [hrawSeed] using B.typicalAllocation)
    (by simpa only [hrawSeed] using B.thresholdAllocation)
    B.threshold_le_error
    (by
      convert B.externalAllocation using 1 <;> ring)
    B.redAllocation
  let indexed : IndexedUniformCoreSeedStage P A.cleaned A.goodSet
      (C.redDegree A.seed : ℝ) := {
    level := q
    stage := uniform
    terminalNonblueCap := by
      change coreSeedNonblueCap (P.betaSeq q.succ)
          (A.cleaned.redDegree seed) ≤
        coreSeedNonblueCap (P.betaSeq (Fin.last P.stageBound)) n
      unfold coreSeedNonblueCap
      apply Nat.ceil_mono
      have hbeta : P.betaSeq q.succ ≤
          P.betaSeq (Fin.last P.stageBound) :=
        P.betaSeq_strictMono.monotone (Fin.le_last q.succ)
      have hsqrt : Real.sqrt (P.betaSeq q.succ) ≤
          Real.sqrt (P.betaSeq (Fin.last P.stageBound)) :=
        Real.sqrt_le_sqrt hbeta
      have hdegree : (A.cleaned.redDegree seed : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hseedDegreeLe
      exact mul_le_mul hsqrt hdegree (Nat.cast_nonneg _)
        (Real.sqrt_nonneg _)
  }
  refine ⟨indexed, rfl, ?_⟩
  change raw.seed = seed
  exact hrawSeed

/-- Construct the indexed uniform stage attached to one eligible hierarchy
level.  For `k ≥ 4` the near-Turán input is supplied by the quantitative
local-Turán bridge.  When `k = 3`, `delta k = 1`, so the required Turán
number is zero and the same partition constructor applies directly. -/
theorem exists_indexedUniformCoreSeedStage_atLevel
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta)
    (q : Fin P.stageBound) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n),
      ∀ A : CleanedCoreStart k n C eta P.tailScale, ∀ seed : Fin n,
        (C.redDegree A.seed : ℝ) - P.levelError q.castSucc n ≤
            (A.cleaned.redDegree seed : ℝ) →
        (eta / 4) * (n : ℝ) ≤ (A.cleaned.redDegree seed : ℝ) →
        ∃ S : IndexedUniformCoreSeedStage P A.cleaned A.goodSet
            (C.redDegree A.seed : ℝ),
          S.level = q ∧ S.stage.seed = seed := by
  classical
  obtain ⟨nStage, hstage⟩ :=
    exists_indexedUniformCoreSeedStage_of_nearTuran k hk eta heta P q
  by_cases hk4 : 4 ≤ k
  · obtain ⟨nLocal, hlocal⟩ :=
      exists_localTuranBridge_atLevel k hk4 eta heta P q
    refine ⟨max nStage nLocal, ?_⟩
    intro n hn C A seed hseedLower hseedLarge
    have hnStage : nStage ≤ n := (le_max_left _ _).trans hn
    have hnLocal : nLocal ≤ n := (le_max_right _ _).trans hn
    have hnearMax : ∀ v : Fin n,
        (A.cleaned.redDegree v : ℝ) ≤
          (A.cleaned.redDegree seed : ℝ) +
            P.levelError q.castSucc n := by
      intro v
      have hvOriginal : (A.cleaned.redDegree v : ℝ) ≤
          (C.redDegree A.seed : ℝ) := by
        exact_mod_cast A.cleaned_red_le_seed_original v
      linarith
    exact hstage n hnStage C A seed hseedLower hseedLarge
      (hlocal n hnLocal C A seed hnearMax hseedLarge)
  · have hdelta : delta k = 1 := by
      unfold delta
      omega
    refine ⟨nStage, ?_⟩
    intro n hn C A seed hseedLower hseedLarge
    apply hstage n hn C A seed hseedLower hseedLarge
    have hturan :
        SimpleGraph.turanNumber (A.cleaned.redDegree seed) (delta k) = 0 := by
      rw [hdelta]
      rw [SimpleGraph.turanNumber_eq, Nat.mod_one]
      norm_num [Nat.choose]
    have hmodulus :
        0 < coreExtractionESModulus k (P.betaSeq q.succ) :=
      coreExtractionESModulus_pos hk (P.betaSeq_pos q.succ)
    have hedge :
        0 ≤ ((redGreenNeighborhoodGraph A.cleaned seed).edgeFinset.card : ℝ) :=
      Nat.cast_nonneg _
    calc
      (SimpleGraph.turanNumber (A.cleaned.redDegree seed) (delta k) : ℝ) -
            coreExtractionESModulus k (P.betaSeq q.succ) *
              (A.cleaned.redDegree seed : ℝ) ^ 2 =
          -(coreExtractionESModulus k (P.betaSeq q.succ) *
              (A.cleaned.redDegree seed : ℝ) ^ 2) := by
            rw [hturan]
            norm_num
      _ ≤ 0 := neg_nonpos.mpr
        (mul_nonneg hmodulus.le
          (sq_nonneg (A.cleaned.redDegree seed : ℝ)))
      _ ≤ ((redGreenNeighborhoodGraph A.cleaned seed).edgeFinset.card : ℝ) :=
        hedge

/-- A single ambient threshold works simultaneously for every hierarchy
level, since the level type is finite.  This is the realization interface
used by the bounded seed recursion. -/
theorem exists_uniformIndexedCoreSeedStage_atLevel
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    ∃ n₀ : ℕ, ∀ q : Fin P.stageBound, ∀ n ≥ n₀,
      ∀ C : ColoredGraph (Fin n),
      ∀ A : CleanedCoreStart k n C eta P.tailScale, ∀ seed : Fin n,
        (C.redDegree A.seed : ℝ) - P.levelError q.castSucc n ≤
            (A.cleaned.redDegree seed : ℝ) →
        (eta / 4) * (n : ℝ) ≤ (A.cleaned.redDegree seed : ℝ) →
        ∃ S : IndexedUniformCoreSeedStage P A.cleaned A.goodSet
            (C.redDegree A.seed : ℝ),
          S.level = q ∧ S.stage.seed = seed := by
  classical
  choose levelThreshold hlevel using
    (fun q : Fin P.stageBound ↦
      exists_indexedUniformCoreSeedStage_atLevel k hk eta heta P q)
  let n₀ : ℕ := Finset.univ.sup levelThreshold
  refine ⟨n₀, ?_⟩
  intro q n hn C A seed hseedLower hseedLarge
  have hq : levelThreshold q ≤ n₀ := by
    exact Finset.le_sup (f := levelThreshold) (Finset.mem_univ q)
  exact hlevel q n (hq.trans hn) C A seed hseedLower hseedLarge

/-- Every hierarchy beta lies below its own fourth-power envelope in the
direction needed for the initial deleted-vertex budget. -/
theorem CoreExtractionParameters.betaSeq_fourth_le_self
    {k : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta)
    (q : Fin (P.stageBound + 1)) :
    (P.betaSeq q) ^ 4 ≤ P.betaSeq q := by
  have hbetaNonneg := (P.betaSeq_pos q).le
  have hbetaOne := (P.betaSeq_lt_one q).le
  have hsquare : (P.betaSeq q) ^ 2 ≤ P.betaSeq q := by
    nlinarith [mul_nonneg hbetaNonneg (sub_nonneg.mpr hbetaOne)]
  have hsquareOne : (P.betaSeq q) ^ 2 ≤ 1 := hsquare.trans hbetaOne
  have hfourthSquare : ((P.betaSeq q) ^ 2) ^ 2 ≤
      (P.betaSeq q) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (P.betaSeq q))
      (sub_nonneg.mpr hsquareOne)]
  nlinarith

/-- The one-time deleted set is already covered by the level-zero error.
This is the scalar input needed to use the cleaned maximum-red vertex as
the first seed. -/
theorem CleanedCoreStart.deleted_le_levelError_zero
    {k n : ℕ} (hk : 3 ≤ k) {eta zeta : ℝ}
    {C : ColoredGraph (Fin n)}
    (P : CoreExtractionParameters k eta zeta)
    (A : CleanedCoreStart k n C eta P.tailScale) :
    ((Finset.univ \ A.retained).card : ℝ) ≤
      P.levelError (0 : Fin (P.stageBound + 1)) n := by
  have hdeleted := A.deleted_le_betaSeq_zero_fourth_mul P
  have hfourth := P.betaSeq_fourth_le_self
    (0 : Fin (P.stageBound + 1))
  have hbetaSqrt := P.betaSeq_le_sqrt
    (0 : Fin (P.stageBound + 1))
  have hmaster : (100 : ℝ) ≤ P.master := by
    linarith [P.one_ninety_two_le_master]
  have hcoefficient : (1 : ℝ) ≤ P.master / 100 := by
    linarith
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsqrtN : 0 ≤ Real.sqrt (P.betaSeq 0) * (n : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) hn
  calc
    ((Finset.univ \ A.retained).card : ℝ) ≤
        (P.betaSeq 0) ^ 4 * (n : ℝ) := hdeleted
    _ ≤ P.betaSeq 0 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hfourth hn
    _ ≤ Real.sqrt (P.betaSeq 0) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hbetaSqrt hn
    _ ≤ (P.master / 100) * Real.sqrt (P.betaSeq 0) * (n : ℝ) := by
      nlinarith
    _ ≤ P.levelError (0 : Fin (P.stageBound + 1)) n := by
      unfold CoreExtractionParameters.levelError
      linarith [P.master_pos]

/-- The cleaned maximum-red vertex keeps much more than the quarter-density
needed by the seed partition theorem. -/
theorem CleanedCoreStart.cleaned_seed_red_ge_eta_quarter
    {k n : ℕ} (hk : 3 ≤ k) {eta zeta : ℝ}
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) {C : ColoredGraph (Fin n)}
    (P : CoreExtractionParameters k eta zeta)
    (A : CleanedCoreStart k n C eta P.tailScale) :
    (eta / 4) * (n : ℝ) ≤ (A.cleaned.redDegree A.seed : ℝ) := by
  have hdeleted := A.deleted_le_betaSeq_zero_fourth_mul P
  have hfourth := P.betaSeq_fourth_le_self
    (0 : Fin (P.stageBound + 1))
  have hmasterOne : (1 : ℝ) ≤ P.master := by
    linarith [P.one_ninety_two_le_master]
  have htauMaster : P.tau ≤ P.master * P.tau := by
    nlinarith [P.tau_pos]
  have hbetaEta : (P.betaSeq 0) ^ 4 ≤ eta / 100 := by
    calc
      (P.betaSeq 0) ^ 4 ≤ P.betaSeq 0 := hfourth
      _ ≤ P.tau := (P.betaSeq_lt_tau 0).le
      _ ≤ P.master * P.tau := htauMaster
      _ ≤ eta / 100 := P.tau_lt_eta.le
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdeletedEta :
      ((Finset.univ \ A.retained).card : ℝ) ≤
        (eta / 100) * (n : ℝ) :=
    hdeleted.trans (mul_le_mul_of_nonneg_right hbetaEta hn)
  have hetaN : 0 ≤ eta * (n : ℝ) :=
    mul_nonneg heta.1.le hn
  linarith [A.cleaned_seed_red_lower]

/-- Initial indexed stage, realized by the original maximum-red vertex that
was explicitly retained during cleaning.  The seed equation in the witness
is inherited definitionally from the raw stage constructor. -/
theorem exists_initialIndexedUniformCoreSeedStage
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n),
      ∀ A : CleanedCoreStart k n C eta P.tailScale,
        ∃ S : IndexedUniformCoreSeedStage P A.cleaned A.goodSet
            (C.redDegree A.seed : ℝ),
          S.level = (⟨0, P.stageBound_pos⟩ : Fin P.stageBound) ∧
            S.stage.seed = A.seed := by
  classical
  let q₀ : Fin P.stageBound := ⟨0, P.stageBound_pos⟩
  obtain ⟨n₀, hstage⟩ :=
    exists_indexedUniformCoreSeedStage_atLevel k hk eta heta P q₀
  refine ⟨n₀, ?_⟩
  intro n hn C A
  let deleted : ℝ := (Finset.univ \ A.retained).card
  have hdeletedError : deleted ≤ P.levelError q₀.castSucc n := by
    simpa [deleted, q₀] using A.deleted_le_levelError_zero hk P
  have hseedLoss : (C.redDegree A.seed : ℝ) ≤
      (A.cleaned.redDegree A.seed : ℝ) + deleted := by
    change (C.redDegree A.seed : ℝ) ≤
      (A.cleaned.redDegree A.seed : ℝ) +
        (((Finset.univ \ A.retained).card : ℕ) : ℝ)
    exact_mod_cast A.seed_red_loss
  have hseedLower :
      (C.redDegree A.seed : ℝ) - P.levelError q₀.castSucc n ≤
        (A.cleaned.redDegree A.seed : ℝ) := by
    linarith
  obtain ⟨S, hlevel, hseed⟩ := hstage n hn C A A.seed hseedLower
    (A.cleaned_seed_red_ge_eta_quarter hk heta P)
  exact ⟨S, by simpa [q₀] using hlevel, hseed⟩

/-! ## Integer gaps from two scaled approximations -/

/-- If one real quantity approximates two natural-number multiples of the
same positive scale, and the sum of the two errors is smaller than one unit
of that scale, then the natural numbers are equal.  This packages the
triangle-inequality and factoring steps in the reduced-degree argument. -/
theorem nat_eq_of_two_scaled_approximations
    {degreeNat targetNat : ℕ}
    {quantity scale coreError degreeError : ℝ}
    (hscale : 0 < scale)
    (hcore :
      |quantity - (targetNat : ℝ) * scale| ≤ coreError)
    (hdegree :
      |quantity - (degreeNat : ℝ) * scale| ≤ degreeError)
    (herror : coreError + degreeError < scale) :
    degreeNat = targetNat := by
  have habsScale : |scale| = scale := abs_of_pos hscale
  have hscaled :
      scale * |(degreeNat : ℝ) - (targetNat : ℝ)| ≤
        degreeError + coreError := by
    calc
      scale * |(degreeNat : ℝ) - (targetNat : ℝ)| =
          |scale| * |(degreeNat : ℝ) - (targetNat : ℝ)| := by
            rw [habsScale]
      _ = |scale * ((degreeNat : ℝ) - (targetNat : ℝ))| := by
            rw [abs_mul]
      _ = |(degreeNat : ℝ) * scale - (targetNat : ℝ) * scale| := by
            congr 1
            ring
      _ =
          |(-(quantity - (degreeNat : ℝ) * scale)) +
            (quantity - (targetNat : ℝ) * scale)| := by
            congr 1
            ring
      _ ≤ |-(quantity - (degreeNat : ℝ) * scale)| +
            |quantity - (targetNat : ℝ) * scale| :=
          abs_add_le _ _
      _ = |quantity - (degreeNat : ℝ) * scale| +
            |quantity - (targetNat : ℝ) * scale| := by
          rw [abs_neg]
      _ ≤ degreeError + coreError := add_le_add hdegree hcore
  exact nat_eq_of_scaled_abs_cast_sub_lt hscale hscaled
    (by simpa only [add_comm] using herror)

/-- The reduced-degree specialization of
`nat_eq_of_two_scaled_approximations`.  Here one unit of scale is exactly
`m² / Δ²`, with `Δ = k - 2`; positivity of both integer parameters is
kept explicit for downstream use. -/
theorem reducedDegree_eq_delta_of_two_approximations
    {k m degreeNat : ℕ} {quantity coreError degreeError : ℝ}
    (hdelta : 0 < delta k) (hm : 0 < m)
    (hcore :
      |quantity - (delta k : ℝ) *
          ((m : ℝ) ^ 2 / (delta k : ℝ) ^ 2)| ≤ coreError)
    (hdegree :
      |quantity - (degreeNat : ℝ) *
          ((m : ℝ) ^ 2 / (delta k : ℝ) ^ 2)| ≤ degreeError)
    (herror :
      coreError + degreeError <
        (m : ℝ) ^ 2 / (delta k : ℝ) ^ 2) :
    degreeNat = delta k := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hdeltaReal : 0 < (delta k : ℝ) := by exact_mod_cast hdelta
  have hscale :
      0 < (m : ℝ) ^ 2 / (delta k : ℝ) ^ 2 := by
    exact div_pos (sq_pos_of_pos hmReal) (sq_pos_of_pos hdeltaReal)
  exact nat_eq_of_two_scaled_approximations hscale hcore hdegree herror

/-! ### Stage F8: exact reduced regularity from geometric estimates -/

section ReducedDegreeBridgeConclusion

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

/-- Quantitative Stage F8 bridge.  The hypotheses are the explicit finite
estimates produced by the preceding construction: balanced cluster sizes,
pointwise weighted-degree control, internal and external blue-degree control,
an internal red-edge error, and the red/green reduced-pair dichotomy.

The first parenthesized expression in `herror` is the error in approximating
the intercluster red mass by `Δ · m²/Δ²`; the second is the error in
approximating it by `degree_R(i) · m²/Δ²`.  Requiring their sum to be less
than one unit of that scale gives the exact integer identity. -/
theorem reducedDegree_eq_delta_of_cluster_estimates
    {k m : ℕ} (hdelta : 0 < delta k) (hm : 0 < m)
    (C : ColoredGraph V) (clusters : I → Finset V)
    (R : SimpleGraph I) [DecidableRel R.Adj] (i : I)
    (sizeError weightedError ownBlueError outsideBlueError
      internalRedError densityError : ℝ)
    (hsizeError : 0 ≤ sizeError)
    (hweightedError : 0 ≤ weightedError)
    (hownBlueError : 0 ≤ ownBlueError)
    (houtsideBlueError : 0 ≤ outsideBlueError)
    (hinternalRedError : 0 ≤ internalRedError)
    (hdensityError : 0 ≤ densityError)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hnonempty : ∀ a, (clusters a).Nonempty)
    (hsize : ∀ a,
      |((clusters a).card : ℝ) - (m : ℝ) / (delta k : ℝ)| ≤
        sizeError)
    (hweighted : ∀ v ∈ clusters i,
      |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
        weightedError)
    (hownBlue : ∀ v ∈ clusters i,
      ((clusters i).card : ℝ) - ownBlueError ≤
        (C.blueDegreeIn v (clusters i) : ℝ))
    (houtsideBlue : ∀ v ∈ clusters i,
      (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
        outsideBlueError)
    (hinternalRed :
      (C.redEdgeCountIn (clusters i) : ℝ) ≤ internalRedError)
    (hredEdge : ∀ {a b}, R.Adj a b →
      1 - densityError ≤
        C.colorDensity .red (clusters a) (clusters b))
    (hredNonedge : ∀ {a b}, a ≠ b → ¬ R.Adj a b →
      C.colorDensity .red (clusters a) (clusters b) ≤ densityError)
    (herror :
      (((clusters i).card : ℝ) * weightedError +
          (delta k : ℝ) *
            (((clusters i).card : ℝ) *
                (ownBlueError + outsideBlueError + sizeError) +
              ((m : ℝ) / (delta k : ℝ)) * sizeError) +
          2 * internalRedError) +
        (Fintype.card I : ℝ) *
          (2 * ((m : ℝ) / (delta k : ℝ) + sizeError) * sizeError +
            densityError *
              ((m : ℝ) / (delta k : ℝ) + sizeError) ^ 2) <
        (m : ℝ) ^ 2 / (delta k : ℝ) ^ 2) :
    R.degree i = delta k := by
  let reference : ℝ := (m : ℝ) / (delta k : ℝ)
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hdeltaReal : 0 < (delta k : ℝ) := by exact_mod_cast hdelta
  have href : 0 ≤ reference :=
    (div_pos hmReal hdeltaReal).le
  have hblue : ∀ v ∈ clusters i,
      |(C.blueDegreeIn v (clusterUnion clusters) : ℝ) - reference| ≤
        ownBlueError + outsideBlueError + sizeError := by
    intro v hv
    exact blueDegreeIn_clusterUnion_close_reference
      C clusters i v reference ownBlueError outsideBlueError sizeError
      hownBlueError houtsideBlueError hsizeError
      (by simpa only [reference] using hsize i)
      (hownBlue v hv) (houtsideBlue v hv)
  have hcore := interclusterRedCount_close_delta_mul_reference_sq
    k C clusters hdisj i reference weightedError
      (ownBlueError + outsideBlueError + sizeError)
      sizeError internalRedError href hweightedError
      (add_nonneg (add_nonneg hownBlueError houtsideBlueError) hsizeError)
      hsizeError hinternalRedError
      (by simpa only [reference] using hsize i)
      hweighted hblue hinternalRed
  have hdegree :=
    interclusterRedCount_close_reducedDegreeScale_of_density
      C clusters R i reference sizeError densityError
      href hsizeError hdensityError hnonempty
      (by simpa only [reference] using hsize) hredEdge hredNonedge
  have hreferenceSq :
      reference ^ 2 = (m : ℝ) ^ 2 / (delta k : ℝ) ^ 2 := by
    dsimp [reference]
    ring
  rw [hreferenceSq] at hcore hdegree
  apply reducedDegree_eq_delta_of_two_approximations hdelta hm hcore hdegree
  simpa only [reference] using herror

end ReducedDegreeBridgeConclusion

/-! ### Stages F6--F8 as one transparent adapter -/

/-- The final cluster-family data consumed jointly by Goal 2c and the exact
reduced-degree bridge.

The first eight fields repeat `CoreExtractionMixedMassCertificate` verbatim.
The remaining fields expose the reference degree and every scalar estimate
used by `reducedDegree_eq_delta_of_cluster_estimates`.  In particular,
`scalarGap` is the sole integer-gap hypothesis: no asymptotic or big-O
estimate is hidden in the adapter. -/
structure CoreExtractionFinalClusterCertificate
    (n₀ k n t : ℕ) (C : ColoredGraph (Fin n)) (eta beta : ℝ)
    (clusters : Fin t → Finset (Fin n)) where
  /-- Goal 2c hypothesis (1). -/
  ambientLarge : n₀ ≤ n
  /-- Goal 2c hypothesis (2). -/
  coloring_mem_Ck : C ∈ Ck k n
  /-- Goal 2c hypothesis (3). -/
  clusterCount_ge : k - 1 ≤ t
  /-- Goal 2c hypothesis (4). -/
  clusters_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin t)) clusters
  /-- Goal 2c hypothesis (5). -/
  clusterLowerBound : ∀ i,
    eta * (n : ℝ) ≤ ((clusters i).card : ℝ)
  /-- Goal 2c hypothesis (6). -/
  clusterBalanced : ∀ i j,
    |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| ≤
      beta * (n : ℝ)
  /-- Goal 2c hypothesis (7). -/
  blueSparseBetween : ∀ i j, i ≠ j →
    C.colorDensity .blue (clusters i) (clusters j) ≤ beta
  /-- Goal 2c hypothesis (8). -/
  vertexControls : ∀ i v, v ∈ clusters i →
    (1 - beta) * ((clusters i).card : ℝ) ≤
        (C.blueDegreeIn v (clusters i) : ℝ) ∧
    (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
        beta * (n : ℝ) ∧
    |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
        beta * (n : ℝ)
  /-- The seed red degree `m` giving the common reference size `m / Δ`. -/
  referenceDegree : ℕ
  referenceDegree_pos : 0 < referenceDegree
  sizeError : ℝ
  weightedError : ℝ
  ownBlueError : ℝ
  outsideBlueError : ℝ
  internalRedError : ℝ
  sizeError_nonneg : 0 ≤ sizeError
  weightedError_nonneg : 0 ≤ weightedError
  ownBlueError_nonneg : 0 ≤ ownBlueError
  outsideBlueError_nonneg : 0 ≤ outsideBlueError
  internalRedError_nonneg : 0 ≤ internalRedError
  sizeAroundReference : ∀ i,
    |((clusters i).card : ℝ) -
        (referenceDegree : ℝ) / (delta k : ℝ)| ≤ sizeError
  weightedEstimate : ∀ i v, v ∈ clusters i →
    |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
      weightedError
  ownBlueEstimate : ∀ i v, v ∈ clusters i →
    ((clusters i).card : ℝ) - ownBlueError ≤
      (C.blueDegreeIn v (clusters i) : ℝ)
  outsideBlueEstimate : ∀ i v, v ∈ clusters i →
    (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
      outsideBlueError
  internalRedEstimate : ∀ i,
    (C.redEdgeCountIn (clusters i) : ℝ) ≤ internalRedError
  /-- The two explicit real approximation errors sum to less than
  one unit of the reduced-degree scale, uniformly for every cluster. -/
  scalarGap : ∀ i,
    (((clusters i).card : ℝ) * weightedError +
          (delta k : ℝ) *
            (((clusters i).card : ℝ) *
                (ownBlueError + outsideBlueError + sizeError) +
              ((referenceDegree : ℝ) / (delta k : ℝ)) * sizeError) +
          2 * internalRedError) +
        (t : ℝ) *
          (2 * ((referenceDegree : ℝ) / (delta k : ℝ) + sizeError) *
              sizeError +
            (dominantColorConstant k * Real.sqrt beta / eta ^ 2) *
              ((referenceDegree : ℝ) / (delta k : ℝ) + sizeError) ^ 2) <
      (referenceDegree : ℝ) ^ 2 / (delta k : ℝ) ^ 2

namespace CoreExtractionFinalClusterCertificate

/-- Forget the F8 scalar data and retain exactly the eight Goal 2c fields. -/
theorem toMixedMassCertificate
    {n₀ k n t : ℕ} {C : ColoredGraph (Fin n)} {eta beta : ℝ}
    {clusters : Fin t → Finset (Fin n)}
    (A : CoreExtractionFinalClusterCertificate
      n₀ k n t C eta beta clusters) :
    CoreExtractionMixedMassCertificate n₀ k n t C eta beta clusters := {
  ambientLarge := A.ambientLarge
  coloring_mem_Ck := A.coloring_mem_Ck
  clusterCount_ge := A.clusterCount_ge
  clusters_pairwiseDisjoint := A.clusters_pairwiseDisjoint
  clusterLowerBound := A.clusterLowerBound
  clusterBalanced := A.clusterBalanced
  blueSparseBetween := A.blueSparseBetween
  vertexControls := A.vertexControls
}

end CoreExtractionFinalClusterCertificate

/- A coarse, quotient-facing allocation of the reduced-degree scalar gap.

The hypotheses deliberately mention only the estimates naturally produced by
the terminal quotient: the reference degree lies between `η n` and `n`, every
cluster has size at most `n`, there are at most `master / η` clusters, and the
five error terms have the displayed hierarchy bounds.  The conclusion is
exactly the expression required by
`CoreExtractionFinalClusterCertificate.scalarGap`, at the mixed-mass parameters
`eta = η / master` and `beta = mixedInput`.

The upper bound on the reference degree is indispensable here: without it the
terms containing `referenceDegree / Δ` are not controlled by an error budget
whose scale is `n`. -/
set_option maxHeartbeats 800000 in
-- Expanding the five error allocations produces a sizeable ordered-ring goal.
theorem CoreExtractionParameters.finalCluster_scalarGap_of_coarse_bounds
    {k n t referenceDegree : ℕ} {η ζ : ℝ}
    (hk : 3 ≤ k) (hη : η ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k η ζ)
    {clusters : Fin t → Finset (Fin n)}
    {sizeError weightedError ownBlueError outsideBlueError
      internalRedError : ℝ}
    (hreferenceDegree_pos : 0 < referenceDegree)
    (hreferenceDegree_lower :
      η * (n : ℝ) ≤ (referenceDegree : ℝ))
    (hreferenceDegree_upper :
      (referenceDegree : ℝ) ≤ (n : ℝ))
    (hclusterUpper : ∀ i, ((clusters i).card : ℝ) ≤ (n : ℝ))
    (hclusterCount : (t : ℝ) ≤ P.master / η)
    (hsizeError_nonneg : 0 ≤ sizeError)
    (hweightedError_nonneg : 0 ≤ weightedError)
    (hownBlueError_nonneg : 0 ≤ ownBlueError)
    (houtsideBlueError_nonneg : 0 ≤ outsideBlueError)
    (hinternalRedError_nonneg : 0 ≤ internalRedError)
    (hweightedError :
      weightedError ≤ P.mixedInput * (n : ℝ))
    (hsizeError :
      sizeError ≤ η * P.tau / 10 * (n : ℝ))
    (hownBlueError :
      ownBlueError ≤ η * P.tau / 10 * (n : ℝ))
    (houtsideBlueError :
      outsideBlueError ≤ η * P.tau / 10 * (n : ℝ))
    (hinternalRedError :
      internalRedError ≤ P.tau ^ 2 * (n : ℝ) ^ 2) :
    ∀ i,
      (((clusters i).card : ℝ) * weightedError +
            (delta k : ℝ) *
              (((clusters i).card : ℝ) *
                  (ownBlueError + outsideBlueError + sizeError) +
                ((referenceDegree : ℝ) / (delta k : ℝ)) * sizeError) +
            2 * internalRedError) +
          (t : ℝ) *
            (2 * ((referenceDegree : ℝ) / (delta k : ℝ) + sizeError) *
                sizeError +
              (dominantColorConstant k * Real.sqrt P.mixedInput /
                  (η / P.master) ^ 2) *
                ((referenceDegree : ℝ) / (delta k : ℝ) + sizeError) ^ 2) <
        (referenceDegree : ℝ) ^ 2 / (delta k : ℝ) ^ 2 := by
  intro i
  let D : ℝ := (delta k : ℝ)
  let N : ℝ := (n : ℝ)
  let K : ℝ := P.master
  let densityError : ℝ :=
    dominantColorConstant k * Real.sqrt P.mixedInput /
      (η / P.master) ^ 2
  have hηpos : 0 < η := hη.1
  have hηone : η < 1 := hη.2
  have hKpos : 0 < K := P.master_pos
  have hKge : (192 : ℝ) ≤ K := P.one_ninety_two_le_master
  have hKone : 1 ≤ K := (by norm_num : (1 : ℝ) ≤ 192).trans hKge
  have hdeltaNat : 0 < delta k := by
    unfold delta
    omega
  have hDpos : 0 < D := by
    have hcast : (0 : ℝ) < (delta k : ℝ) := by
      exact_mod_cast hdeltaNat
    simpa only [D] using hcast
  have hdeltaOne : 1 ≤ delta k := hdeltaNat
  have hDone : 1 ≤ D := by
    have hcast : (1 : ℝ) ≤ (delta k : ℝ) := by
      exact_mod_cast hdeltaOne
    simpa only [D] using hcast
  have hNnonneg : 0 ≤ N := by positivity
  have hreferencePos : (0 : ℝ) < referenceDegree := by
    exact_mod_cast hreferenceDegree_pos
  have hNpos : 0 < N := hreferencePos.trans_le hreferenceDegree_upper
  have hDleK : D ≤ K := by
    have hmaster := P.ten_thousand_mul_delta_add_one_le_master
    change 10000 * (D + 1) ≤ K at hmaster
    nlinarith only [hmaster, hDpos]
  have hDsqLeKsq : D ^ 2 ≤ K ^ 2 :=
    (sq_le_sq₀ hDpos.le hKpos.le).2 hDleK
  have hreferenceLeN : (referenceDegree : ℝ) / D ≤ N := by
    apply (div_le_iff₀ hDpos).2
    calc
      (referenceDegree : ℝ) ≤ N := by
        simpa only [N] using hreferenceDegree_upper
      _ = N * 1 := by ring
      _ ≤ N * D := mul_le_mul_of_nonneg_left hDone hNnonneg
  have hηtau_lt_one : η * P.tau < 1 := by
    calc
      η * P.tau < η * 1 :=
        mul_lt_mul_of_pos_left P.tau_lt_one hηpos
      _ = η := mul_one η
      _ < 1 := hηone
  have htauSqLeTau : P.tau ^ 2 ≤ P.tau := by
    calc
      P.tau ^ 2 = P.tau * P.tau := by ring
      _ ≤ P.tau * 1 :=
        mul_le_mul_of_nonneg_left P.tau_lt_one.le P.tau_pos.le
      _ = P.tau := mul_one P.tau
  have hsmallLeTauN :
      η * P.tau / 10 * N ≤ P.tau * N := by
    have hcoefficient : η / 10 ≤ 1 := by
      linarith only [hηone]
    calc
      η * P.tau / 10 * N = (η / 10) * (P.tau * N) := by ring
      _ ≤ 1 * (P.tau * N) :=
        mul_le_mul_of_nonneg_right hcoefficient
          (mul_nonneg P.tau_pos.le hNnonneg)
      _ = P.tau * N := one_mul _
  have hsmallLeN : η * P.tau / 10 * N ≤ N := by
    have hcoefficient : η * P.tau / 10 ≤ 1 := by
      linarith only [hηtau_lt_one]
    calc
      η * P.tau / 10 * N ≤ 1 * N :=
        mul_le_mul_of_nonneg_right hcoefficient hNnonneg
      _ = N := one_mul _
  have hsizeLeTauN : sizeError ≤ P.tau * N :=
    hsizeError.trans hsmallLeTauN
  have hsizeLeN : sizeError ≤ N := hsizeError.trans hsmallLeN
  have hsumErrors :
      ownBlueError + outsideBlueError + sizeError ≤ P.tau * N := by
    have hthree : 3 * (η / 10) ≤ 1 := by
      linarith only [hηone]
    calc
      ownBlueError + outsideBlueError + sizeError ≤
          3 * (η * P.tau / 10 * N) := by
        linarith only [hownBlueError, houtsideBlueError, hsizeError]
      _ = (3 * (η / 10)) * (P.tau * N) := by ring
      _ ≤ 1 * (P.tau * N) :=
        mul_le_mul_of_nonneg_right hthree
          (mul_nonneg P.tau_pos.le hNnonneg)
      _ = P.tau * N := one_mul _
  have hweighted : weightedError ≤ K * P.tau * N := by
    calc
      weightedError ≤ P.mixedInput * (n : ℝ) := hweightedError
      _ = K * P.tau * N := by
        simp only [K, N, P.mixedInput_eq]
  have hcardNonneg : 0 ≤ ((clusters i).card : ℝ) := by positivity
  have hcard : ((clusters i).card : ℝ) ≤ N := hclusterUpper i
  have hweightedTerm :
      ((clusters i).card : ℝ) * weightedError ≤
        K * P.tau * N ^ 2 := by
    calc
      ((clusters i).card : ℝ) * weightedError ≤
          N * (K * P.tau * N) :=
        mul_le_mul hcard hweighted hweightedError_nonneg hNnonneg
      _ = K * P.tau * N ^ 2 := by ring
  have hclusterErrorTerm :
      D * (((clusters i).card : ℝ) *
          (ownBlueError + outsideBlueError + sizeError)) ≤
        K * P.tau * N ^ 2 := by
    have hsumNonneg :
        0 ≤ ownBlueError + outsideBlueError + sizeError := by
      linarith only [hownBlueError_nonneg, houtsideBlueError_nonneg,
        hsizeError_nonneg]
    have hcardTimes :
        ((clusters i).card : ℝ) *
            (ownBlueError + outsideBlueError + sizeError) ≤
          N * (P.tau * N) :=
      mul_le_mul hcard hsumErrors hsumNonneg hNnonneg
    calc
      D * (((clusters i).card : ℝ) *
          (ownBlueError + outsideBlueError + sizeError)) ≤
          D * (N * (P.tau * N)) := by
        exact mul_le_mul_of_nonneg_left hcardTimes hDpos.le
      _ ≤ K * (N * (P.tau * N)) := by
        exact mul_le_mul_of_nonneg_right hDleK
          (mul_nonneg hNnonneg
            (mul_nonneg P.tau_pos.le hNnonneg))
      _ = K * P.tau * N ^ 2 := by ring
  have hreferenceErrorCancel :
      D * (((referenceDegree : ℝ) / D) * sizeError) =
        (referenceDegree : ℝ) * sizeError := by
    field_simp
  have hreferenceErrorTerm :
      D * (((referenceDegree : ℝ) / D) * sizeError) ≤
        K * P.tau * N ^ 2 := by
    calc
      D * (((referenceDegree : ℝ) / D) * sizeError) =
          (referenceDegree : ℝ) * sizeError := hreferenceErrorCancel
      _ ≤ N * (P.tau * N) :=
        mul_le_mul hreferenceDegree_upper hsizeLeTauN
          hsizeError_nonneg hNnonneg
      _ ≤ K * (P.tau * N ^ 2) := by
        have h := mul_le_mul_of_nonneg_right hKone
          (mul_nonneg P.tau_pos.le (sq_nonneg N))
        nlinarith only [h]
      _ = K * P.tau * N ^ 2 := by ring
  have hinternalTerm :
      2 * internalRedError ≤ 2 * K * P.tau * N ^ 2 := by
    calc
      2 * internalRedError ≤ 2 * (P.tau ^ 2 * N ^ 2) := by
        gcongr
      _ ≤ 2 * (P.tau * N ^ 2) := by
        gcongr
      _ ≤ 2 * (K * P.tau * N ^ 2) := by
        have h := mul_le_mul_of_nonneg_right hKone
          (mul_nonneg P.tau_pos.le (sq_nonneg N))
        nlinarith only [h]
      _ = 2 * K * P.tau * N ^ 2 := by ring
  have hcoreError :
      (((clusters i).card : ℝ) * weightedError +
          D * (((clusters i).card : ℝ) *
              (ownBlueError + outsideBlueError + sizeError) +
            ((referenceDegree : ℝ) / D) * sizeError) +
          2 * internalRedError) ≤
        5 * K * P.tau * N ^ 2 := by
    nlinarith only [hweightedTerm, hclusterErrorTerm,
      hreferenceErrorTerm, hinternalTerm]
  have hreferencePlusSizeNonneg :
      0 ≤ (referenceDegree : ℝ) / D + sizeError := by positivity
  have hreferencePlusSize :
      (referenceDegree : ℝ) / D + sizeError ≤ 2 * N := by
    linarith only [hreferenceLeN, hsizeLeN]
  have hlinearInside :
      2 * ((referenceDegree : ℝ) / D + sizeError) * sizeError ≤
        (2 / 5 : ℝ) * η * P.tau * N ^ 2 := by
    calc
      2 * ((referenceDegree : ℝ) / D + sizeError) * sizeError ≤
          2 * (2 * N) * (η * P.tau / 10 * N) := by
        gcongr
      _ = (2 / 5 : ℝ) * η * P.tau * N ^ 2 := by ring
  have hclusterCountEta : (t : ℝ) * η ≤ K := by
    exact (le_div_iff₀ hηpos).mp (by simpa [K] using hclusterCount)
  have hlinearDegreeError :
      (t : ℝ) *
          (2 * ((referenceDegree : ℝ) / D + sizeError) * sizeError) ≤
        K * P.tau * N ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlinearInside
      (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
    have hcountMul := mul_le_mul_of_nonneg_right hclusterCountEta
      (mul_nonneg P.tau_pos.le (sq_nonneg N))
    calc
      (t : ℝ) *
          (2 * ((referenceDegree : ℝ) / D + sizeError) * sizeError) ≤
          (t : ℝ) * ((2 / 5 : ℝ) * η * P.tau * N ^ 2) := hmul
      _ = (2 / 5 : ℝ) *
          (((t : ℝ) * η) * (P.tau * N ^ 2)) := by ring
      _ ≤ 1 * (((t : ℝ) * η) * (P.tau * N ^ 2)) :=
        mul_le_mul_of_nonneg_right (by norm_num : (2 / 5 : ℝ) ≤ 1)
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg t) hηpos.le)
            (mul_nonneg P.tau_pos.le (sq_nonneg N)))
      _ = ((t : ℝ) * η) * (P.tau * N ^ 2) := one_mul _
      _ ≤ K * (P.tau * N ^ 2) := hcountMul
      _ = K * P.tau * N ^ 2 := by ring
  have hdensityErrorNonneg : 0 ≤ densityError := by
    dsimp [densityError]
    exact div_nonneg
      (mul_nonneg
        (zero_le_one.trans (dominantColorConstant_ge_one hk))
        (Real.sqrt_nonneg P.mixedInput))
      (sq_nonneg (η / P.master))
  have hdensityErrorUpper : densityError ≤ η ^ 4 / K ^ 4 := by
    dsimp [densityError, K]
    exact P.mixedError_regularity.le
  have hmasterDivEtaNonneg : 0 ≤ K / η :=
    div_nonneg hKpos.le hηpos.le
  have hcountDensity :
      (t : ℝ) * densityError ≤ η ^ 3 / K ^ 3 := by
    calc
      (t : ℝ) * densityError ≤
          (K / η) * (η ^ 4 / K ^ 4) :=
        mul_le_mul (by simpa [K] using hclusterCount)
          hdensityErrorUpper hdensityErrorNonneg hmasterDivEtaNonneg
      _ = η ^ 3 / K ^ 3 := by
        field_simp
        <;> ring
  have hreferencePlusSizeSq :
      ((referenceDegree : ℝ) / D + sizeError) ^ 2 ≤ 4 * N ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ hreferencePlusSizeNonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hNnonneg)).2
        hreferencePlusSize
    calc
      ((referenceDegree : ℝ) / D + sizeError) ^ 2 ≤ (2 * N) ^ 2 :=
        hsquare
      _ = 4 * N ^ 2 := by ring
  have hdensityDegreeError :
      (t : ℝ) *
          (densityError *
            ((referenceDegree : ℝ) / D + sizeError) ^ 2) ≤
        4 * η ^ 3 / K ^ 3 * N ^ 2 := by
    calc
      (t : ℝ) *
          (densityError *
            ((referenceDegree : ℝ) / D + sizeError) ^ 2) =
          ((t : ℝ) * densityError) *
            ((referenceDegree : ℝ) / D + sizeError) ^ 2 := by ring
      _ ≤ (η ^ 3 / K ^ 3) * (4 * N ^ 2) :=
        mul_le_mul hcountDensity hreferencePlusSizeSq
          (sq_nonneg _) (by positivity)
      _ = 4 * η ^ 3 / K ^ 3 * N ^ 2 := by ring
  have htotalError :
      ((((clusters i).card : ℝ) * weightedError +
            D * (((clusters i).card : ℝ) *
                (ownBlueError + outsideBlueError + sizeError) +
              ((referenceDegree : ℝ) / D) * sizeError) +
            2 * internalRedError) +
          (t : ℝ) *
            (2 * ((referenceDegree : ℝ) / D + sizeError) * sizeError +
              densityError *
                ((referenceDegree : ℝ) / D + sizeError) ^ 2)) ≤
        (6 * K * P.tau + 4 * η ^ 3 / K ^ 3) * N ^ 2 := by
    nlinarith only [hcoreError, hlinearDegreeError, hdensityDegreeError]
  have hηsixLeηsq : η ^ 6 ≤ η ^ 2 := by
    have hηsqLeOne : η ^ 2 ≤ 1 := by
      have hsquare :=
        (sq_le_sq₀ hηpos.le (by norm_num : (0 : ℝ) ≤ 1)).2 hηone.le
      simpa only [one_pow] using hsquare
    have hηfourLeOne : η ^ 4 ≤ 1 := by
      calc
        η ^ 4 = η ^ 2 * η ^ 2 := by ring
        _ ≤ 1 * 1 :=
          mul_le_mul hηsqLeOne hηsqLeOne (sq_nonneg η) (by norm_num)
        _ = 1 := one_mul 1
    calc
      η ^ 6 = η ^ 2 * η ^ 4 := by ring
      _ ≤ η ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hηfourLeOne (sq_nonneg η)
      _ = η ^ 2 := mul_one _
  have htauWithDelta :
      K * P.tau * D ^ 2 < η ^ 6 / K ^ 2 := by
    calc
      K * P.tau * D ^ 2 < (η ^ 6 / K ^ 4) * D ^ 2 :=
        mul_lt_mul_of_pos_right P.tau_regularity (sq_pos_of_pos hDpos)
      _ ≤ (η ^ 6 / K ^ 4) * K ^ 2 :=
        mul_le_mul_of_nonneg_left hDsqLeKsq (by positivity)
      _ = η ^ 6 / K ^ 2 := by
        field_simp
        <;> ring
  have htauHalf : 6 * K * P.tau * D ^ 2 < η ^ 2 / 2 := by
    have hscaled : 12 * (K * P.tau * D ^ 2) < η ^ 2 := by
      calc
        12 * (K * P.tau * D ^ 2) < 12 * (η ^ 6 / K ^ 2) := by
          gcongr
        _ = (12 * η ^ 6) / K ^ 2 := by ring
        _ ≤ η ^ 2 := by
          apply (div_le_iff₀ (sq_pos_of_pos hKpos)).2
          have hKsq : (12 : ℝ) ≤ K ^ 2 := by
            nlinarith only [hKge, sq_nonneg K]
          calc
            12 * η ^ 6 ≤ 12 * η ^ 2 := by gcongr
            _ = η ^ 2 * 12 := by ring
            _ ≤ η ^ 2 * K ^ 2 :=
              mul_le_mul_of_nonneg_left hKsq (sq_nonneg η)
    linarith only [hscaled]
  have hdensityWithDelta :
      (4 * η ^ 3 / K ^ 3) * D ^ 2 < η ^ 2 / 2 := by
    have hreduce :
        (4 * η ^ 3 / K ^ 3) * D ^ 2 ≤ 4 * η ^ 3 / K := by
      calc
        (4 * η ^ 3 / K ^ 3) * D ^ 2 ≤
            (4 * η ^ 3 / K ^ 3) * K ^ 2 :=
          mul_le_mul_of_nonneg_left hDsqLeKsq (by positivity)
        _ = 4 * η ^ 3 / K := by
          field_simp
          <;> ring
    have hstrict : 4 * η ^ 3 / K < η ^ 2 / 2 := by
      apply (div_lt_iff₀ hKpos).2
      have h8η : 8 * η < K := by
        linarith only [hηone, hKge]
      have hmul := mul_lt_mul_of_pos_left h8η (sq_pos_of_pos hηpos)
      calc
        4 * η ^ 3 = (η ^ 2 * (8 * η)) / 2 := by ring
        _ < (η ^ 2 * K) / 2 :=
          div_lt_div_of_pos_right hmul (by norm_num)
        _ = η ^ 2 / 2 * K := by ring
    exact hreduce.trans_lt hstrict
  have hcoefficientGap :
      (6 * K * P.tau + 4 * η ^ 3 / K ^ 3) * D ^ 2 < η ^ 2 := by
    calc
      (6 * K * P.tau + 4 * η ^ 3 / K ^ 3) * D ^ 2 =
          6 * K * P.tau * D ^ 2 +
            (4 * η ^ 3 / K ^ 3) * D ^ 2 := by ring
      _ < η ^ 2 / 2 + η ^ 2 / 2 :=
        add_lt_add htauHalf hdensityWithDelta
      _ = η ^ 2 := by ring
  have hreferenceSquare : (η * N) ^ 2 ≤ (referenceDegree : ℝ) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hηpos.le hNnonneg) hreferencePos.le).2
      hreferenceDegree_lower
  apply (lt_div_iff₀ (sq_pos_of_pos hDpos)).2
  calc
    ((((clusters i).card : ℝ) * weightedError +
          D * (((clusters i).card : ℝ) *
              (ownBlueError + outsideBlueError + sizeError) +
            ((referenceDegree : ℝ) / D) * sizeError) +
          2 * internalRedError) +
        (t : ℝ) *
          (2 * ((referenceDegree : ℝ) / D + sizeError) * sizeError +
            densityError *
              ((referenceDegree : ℝ) / D + sizeError) ^ 2)) * D ^ 2 ≤
        ((6 * K * P.tau + 4 * η ^ 3 / K ^ 3) * N ^ 2) * D ^ 2 :=
      mul_le_mul_of_nonneg_right htotalError (sq_nonneg D)
    _ = ((6 * K * P.tau + 4 * η ^ 3 / K ^ 3) * D ^ 2) * N ^ 2 := by ring
    _ < η ^ 2 * N ^ 2 :=
      mul_lt_mul_of_pos_right hcoefficientGap (sq_pos_of_pos hNpos)
    _ = (η * N) ^ 2 := by ring
    _ ≤ (referenceDegree : ℝ) ^ 2 := hreferenceSquare

/-- The packaged F6--F8 conclusion for the graph obtained by thresholding
red density at `1/2`. -/
structure CoreExtractionFinalClusterResult
    (k n t : ℕ) (C : ColoredGraph (Fin n)) (eta beta : ℝ)
    (clusters : Fin t → Finset (Fin n)) where
  redDenseOnEdges : ∀ i j,
    (coreExtractionReducedGraph C clusters).Adj i j →
      1 - dominantColorConstant k * Real.sqrt beta / eta ^ 2 ≤
        C.colorDensity .red (clusters i) (clusters j)
  redSmallGreenDenseOnNonedges : ∀ i j, i ≠ j →
    ¬(coreExtractionReducedGraph C clusters).Adj i j →
      C.colorDensity .red (clusters i) (clusters j) ≤
          dominantColorConstant k * Real.sqrt beta / eta ^ 2 ∧
        1 - dominantColorConstant k * Real.sqrt beta / eta ^ 2 ≤
          C.colorDensity .green (clusters i) (clusters j)
  reducedGraph_regular :
    ∀ reducedGraphAdjDecidable :
        DecidableRel (coreExtractionReducedGraph C clusters).Adj,
      letI := reducedGraphAdjDecidable
      ∀ i, (coreExtractionReducedGraph C clusters).degree i = delta k

/-- F6--F8 in one reusable adapter.  Goal 2c supplies the actual
`dominantColorConstant` dichotomy for `coreExtractionReducedGraph`; the
explicit estimates and the single `scalarGap` field then turn both real
approximations into exact `Δ`-regularity.

The extra `max 1` in the returned threshold is used only to infer that every
linearly large cluster is nonempty. -/
theorem exists_coreExtractionFinalClusterResultThreshold
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) (beta : ℝ)
    (hbeta : beta ∈ Set.Ioo (0 : ℝ) (dominantColorBeta₀ k eta)) :
    ∃ n₀ : ℕ,
      ∀ {n t : ℕ} {C : ColoredGraph (Fin n)}
        {clusters : Fin t → Finset (Fin n)},
        CoreExtractionFinalClusterCertificate
            n₀ k n t C eta beta clusters →
          CoreExtractionFinalClusterResult k n t C eta beta clusters := by
  classical
  obtain ⟨nDichotomy, hDichotomy⟩ :=
    exists_coreExtractionReducedGraphDichotomyThreshold
      k hk eta heta beta hbeta
  refine ⟨max 1 nDichotomy, ?_⟩
  intro n t C clusters A
  have hnDichotomy : nDichotomy ≤ n :=
    (le_max_right 1 nDichotomy).trans A.ambientLarge
  have hnOne : 1 ≤ n :=
    (le_max_left 1 nDichotomy).trans A.ambientLarge
  have hMixed :
      CoreExtractionMixedMassCertificate
        nDichotomy k n t C eta beta clusters := {
    ambientLarge := hnDichotomy
    coloring_mem_Ck := A.coloring_mem_Ck
    clusterCount_ge := A.clusterCount_ge
    clusters_pairwiseDisjoint := A.clusters_pairwiseDisjoint
    clusterLowerBound := A.clusterLowerBound
    clusterBalanced := A.clusterBalanced
    blueSparseBetween := A.blueSparseBetween
    vertexControls := A.vertexControls
  }
  have hDich := hDichotomy hMixed
  have hnPos : 0 < n := by omega
  have hnonempty : ∀ i, (clusters i).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro hi
    have hsize := A.clusterLowerBound i
    rw [hi, Finset.card_empty, Nat.cast_zero] at hsize
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
    nlinarith [mul_pos heta.1 hnReal]
  have hdelta : 0 < delta k := by
    unfold delta
    omega
  have hdensityError :
      0 ≤ dominantColorConstant k * Real.sqrt beta / eta ^ 2 := by
    exact div_nonneg
      (mul_nonneg
        (zero_le_one.trans (dominantColorConstant_ge_one hk))
        (Real.sqrt_nonneg beta))
      (sq_nonneg eta)
  exact {
    redDenseOnEdges := hDich.1
    redSmallGreenDenseOnNonedges := hDich.2
    reducedGraph_regular := by
      intro hReducedAdj
      letI := hReducedAdj
      intro i
      apply reducedDegree_eq_delta_of_cluster_estimates
        hdelta A.referenceDegree_pos C clusters
        (coreExtractionReducedGraph C clusters) i
        A.sizeError A.weightedError A.ownBlueError A.outsideBlueError
        A.internalRedError
        (dominantColorConstant k * Real.sqrt beta / eta ^ 2)
        A.sizeError_nonneg A.weightedError_nonneg A.ownBlueError_nonneg
        A.outsideBlueError_nonneg A.internalRedError_nonneg hdensityError
        A.clusters_pairwiseDisjoint hnonempty A.sizeAroundReference
        (A.weightedEstimate i) (A.ownBlueEstimate i)
        (A.outsideBlueEstimate i) (A.internalRedEstimate i)
        (fun {a b} hab ↦ hDich.1 a b hab)
        (fun {a b} hab hnonadj ↦ (hDich.2 a b hab hnonadj).1)
      simpa only [Fintype.card_fin] using A.scalarGap i
  }

/-! ## Generic overlap classes

The stage-cluster quotient later in core extraction uses only the following
finite-set argument.  It is stated independently of colored graphs so that
the nontrivial transitivity step is available without carrying any of the
iteration data.
-/

section OverlapClasses

variable {I V : Type*} [DecidableEq V]

/-- Two members of a finite-set family are close when their symmetric
difference has cardinality at most `error`.  The symmetric difference is
written transparently as the union of the two directed differences. -/
def overlapClose (W : I → Finset V) (error : ℕ) (i j : I) : Prop :=
  ((W i \ W j) ∪ (W j \ W i)).card ≤ error

instance overlapCloseDecidable (W : I → Finset V) (error : ℕ) (i j : I) :
    Decidable (overlapClose W error i j) := by
  unfold overlapClose
  infer_instance

@[simp]
theorem overlapClose_refl (W : I → Finset V) (error : ℕ) (i : I) :
    overlapClose W error i i := by
  simp [overlapClose]

theorem overlapClose_symm {W : I → Finset V} {error : ℕ} {i j : I}
    (h : overlapClose W error i j) : overlapClose W error j i := by
  simpa only [overlapClose, Finset.union_comm] using h

/-! ### The blue-degree overlap dichotomy -/

/-- Exact finite form of the overlap-gap argument from the seed iteration.

Each typical set `W i` lies in a part `A i`. A typical vertex has at least
`baseBlue` blue neighbors in its own part, at most `nonblueCap` nonblue
neighbors there, and total blue degree at most `baseBlue + externalError`.
Moreover, deleting the atypical vertices loses at most `partLoss` vertices
from a part. Two typical sets are therefore either disjoint or have
symmetric difference at most twice the sum of the three losses.

This statement is deliberately integral: all floor/ceiling estimates belong
in the seed-stage constructor, while the combinatorial contradiction itself
uses no asymptotic notation. -/
theorem overlapClose_or_disjoint_of_blue_bounds
    {I V : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (A W : I → Finset V)
    (baseBlue externalError partLoss nonblueCap : ℕ)
    (hsubset : ∀ i, W i ⊆ A i)
    (hloss : ∀ i, (A i \ W i).card ≤ partLoss)
    (hinside : ∀ i v, v ∈ W i →
      baseBlue ≤ C.blueDegreeIn v (A i))
    (hnonblue : ∀ i v, v ∈ W i →
      C.redDegreeIn v (A i) + C.greenDegreeIn v (A i) ≤ nonblueCap)
    (htotal : ∀ i v, v ∈ W i →
      C.blueDegree v ≤ baseBlue + externalError) :
    ∀ i j,
      overlapClose W (2 * (partLoss + nonblueCap + externalError)) i j ∨
        Disjoint (W i) (W j) := by
  classical
  let loss := partLoss + nonblueCap + externalError
  have hdegreeMono (c : EdgeColor) (v : V) {S T : Finset V}
      (hST : S ⊆ T) : C.degreeIn c v S ≤ C.degreeIn c v T := by
    unfold degreeIn neighborFinsetIn
    apply Finset.card_le_card
    intro w hw
    rw [Finset.mem_inter] at hw ⊢
    exact ⟨hw.1, hST hw.2⟩
  have horiented (i j : I) (v : V) (hvi : v ∈ W i) (hvj : v ∈ W j)
      (hlarge : loss < (W j \ W i).card) : False := by
    let outside := W j \ A i
    have hcover : W j \ W i ⊆ outside ∪ (A i \ W i) := by
      intro w hw
      have hwj := (Finset.mem_sdiff.mp hw).1
      have hwni := (Finset.mem_sdiff.mp hw).2
      by_cases hwA : w ∈ A i
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwA, hwni⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hwj, hwA⟩)
    have hcardCover : (W j \ W i).card ≤ outside.card + (A i \ W i).card :=
      (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have houtsideLarge : nonblueCap + externalError < outside.card := by
      have := hloss i
      dsimp [loss] at hlarge
      omega
    have houtsideSubsetPart : outside ⊆ A j := by
      intro w hw
      exact hsubset j (Finset.mem_sdiff.mp hw).1
    have hvOutside : v ∉ outside := by
      intro hv
      exact (Finset.mem_sdiff.mp hv).2 (hsubset i hvi)
    have hcolors :=
      C.redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_not_mem
        v outside hvOutside
    change C.redDegreeIn v outside + C.greenDegreeIn v outside +
      C.blueDegreeIn v outside = outside.card at hcolors
    have hredMono : C.redDegreeIn v outside ≤ C.redDegreeIn v (A j) :=
      hdegreeMono .red v houtsideSubsetPart
    have hgreenMono : C.greenDegreeIn v outside ≤ C.greenDegreeIn v (A j) :=
      hdegreeMono .green v houtsideSubsetPart
    have hnonblueOutside :
        C.redDegreeIn v outside + C.greenDegreeIn v outside ≤ nonblueCap :=
      (Nat.add_le_add hredMono hgreenMono).trans (hnonblue j v hvj)
    have hblueOutside : externalError < C.blueDegreeIn v outside := by
      omega
    have houtsideSubsetCompl : outside ⊆ (A i)ᶜ := by
      intro w hw
      simpa using (Finset.mem_sdiff.mp hw).2
    have hblueMono :
        C.blueDegreeIn v outside ≤ C.blueDegreeIn v (A i)ᶜ :=
      hdegreeMono .blue v houtsideSubsetCompl
    have hsplit := C.degreeIn_add_degreeIn_compl .blue v (A i)
    change C.blueDegreeIn v (A i) + C.blueDegreeIn v (A i)ᶜ =
      C.blueDegree v at hsplit
    have hin := hinside i v hvi
    have hout : externalError < C.blueDegreeIn v (A i)ᶜ :=
      hblueOutside.trans_le hblueMono
    have htot := htotal i v hvi
    omega
  intro i j
  by_cases hclose :
      overlapClose W (2 * (partLoss + nonblueCap + externalError)) i j
  · exact Or.inl hclose
  · refine Or.inr (Finset.disjoint_left.2 ?_)
    intro v hvi hvj
    have hdiffDisjoint : Disjoint (W i \ W j) (W j \ W i) := by
      refine Finset.disjoint_left.2 ?_
      intro a hai haj
      exact (Finset.mem_sdiff.mp hai).2 (Finset.mem_sdiff.mp haj).1
    have hcard :
        ((W i \ W j) ∪ (W j \ W i)).card =
          (W i \ W j).card + (W j \ W i).card :=
      Finset.card_union_of_disjoint hdiffDisjoint
    have hlargeUnion :
        2 * (partLoss + nonblueCap + externalError) <
          ((W i \ W j) ∪ (W j \ W i)).card := by
      unfold overlapClose at hclose
      omega
    have hone :
        loss < (W i \ W j).card ∨ loss < (W j \ W i).card := by
      dsimp [loss]
      omega
    rcases hone with hij | hji
    · exact horiented j i v hvj hvi hij
    · exact horiented i j v hvi hvj hji

/-- Under the close-or-disjoint dichotomy, closeness is transitive provided
every family member is larger than twice the error.  In the disjoint branch
for the two outer sets, their common close middle set is covered by its two
directed differences, so it would have size at most `2 * error`. -/
theorem overlapClose_trans_of_dichotomy {W : I → Finset V} {error : ℕ}
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card)
    {i j k : I} (hij : overlapClose W error i j)
    (hjk : overlapClose W error j k) : overlapClose W error i k := by
  rcases dichotomy i k with hik | hikDisjoint
  · exact hik
  · exfalso
    have hjSubset :
        W j ⊆ (W j \ W i) ∪ (W j \ W k) := by
      intro v hvj
      by_cases hvi : v ∈ W i
      · have hvk : v ∉ W k := by
          intro hvk
          exact Finset.disjoint_left.mp hikDisjoint hvi hvk
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvj, hvk⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvj, hvi⟩)
    have hjiDifference : (W j \ W i).card ≤ error := by
      exact (Finset.card_le_card Finset.subset_union_right).trans hij
    have hjkDifference : (W j \ W k).card ≤ error := by
      exact (Finset.card_le_card Finset.subset_union_left).trans hjk
    have hjCard : (W j).card ≤ 2 * error := by
      calc
        (W j).card ≤ ((W j \ W i) ∪ (W j \ W k)).card :=
          Finset.card_le_card hjSubset
        _ ≤ (W j \ W i).card + (W j \ W k).card :=
          Finset.card_union_le _ _
        _ ≤ 2 * error := by omega
    exact (Nat.not_lt_of_ge hjCard) (large j)

/-- The equivalence relation induced by a close-or-disjoint family of large
finite sets. -/
def overlapCloseSetoid (W : I → Finset V) (error : ℕ)
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card) : Setoid I where
  r := overlapClose W error
  iseqv.refl := overlapClose_refl W error
  iseqv.symm := overlapClose_symm
  iseqv.trans := overlapClose_trans_of_dichotomy dichotomy large

@[simp]
theorem overlapCloseSetoid_apply (W : I → Finset V) (error : ℕ)
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card) (i j : I) :
    overlapCloseSetoid W error dichotomy large i j ↔
      overlapClose W error i j :=
  Iff.rfl

section FiniteIndex

variable [Fintype I] [DecidableEq I]

/-- The concrete finite equivalence class represented by `i`.  Keeping the
class as a `Finset` makes subsequent cardinality and intersection arguments
independent of quotient elimination. -/
def overlapClass (W : I → Finset V) (error : ℕ) (i : I) : Finset I :=
  Finset.univ.filter fun j ↦ overlapClose W error j i

@[simp]
theorem mem_overlapClass {W : I → Finset V} {error : ℕ} {i j : I} :
    j ∈ overlapClass W error i ↔ overlapClose W error j i := by
  simp [overlapClass]

@[simp]
theorem self_mem_overlapClass (W : I → Finset V) (error : ℕ) (i : I) :
    i ∈ overlapClass W error i := by
  simp

theorem overlapClass_eq_of_close {W : I → Finset V} {error : ℕ}
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card)
    {i j : I} (hij : overlapClose W error i j) :
    overlapClass W error i = overlapClass W error j := by
  ext x
  simp only [mem_overlapClass]
  constructor
  · intro hxi
    exact overlapClose_trans_of_dichotomy dichotomy large hxi hij
  · intro hxj
    exact overlapClose_trans_of_dichotomy dichotomy large hxj
      (overlapClose_symm hij)

theorem overlapClose_of_overlapClass_eq {W : I → Finset V} {error : ℕ}
    {i j : I} (hclasses : overlapClass W error i = overlapClass W error j) :
    overlapClose W error i j := by
  have hi : i ∈ overlapClass W error i := self_mem_overlapClass W error i
  rw [hclasses] at hi
  exact mem_overlapClass.mp hi

theorem overlapClass_eq_iff_close {W : I → Finset V} {error : ℕ}
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card) {i j : I} :
    overlapClass W error i = overlapClass W error j ↔
      overlapClose W error i j := by
  exact ⟨overlapClose_of_overlapClass_eq,
    overlapClass_eq_of_close dichotomy large⟩

/-- If indices in the same stage label give disjoint sets, then an overlap
class contains at most one index of each stage.  Consequently every class is
bounded by the number of stage labels.  This is the finite quotient form of
the paper's “at most one representative from each iteration” observation. -/
theorem overlapClass_card_le_stageCount
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {W : I → Finset V} {error : ℕ}
    (stage : I → Q)
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card)
    (sameStageDisjoint : ∀ i j, i ≠ j → stage i = stage j →
      Disjoint (W i) (W j)) (representative : I) :
    (overlapClass W error representative).card ≤ Fintype.card Q := by
  classical
  change (overlapClass W error representative).card ≤
    (Finset.univ : Finset Q).card
  refine Finset.card_le_card_of_injOn stage (by simp [Set.MapsTo]) ?_
  intro i hi j hj hstage
  by_contra hij
  have hir : overlapClose W error i representative :=
    mem_overlapClass.mp hi
  have hjr : overlapClose W error j representative :=
    mem_overlapClass.mp hj
  have hijClose : overlapClose W error i j :=
    overlapClose_trans_of_dichotomy dichotomy large hir
      (overlapClose_symm hjr)
  have hijDisjoint : Disjoint (W i) (W j) :=
    sameStageDisjoint i j hij hstage
  have hiSubset :
      W i ⊆ (W i \ W j) ∪ (W j \ W i) := by
    intro v hvi
    have hvj : v ∉ W j := by
      intro hvj
      exact Finset.disjoint_left.mp hijDisjoint hvi hvj
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvi, hvj⟩)
  have hiCard : (W i).card ≤ error :=
    (Finset.card_le_card hiSubset).trans hijClose
  have hlarge := large i
  omega

/-- Distinct concrete overlap classes have disjoint representative sets. -/
theorem disjoint_of_overlapClass_ne {W : I → Finset V} {error : ℕ}
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card) {i j : I}
    (hclasses : overlapClass W error i ≠ overlapClass W error j) :
    Disjoint (W i) (W j) := by
  rcases dichotomy i j with hij | hij
  · exact False.elim (hclasses (overlapClass_eq_of_close dichotomy large hij))
  · exact hij

section FiniteVertices

variable [Fintype V]

/-- The final set attached to a concrete overlap class is the intersection
of all family members in that class. -/
def overlapClassIntersection (W : I → Finset V) (error : ℕ) (i : I) :
    Finset V :=
  Finset.univ.filter fun v ↦ ∀ j ∈ overlapClass W error i, v ∈ W j

@[simp]
theorem mem_overlapClassIntersection {W : I → Finset V} {error : ℕ}
    {i : I} {v : V} :
    v ∈ overlapClassIntersection W error i ↔
      ∀ j, overlapClose W error j i → v ∈ W j := by
  simp [overlapClassIntersection]

theorem overlapClassIntersection_subset {W : I → Finset V} {error : ℕ}
    {i j : I} (hji : overlapClose W error j i) :
    overlapClassIntersection W error i ⊆ W j := by
  intro v hv
  exact mem_overlapClassIntersection.mp hv j hji

theorem overlapClassIntersection_subset_rep (W : I → Finset V)
    (error : ℕ) (i : I) : overlapClassIntersection W error i ⊆ W i :=
  overlapClassIntersection_subset (overlapClose_refl W error i)

theorem overlapClassIntersection_eq_of_close {W : I → Finset V}
    {error : ℕ}
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card)
    {i j : I} (hij : overlapClose W error i j) :
    overlapClassIntersection W error i =
      overlapClassIntersection W error j := by
  unfold overlapClassIntersection
  rw [overlapClass_eq_of_close dichotomy large hij]

/-- The intersection loses at most `error` vertices for each member of its
concrete overlap class. -/
theorem overlapClass_card_le_intersection_add_error {W : I → Finset V}
    {error : ℕ} (i : I) :
    (W i).card ≤ (overlapClassIntersection W error i).card +
      (overlapClass W error i).card * error := by
  classical
  let final := overlapClassIntersection W error i
  let cls := overlapClass W error i
  have hfinalSubset : final ⊆ W i := by
    simpa only [final] using overlapClassIntersection_subset_rep W error i
  have hlossSubset :
      W i \ final ⊆ cls.biUnion fun j ↦ W i \ W j := by
    intro v hv
    have hvi : v ∈ W i := (Finset.mem_sdiff.mp hv).1
    have hvFinal : v ∉ final := (Finset.mem_sdiff.mp hv).2
    have hnotAll : ¬ ∀ j ∈ cls, v ∈ W j := by
      intro hall
      apply hvFinal
      simp only [final, overlapClassIntersection, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa only [cls] using hall
    push Not at hnotAll
    obtain ⟨j, hjClass, hvj⟩ := hnotAll
    exact Finset.mem_biUnion.mpr
      ⟨j, hjClass, Finset.mem_sdiff.mpr ⟨hvi, hvj⟩⟩
  have hpiece : ∀ j ∈ cls, (W i \ W j).card ≤ error := by
    intro j hj
    have hji : overlapClose W error j i := by
      exact mem_overlapClass.mp (by simpa only [cls] using hj)
    exact (Finset.card_le_card Finset.subset_union_right).trans hji
  have hlossCard : (W i \ final).card ≤ cls.card * error := by
    exact (Finset.card_le_card hlossSubset).trans
      (Finset.card_biUnion_le_card_mul cls (fun j ↦ W i \ W j) error hpiece)
  have hdecompose := Finset.card_sdiff_add_card_eq_card hfinalSubset
  dsimp only [final, cls] at hlossCard hdecompose ⊢
  omega

theorem overlapClassIntersection_card_lower_of_class_card_le
    {W : I → Finset V} {error L : ℕ} {i : I}
    (hclass : (overlapClass W error i).card ≤ L) :
    (W i).card - L * error ≤
      (overlapClassIntersection W error i).card := by
  have hmain := overlapClass_card_le_intersection_add_error
    (W := W) (error := error) i
  have hmul : (overlapClass W error i).card * error ≤ L * error :=
    Nat.mul_le_mul_right error hclass
  omega

/-- Distinct overlap classes give disjoint final intersections. -/
theorem disjoint_overlapClassIntersections_of_ne
    {W : I → Finset V} {error : ℕ}
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card) {i j : I}
    (hclasses : overlapClass W error i ≠ overlapClass W error j) :
    Disjoint (overlapClassIntersection W error i)
      (overlapClassIntersection W error j) := by
  exact (disjoint_of_overlapClass_ne dichotomy large hclasses).mono
    (overlapClassIntersection_subset_rep W error i)
    (overlapClassIntersection_subset_rep W error j)

/-! ### Concrete finite indexing of the overlap quotient -/

/-- The finite set of distinct concrete overlap classes. -/
def overlapClassFamily (W : I → Finset V) (error : ℕ) :
    Finset (Finset I) :=
  Finset.univ.image fun i ↦ overlapClass W error i

@[simp]
theorem mem_overlapClassFamily {W : I → Finset V} {error : ℕ}
    {s : Finset I} :
    s ∈ overlapClassFamily W error ↔
      ∃ i : I, overlapClass W error i = s := by
  simp [overlapClassFamily]

/-- A concrete finite type with one element for every overlap class. -/
def OverlapClassIndex (W : I → Finset V) (error : ℕ) :=
  {s : Finset I // s ∈ overlapClassFamily W error}

noncomputable instance overlapClassIndexFintype
    (W : I → Finset V) (error : ℕ) :
    Fintype (OverlapClassIndex W error) :=
  Fintype.ofFinset (overlapClassFamily W error) (fun _ ↦ Iff.rfl)

/-- Every concrete class index has an original stage-cluster representative. -/
theorem overlapClassIndex_exists_source (W : I → Finset V) (error : ℕ)
    (q : OverlapClassIndex W error) :
    ∃ i : I, overlapClass W error i = q.1 := by
  exact mem_overlapClassFamily.mp q.2

/-- A chosen representative of a concrete overlap class. -/
noncomputable def overlapClassSource (W : I → Finset V) (error : ℕ)
    (q : OverlapClassIndex W error) : I :=
  Classical.choose (overlapClassIndex_exists_source W error q)

theorem overlapClassSource_spec (W : I → Finset V) (error : ℕ)
    (q : OverlapClassIndex W error) :
    overlapClass W error (overlapClassSource W error q) = q.1 :=
  Classical.choose_spec (overlapClassIndex_exists_source W error q)

/-- The canonical class index containing an original family member. -/
def overlapClassIndexOf (W : I → Finset V) (error : ℕ) (i : I) :
    OverlapClassIndex W error :=
  ⟨overlapClass W error i, by simp⟩

/-- The number of distinct overlap classes. -/
noncomputable def overlapClassCount (W : I → Finset V) (error : ℕ) : ℕ :=
  Fintype.card (OverlapClassIndex W error)

/-- Relabel the concrete overlap classes by an initial interval. -/
noncomputable def overlapClassEquivFin (W : I → Finset V) (error : ℕ) :
    OverlapClassIndex W error ≃ Fin (overlapClassCount W error) :=
  Fintype.equivFin (OverlapClassIndex W error)

/-- The final clusters, indexed by `Fin`, are the intersections belonging to
the distinct overlap classes. -/
noncomputable def overlapFinalClusters (W : I → Finset V) (error : ℕ) :
    Fin (overlapClassCount W error) → Finset V :=
  fun q ↦ overlapClassIntersection W error
    (overlapClassSource W error ((overlapClassEquivFin W error).symm q))

/-- The `Fin`-indexed cluster corresponding to `i` is exactly the concrete
intersection of the class of `i`. -/
theorem overlapFinalClusters_at_indexOf (W : I → Finset V) (error : ℕ)
    (i : I) :
    overlapFinalClusters W error
        (overlapClassEquivFin W error (overlapClassIndexOf W error i)) =
      overlapClassIntersection W error i := by
  unfold overlapFinalClusters
  rw [Equiv.symm_apply_apply]
  unfold overlapClassIntersection
  rw [overlapClassSource_spec]
  rfl

/-- Distinct `Fin` indices give disjoint final clusters. -/
theorem overlapFinalClusters_pairwiseDisjoint
    (W : I → Finset V) (error : ℕ)
    (dichotomy : ∀ i j, overlapClose W error i j ∨ Disjoint (W i) (W j))
    (large : ∀ i, 2 * error < (W i).card) :
    Set.PairwiseDisjoint
      (Set.univ : Set (Fin (overlapClassCount W error)))
      (overlapFinalClusters W error) := by
  intro i _ j _ hij
  let E := overlapClassEquivFin W error
  let qi := E.symm i
  let qj := E.symm j
  have hq : qi ≠ qj := by
    intro h
    apply hij
    calc
      i = E qi := (E.apply_symm_apply i).symm
      _ = E qj := congrArg E h
      _ = j := E.apply_symm_apply j
  have hclass :
      overlapClass W error (overlapClassSource W error qi) ≠
        overlapClass W error (overlapClassSource W error qj) := by
    intro h
    apply hq
    apply Subtype.ext
    rw [← overlapClassSource_spec W error qi,
      ← overlapClassSource_spec W error qj]
    exact h
  exact disjoint_overlapClassIntersections_of_ne dichotomy large hclass

/-- A nonempty family has at least one overlap class. -/
theorem overlapClassCount_pos (W : I → Finset V) (error : ℕ)
    [Nonempty I] : 0 < overlapClassCount W error := by
  classical
  let i : I := Classical.choice inferInstance
  have hnonempty : Nonempty (OverlapClassIndex W error) :=
    ⟨overlapClassIndexOf W error i⟩
  exact Fintype.card_pos_iff.mpr hnonempty

end FiniteVertices

end FiniteIndex

end OverlapClasses

section UniformStageOverlapBridge

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {k : ℕ} {C : ColoredGraph V} {control : Finset V}
variable {reference error : ℝ}

abbrev UniformStageList :=
  List (UniformCoreSeedStage k C control reference error)

/-- A pair consisting of a stage position and a part within that stage. -/
abbrev UniformStagePartIndex (run : UniformStageList (k := k) (C := C)
    (control := control) (reference := reference) (error := error)) :=
  Fin run.length × Fin (delta k)

/-- The stage at a finite position in a nonempty or empty run. -/
def uniformStageAt (run : UniformStageList (k := k) (C := C)
    (control := control) (reference := reference) (error := error))
    (q : Fin run.length) : UniformCoreSeedStage k C control reference error :=
  run.get q

/-- The ambient partition part associated to a stage-part index. -/
def uniformStagePart (run : UniformStageList (k := k) (C := C)
    (control := control) (reference := reference) (error := error))
    (a : UniformStagePartIndex run) : Finset V :=
  (uniformStageAt run a.1).parts a.2

/-- The typical set associated to a stage-part index. -/
def uniformStageTypical (run : UniformStageList (k := k) (C := C)
    (control := control) (reference := reference) (error := error))
    (a : UniformStagePartIndex run) : Finset V :=
  (uniformStageAt run a.1).typical a.2

/-- The stage-position projection from the stage-part index. -/
def uniformStageLabel (run : UniformStageList (k := k) (C := C)
    (control := control) (reference := reference) (error := error))
    (a : UniformStagePartIndex run) : Fin run.length := a.1

theorem uniformStageTypical_subset_part
    (run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error))
    (a : UniformStagePartIndex run) :
    uniformStageTypical run a ⊆ uniformStagePart run a := by
  exact (uniformStageAt run a.1).typical_subset_part a.2

/-- Distinct typical parts carrying the same stage label are disjoint. -/
theorem uniformStageTypical_sameStage_disjoint
    (run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error))
    (a b : UniformStagePartIndex run) (hab : a ≠ b)
    (hstage : uniformStageLabel run a = uniformStageLabel run b) :
    Disjoint (uniformStageTypical run a) (uniformStageTypical run b) := by
  rcases a with ⟨qa, ia⟩
  rcases b with ⟨qb, ib⟩
  change qa = qb at hstage
  subst qb
  have hpart : ia ≠ ib := by
    intro h
    apply hab
    exact Prod.ext rfl h
  have hparts : Disjoint
      (uniformStagePart run (qa, ia)) (uniformStagePart run (qa, ib)) := by
    exact (uniformStageAt run qa).parts_pairwiseDisjoint
      (Set.mem_univ ia) (Set.mem_univ ib) hpart
  exact hparts.mono (uniformStageTypical_subset_part run (qa, ia))
    (uniformStageTypical_subset_part run (qa, ib))

/-- Natural rounding data sufficient to apply the integral overlap-gap
lemma uniformly to every stage-part pair in a run. -/
structure UniformStageOverlapBounds
    (run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)) where
  baseBlue : ℕ
  externalError : ℕ
  partLoss : ℕ
  nonblueCap : ℕ
  baseBlue_round :
    (baseBlue : ℝ) ≤ reference / (delta k : ℝ) - error
  partLoss_round : 2 * error ≤ (partLoss : ℝ)
  totalBlue_round :
    reference / (delta k : ℝ) + 2 * error ≤
      ((baseBlue + externalError : ℕ) : ℝ)
  internalNonblueCap_le : ∀ q : Fin run.length,
    (uniformStageAt run q).internalNonblueCap ≤ nonblueCap
  large_round :
    2 * (2 * (partLoss + nonblueCap + externalError)) < baseBlue

namespace UniformStageOverlapBounds

def overlapError {run : UniformStageList (k := k) (C := C)
    (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) : ℕ :=
  2 * (B.partLoss + B.nonblueCap + B.externalError)

theorem baseBlue_le_typical_card
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (a : UniformStagePartIndex run) :
    B.baseBlue ≤ (uniformStageTypical run a).card := by
  have hbalanced := (uniformStageAt run a.1).typicalBalanced a.2
  have hlower := (abs_le.mp hbalanced).1
  have hlower' : reference / (delta k : ℝ) - error ≤
      ((uniformStageTypical run a).card : ℝ) := by
    simpa [uniformStageTypical] using hlower
  have hreal : (B.baseBlue : ℝ) ≤
      ((uniformStageTypical run a).card : ℝ) :=
    B.baseBlue_round.trans hlower'
  exact_mod_cast hreal

theorem typical_large
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (a : UniformStagePartIndex run) :
    2 * B.overlapError < (uniformStageTypical run a).card := by
  exact B.large_round.trans_le (B.baseBlue_le_typical_card a)

end UniformStageOverlapBounds

/-- The overlap-gap dichotomy instantiated for a list of uniform stages. -/
theorem uniformStageOverlap_dichotomy
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) :
    ∀ a b : UniformStagePartIndex run,
      overlapClose (uniformStageTypical run) B.overlapError a b ∨
        Disjoint (uniformStageTypical run a) (uniformStageTypical run b) := by
  apply overlapClose_or_disjoint_of_blue_bounds C
    (uniformStagePart run) (uniformStageTypical run)
    B.baseBlue B.externalError B.partLoss B.nonblueCap
  · exact uniformStageTypical_subset_part run
  · intro a
    have hloss := (uniformStageAt run a.1).partTypicalLoss a.2
    have hloss' :
        (((uniformStagePart run a \ uniformStageTypical run a).card : ℕ) : ℝ) ≤
          2 * error := by
      simpa [uniformStagePart, uniformStageTypical] using hloss
    have hreal : (((uniformStagePart run a \ uniformStageTypical run a).card : ℕ) : ℝ) ≤
        (B.partLoss : ℝ) := by
      exact hloss'.trans B.partLoss_round
    exact_mod_cast hreal
  · intro a v hv
    have hin := (uniformStageAt run a.1).highInternalBlue a.2 v hv
    have hreal : (B.baseBlue : ℝ) ≤
        (C.blueDegreeIn v (uniformStagePart run a) : ℝ) := by
      exact B.baseBlue_round.trans
        (by simpa [uniformStagePart] using hin)
    exact_mod_cast hreal
  · intro a v hv
    exact ((uniformStageAt run a.1).lowInternalNonblue a.2 v hv).trans
      (B.internalNonblueCap_le a.1)
  · intro a v hv
    have htotal := (uniformStageAt run a.1).totalBlueUpper a.2 v hv
    have hreal : (C.blueDegree v : ℝ) ≤
        ((B.baseBlue + B.externalError : ℕ) : ℝ) :=
      htotal.trans B.totalBlue_round
    exact_mod_cast hreal

theorem uniformStageOverlap_trans
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) {a b c : UniformStagePartIndex run}
    (hab : overlapClose (uniformStageTypical run) B.overlapError a b)
    (hbc : overlapClose (uniformStageTypical run) B.overlapError b c) :
    overlapClose (uniformStageTypical run) B.overlapError a c :=
  overlapClose_trans_of_dichotomy (uniformStageOverlap_dichotomy B)
    B.typical_large hab hbc

def uniformStageOverlapSetoid
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) : Setoid (UniformStagePartIndex run) :=
  overlapCloseSetoid (uniformStageTypical run) B.overlapError
    (uniformStageOverlap_dichotomy B) B.typical_large

/-- Every concrete overlap class contains at most one part from each stage. -/
theorem uniformStageOverlapClass_card_le_length
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (representative : UniformStagePartIndex run) :
    (overlapClass (uniformStageTypical run) B.overlapError representative).card ≤
      run.length := by
  simpa using overlapClass_card_le_stageCount
    (W := uniformStageTypical run) (stage := uniformStageLabel run)
    (uniformStageOverlap_dichotomy B) B.typical_large
    (uniformStageTypical_sameStage_disjoint run) representative

/-- A nonempty stage list and `k ≥ 3` give a nonempty stage-part index. -/
theorem uniformStagePartIndex_nonempty
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (hk : 3 ≤ k) (hrun : run ≠ []) : Nonempty (UniformStagePartIndex run) := by
  have hlength : 0 < run.length := by
    cases run with
    | nil => contradiction
    | cons => simp
  have hdelta : 0 < delta k := by
    unfold delta
    omega
  exact ⟨⟨⟨0, hlength⟩, ⟨0, hdelta⟩⟩⟩

/-- The concrete final clusters obtained by intersecting each overlap class
and relabeling the distinct classes by `Fin`. -/
noncomputable def uniformStageFinalClusters
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) :
    Fin (overlapClassCount (uniformStageTypical run) B.overlapError) → Finset V :=
  overlapFinalClusters (uniformStageTypical run) B.overlapError

theorem uniformStageFinalClusters_pairwiseDisjoint
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) :
    Set.PairwiseDisjoint
      (Set.univ : Set
        (Fin (overlapClassCount (uniformStageTypical run) B.overlapError)))
      (uniformStageFinalClusters B) := by
  exact overlapFinalClusters_pairwiseDisjoint
    (uniformStageTypical run) B.overlapError
    (uniformStageOverlap_dichotomy B) B.typical_large

/-- Each final intersection retains the rounded typical-set lower bound,
apart from at most one overlap error for every stage in the run. -/
theorem uniformStageFinalClusters_card_lower
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    B.baseBlue - run.length * B.overlapError ≤
      (uniformStageFinalClusters B q).card := by
  let source := overlapClassSource (uniformStageTypical run) B.overlapError
    ((overlapClassEquivFin (uniformStageTypical run) B.overlapError).symm q)
  have hclass :
      (overlapClass (uniformStageTypical run) B.overlapError source).card ≤
        run.length :=
    uniformStageOverlapClass_card_le_length B source
  have hinter := overlapClassIntersection_card_lower_of_class_card_le
    (W := uniformStageTypical run) (error := B.overlapError) hclass
  have hbase := B.baseBlue_le_typical_card source
  have hlower := (Nat.sub_le_sub_right hbase
    (run.length * B.overlapError)).trans hinter
  simpa [uniformStageFinalClusters, overlapFinalClusters, source] using hlower

/-- Every final cluster remains balanced around the common reference size;
intersection costs at most `run.length * overlapError`. -/
theorem uniformStageFinalClusters_balanced
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    |((uniformStageFinalClusters B q).card : ℝ) -
        reference / (delta k : ℝ)| ≤
      error + ((run.length * B.overlapError : ℕ) : ℝ) := by
  let source := overlapClassSource (uniformStageTypical run) B.overlapError
    ((overlapClassEquivFin (uniformStageTypical run) B.overlapError).symm q)
  let final := overlapClassIntersection (uniformStageTypical run)
    B.overlapError source
  have hclass :
      (overlapClass (uniformStageTypical run) B.overlapError source).card ≤
        run.length :=
    uniformStageOverlapClass_card_le_length B source
  have hmain := overlapClass_card_le_intersection_add_error
    (W := uniformStageTypical run) (error := B.overlapError) source
  have hmul :
      (overlapClass (uniformStageTypical run) B.overlapError source).card *
          B.overlapError ≤ run.length * B.overlapError :=
    Nat.mul_le_mul_right B.overlapError hclass
  have hlossNat : (uniformStageTypical run source).card ≤
      final.card + run.length * B.overlapError := by
    dsimp only [final]
    exact hmain.trans (Nat.add_le_add_left hmul _)
  have hloss : ((uniformStageTypical run source).card : ℝ) ≤
      (final.card : ℝ) + ((run.length * B.overlapError : ℕ) : ℝ) := by
    exact_mod_cast hlossNat
  have hfinalSubset : final ⊆ uniformStageTypical run source := by
    exact overlapClassIntersection_subset_rep
      (uniformStageTypical run) B.overlapError source
  have hfinalCardNat : final.card ≤ (uniformStageTypical run source).card :=
    Finset.card_le_card hfinalSubset
  have hfinalCard : (final.card : ℝ) ≤
      ((uniformStageTypical run source).card : ℝ) := by
    exact_mod_cast hfinalCardNat
  have htypical := (uniformStageAt run source.1).typicalBalanced source.2
  have htypical' :
      |((uniformStageTypical run source).card : ℝ) -
          reference / (delta k : ℝ)| ≤ error := by
    simpa [uniformStageTypical] using htypical
  have hlower := (abs_le.mp htypical').1
  have hupper := (abs_le.mp htypical').2
  have hlossNonneg : (0 : ℝ) ≤
      ((run.length * B.overlapError : ℕ) : ℝ) := by positivity
  have hbalancedFinal :
      |(final.card : ℝ) - reference / (delta k : ℝ)| ≤
        error + ((run.length * B.overlapError : ℕ) : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  simpa [uniformStageFinalClusters, overlapFinalClusters, source, final] using
    hbalancedFinal

/-- A nonempty uniform run has a nonempty concrete overlap quotient. -/
theorem uniformStageOverlapClassCount_pos
    {run : UniformStageList (k := k) (C := C)
      (control := control) (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (hk : 3 ≤ k) (hrun : run ≠ []) :
    0 < overlapClassCount (uniformStageTypical run) B.overlapError := by
  letI : Nonempty (UniformStagePartIndex run) :=
    uniformStagePartIndex_nonempty hk hrun
  exact overlapClassCount_pos (uniformStageTypical run) B.overlapError

end UniformStageOverlapBridge

namespace UniformCoreSeedStage

/-- If a stage contributes more new red-neighborhood vertices than all
part losses can absorb, one typical part has correspondingly large new mass. -/
theorem exists_typical_sdiff_card_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} {C : ColoredGraph V} {control : Finset V}
    {reference error : ℝ}
    (S : UniformCoreSeedStage k C control reference error)
    (covered : Finset V) (overlapError partLoss newMass : ℕ)
    (hloss : ∀ i, (S.parts i \ S.typical i).card ≤ partLoss)
    (hnew : newMass ≤ (S.redNeighborhood \ covered).card)
    (hmass : delta k * (overlapError + partLoss) < newMass) :
    ∃ i : Fin (delta k),
      overlapError < (S.typical i \ covered).card := by
  by_contra hnone
  have htypical : ∀ i : Fin (delta k),
      (S.typical i \ covered).card ≤ overlapError := by
    intro i
    exact Nat.le_of_not_gt (fun hi ↦ hnone ⟨i, hi⟩)
  have hpiece : ∀ i : Fin (delta k),
      (S.parts i \ covered).card ≤ overlapError + partLoss := by
    intro i
    have hsubset : S.parts i \ covered ⊆
        (S.typical i \ covered) ∪ (S.parts i \ S.typical i) := by
      intro v hv
      have hvpart := (Finset.mem_sdiff.mp hv).1
      have hvcovered := (Finset.mem_sdiff.mp hv).2
      by_cases hvtypical : v ∈ S.typical i
      · exact Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨hvtypical, hvcovered⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hvpart, hvtypical⟩)
    exact (Finset.card_le_card hsubset).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add (htypical i) (hloss i)))
  have hcoveredSubset : S.redNeighborhood \ covered ⊆
      (Finset.univ : Finset (Fin (delta k))).biUnion
        (fun i ↦ S.parts i \ covered) := by
    intro v hv
    have hvred := (Finset.mem_sdiff.mp hv).1
    have hvcovered := (Finset.mem_sdiff.mp hv).2
    rw [← S.parts_cover] at hvred
    rcases Finset.mem_biUnion.mp hvred with ⟨i, hi, hvi⟩
    exact Finset.mem_biUnion.mpr
      ⟨i, hi, Finset.mem_sdiff.mpr ⟨hvi, hvcovered⟩⟩
  have hcard : (S.redNeighborhood \ covered).card ≤
      delta k * (overlapError + partLoss) := by
    calc
      (S.redNeighborhood \ covered).card ≤
          ((Finset.univ : Finset (Fin (delta k))).biUnion
            (fun i ↦ S.parts i \ covered)).card :=
        Finset.card_le_card hcoveredSubset
      _ ≤ (Finset.univ : Finset (Fin (delta k))).card *
          (overlapError + partLoss) :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun i _ ↦ hpiece i)
      _ = delta k * (overlapError + partLoss) := by simp
  omega

end UniformCoreSeedStage

/-- A stage with sufficiently large new red-neighborhood mass contributes
an overlap class distinct from every earlier set contained in `covered`. -/
theorem exists_new_overlapClass_of_newNeighborhoodMass
    {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V]
    {k : ℕ} {C : ColoredGraph V} {control : Finset V}
    {reference error : ℝ}
    (W : I → Finset V) (old : Finset I)
    (S : UniformCoreSeedStage k C control reference error)
    (partIndex : Fin (delta k) → I) (covered : Finset V)
    (overlapError partLoss newMass : ℕ)
    (hpart : ∀ i, W (partIndex i) = S.typical i)
    (hold : ∀ j ∈ old, W j ⊆ covered)
    (hloss : ∀ i, (S.parts i \ S.typical i).card ≤ partLoss)
    (hnew : newMass ≤ (S.redNeighborhood \ covered).card)
    (hmass : delta k * (overlapError + partLoss) < newMass) :
    ∃ i : Fin (delta k), ∀ j ∈ old,
      overlapClass W overlapError (partIndex i) ≠
        overlapClass W overlapError j := by
  obtain ⟨i, hi⟩ := S.exists_typical_sdiff_card_gt covered
    overlapError partLoss newMass hloss hnew hmass
  refine ⟨i, ?_⟩
  intro j hj hclasses
  have hclose : overlapClose W overlapError (partIndex i) j :=
    overlapClose_of_overlapClass_eq hclasses
  have hsubset : S.typical i \ covered ⊆
      (W (partIndex i) \ W j) ∪ (W j \ W (partIndex i)) := by
    intro v hv
    have hvtypical := (Finset.mem_sdiff.mp hv).1
    have hvcovered := (Finset.mem_sdiff.mp hv).2
    have hvnew : v ∈ W (partIndex i) := by simpa [hpart i] using hvtypical
    have hvold : v ∉ W j := by
      intro hvj
      exact hvcovered (hold j hj hvj)
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvnew, hvold⟩)
  have hcard := Finset.card_le_card hsubset
  unfold overlapClose at hclose
  omega

/-! ## Generic bounded iteration -/

/-- A prefix-dependent run starts at `seed` and is built by appending one
vertex at a time whenever `canExtend` holds for the entire earlier prefix. -/
inductive BoundedRunValid {V : Type*} (seed : V)
    (canExtend : List V → V → Prop) : List V → Prop where
  | singleton : BoundedRunValid seed canExtend [seed]
  | append {run : List V} {v : V} :
      BoundedRunValid seed canExtend run →
      canExtend run v →
      BoundedRunValid seed canExtend (run ++ [v])

namespace BoundedRunValid

variable {V : Type*} {seed : V} {canExtend : List V → V → Prop}

/-- The constructor form used at graph-specific seed stages. -/
theorem append_of_valid {run : List V}
    (hrun : BoundedRunValid seed canExtend run) {v : V}
    (hv : canExtend run v) :
    BoundedRunValid seed canExtend (run ++ [v]) :=
  BoundedRunValid.append hrun hv

@[simp]
theorem length_append_singleton (run : List V) (v : V) :
    (run ++ [v]).length = run.length + 1 := by
  simp

theorem nonempty {run : List V}
    (hrun : BoundedRunValid seed canExtend run) : run ≠ [] := by
  induction hrun with
  | singleton => simp
  | append hrun hv ih => simp

theorem head?_eq {run : List V}
    (hrun : BoundedRunValid seed canExtend run) : run.head? = some seed := by
  induction hrun with
  | singleton => simp
  | append hrun hv ih =>
      rw [List.head?_append]
      simp [ih]

end BoundedRunValid

/-- One explicit greedy step.  It appends a chosen legal extension when one
exists and otherwise leaves the run fixed. -/
noncomputable def boundedGreedyStep {V : Type*}
    (canExtend : List V → V → Prop) (run : List V) : List V := by
  classical
  exact if h : ∃ v, canExtend run v then
    run ++ [Classical.choose h]
  else
    run

/-- The explicit finite greedy construction.  It either appends one chosen
extension or remains fixed once no extension exists. -/
noncomputable def boundedGreedyRun {V : Type*} (seed : V)
    (canExtend : List V → V → Prop) : ℕ → List V
  | 0 => [seed]
  | n + 1 => boundedGreedyStep canExtend (boundedGreedyRun seed canExtend n)

@[simp]
theorem boundedGreedyRun_zero {V : Type*} (seed : V)
    (canExtend : List V → V → Prop) :
    boundedGreedyRun seed canExtend 0 = [seed] := rfl

theorem boundedGreedyRun_succ {V : Type*} (seed : V)
    (canExtend : List V → V → Prop) (n : ℕ) :
    boundedGreedyRun seed canExtend (n + 1) =
      boundedGreedyStep canExtend (boundedGreedyRun seed canExtend n) := rfl

theorem boundedGreedyRun_valid {V : Type*} (seed : V)
    (canExtend : List V → V → Prop) (n : ℕ) :
    BoundedRunValid seed canExtend (boundedGreedyRun seed canExtend n) := by
  induction n with
  | zero => exact .singleton
  | succ n ih =>
      classical
      rw [boundedGreedyRun_succ]
      unfold boundedGreedyStep
      split_ifs with h
      · exact .append ih (Classical.choose_spec h)
      · exact ih

/-- If the greedy run is still extendable after `n` trials, then it has
extended at every trial and therefore has the maximal possible trial length. -/
theorem boundedGreedyRun_length_eq_of_extendable {V : Type*} (seed : V)
    (canExtend : List V → V → Prop) (n : ℕ)
    (hterminal : ∃ v, canExtend (boundedGreedyRun seed canExtend n) v) :
    (boundedGreedyRun seed canExtend n).length = n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      classical
      rw [boundedGreedyRun_succ] at hterminal ⊢
      unfold boundedGreedyStep at hterminal ⊢
      by_cases hprev : ∃ v, canExtend (boundedGreedyRun seed canExtend n) v
      · simp [hprev, ih hprev]
      · simp [hprev] at hterminal

/-- A genuinely finite bounded-extension construction: under a uniform
length bound, greedy iteration produces a valid run beginning at `seed` that
has no legal terminal extension. -/
theorem exists_maximal_boundedRun {V : Type*} (seed : V)
    (canExtend : List V → V → Prop) {L : ℕ} (_hL : 0 < L)
    (hbound : ∀ run, BoundedRunValid seed canExtend run → run.length ≤ L) :
    ∃ run, BoundedRunValid seed canExtend run ∧
      run.length ≤ L ∧ ∀ v, ¬ canExtend run v := by
  let run := boundedGreedyRun seed canExtend L
  have hvalid : BoundedRunValid seed canExtend run := by
    exact boundedGreedyRun_valid seed canExtend L
  have hlen : run.length ≤ L := hbound run hvalid
  refine ⟨run, hvalid, hlen, ?_⟩
  intro v hv
  have hextend : ∃ w, canExtend run w := ⟨v, hv⟩
  have heq : run.length = L + 1 := by
    exact boundedGreedyRun_length_eq_of_extendable seed canExtend L hextend
  omega

/-- Stopping rule for the form used in core extraction: every vertex
satisfying the prefix-dependent eligibility condition fails the required
new-mass condition at the terminal prefix. -/
theorem exists_maximal_boundedRun_and_stop {V : Type*} (seed : V)
    (eligible newMass : List V → V → Prop) {L : ℕ} (hL : 0 < L)
    (hbound : ∀ run,
      BoundedRunValid seed (fun run' v ↦ eligible run' v ∧ newMass run' v) run →
        run.length ≤ L) :
    ∃ run,
      BoundedRunValid seed
        (fun run' v ↦ eligible run' v ∧ newMass run' v) run ∧
      run.length ≤ L ∧
      ∀ v, eligible run v → ¬ newMass run v := by
  obtain ⟨run, hvalid, hlen, hstop⟩ :=
    exists_maximal_boundedRun seed
      (fun run' v ↦ eligible run' v ∧ newMass run' v) hL hbound
  exact ⟨run, hvalid, hlen, fun v helig hmass ↦ hstop v ⟨helig, hmass⟩⟩

/-! ## Stage F3: finite growth of seed-stage neighborhoods -/

/-- The vertices covered by the neighborhoods of a finite stage run. -/
def stageNeighborhoodUnion {S V : Type*} [DecidableEq V]
    (neighborhood : S → Finset V) : List S → Finset V
  | [] => ∅
  | s :: run => neighborhood s ∪ stageNeighborhoodUnion neighborhood run

@[simp]
theorem stageNeighborhoodUnion_nil {S V : Type*} [DecidableEq V]
    (neighborhood : S → Finset V) :
    stageNeighborhoodUnion neighborhood [] = ∅ := rfl

@[simp]
theorem stageNeighborhoodUnion_cons {S V : Type*} [DecidableEq V]
    (neighborhood : S → Finset V) (s : S) (run : List S) :
    stageNeighborhoodUnion neighborhood (s :: run) =
      neighborhood s ∪ stageNeighborhoodUnion neighborhood run := rfl

/-- Appending a stage adjoins exactly its neighborhood to the covered set. -/
theorem stageNeighborhoodUnion_append_singleton {S V : Type*}
    [DecidableEq V] (neighborhood : S → Finset V) (run : List S) (s : S) :
    stageNeighborhoodUnion neighborhood (run ++ [s]) =
      stageNeighborhoodUnion neighborhood run ∪ neighborhood s := by
  induction run with
  | nil => simp
  | cons t run ih =>
      simp only [List.cons_append, stageNeighborhoodUnion_cons, ih]
      simp only [Finset.union_assoc]

/-- Exact increase in covered vertices when a stage is appended. -/
theorem card_stageNeighborhoodUnion_append_singleton {S V : Type*}
    [DecidableEq V] (neighborhood : S → Finset V) (run : List S) (s : S) :
    (stageNeighborhoodUnion neighborhood (run ++ [s])).card =
      (stageNeighborhoodUnion neighborhood run).card +
        (neighborhood s \ stageNeighborhoodUnion neighborhood run).card := by
  rw [stageNeighborhoodUnion_append_singleton]
  simpa [Finset.union_comm, Nat.add_comm] using
    (Finset.card_sdiff_add_card (neighborhood s)
      (stageNeighborhoodUnion neighborhood run)).symm

/-- A stage has `newMass` genuinely new vertices relative to the prefix. -/
def stageHasNewMass {S V : Type*} [DecidableEq V]
    (neighborhood : S → Finset V) (newMass : ℕ) (run : List S) (s : S) : Prop :=
  newMass ≤
    (neighborhood s \ stageNeighborhoodUnion neighborhood run).card

/-- Validity of a stage run with an abstract prefix-dependent eligibility
condition and a fixed lower bound on the new neighborhood mass at each append. -/
abbrev StageRunValid {S V : Type*} [DecidableEq V] (seed : S)
    (eligible : List S → S → Prop) (neighborhood : S → Finset V)
    (newMass : ℕ) : List S → Prop :=
  BoundedRunValid seed
    (fun run s ↦ eligible run s ∧ stageHasNewMass neighborhood newMass run s)

namespace StageRunValid

/-- Exact counting along a valid run: all stages after the seed contribute
at least `newMass` vertices not covered by earlier neighborhoods. -/
theorem newMass_mul_le_union_card {S V : Type*} [DecidableEq V]
    {seed : S} {eligible : List S → S → Prop}
    {neighborhood : S → Finset V} {newMass : ℕ} {run : List S}
    (hrun : StageRunValid seed eligible neighborhood newMass run) :
    (run.length - 1) * newMass ≤
      (stageNeighborhoodUnion neighborhood run).card := by
  induction hrun with
  | singleton => simp
  | @append run s hrun hstep ih =>
      have hnonempty : run ≠ [] := BoundedRunValid.nonempty hrun
      have hlength : 1 ≤ run.length := by
        cases run with
        | nil => contradiction
        | cons => simp
      calc
        ((run ++ [s]).length - 1) * newMass =
            run.length * newMass := by simp
        _ = ((run.length - 1) + 1) * newMass := by
          rw [Nat.sub_add_cancel hlength]
        _ = (run.length - 1) * newMass + newMass := by
          simp [Nat.add_mul]
        _ ≤ (stageNeighborhoodUnion neighborhood run).card +
              (neighborhood s \ stageNeighborhoodUnion neighborhood run).card :=
          Nat.add_le_add ih hstep.2
        _ = (stageNeighborhoodUnion neighborhood (run ++ [s])).card :=
          (card_stageNeighborhoodUnion_append_singleton neighborhood run s).symm

/-- The new-mass count is bounded by the total size of the ambient finite
vertex type. -/
theorem newMass_mul_le_card {S V : Type*} [Fintype V] [DecidableEq V]
    {seed : S} {eligible : List S → S → Prop}
    {neighborhood : S → Finset V} {newMass : ℕ} {run : List S}
    (hrun : StageRunValid seed eligible neighborhood newMass run) :
    (run.length - 1) * newMass ≤ Fintype.card V := by
  calc
    (run.length - 1) * newMass ≤
        (stageNeighborhoodUnion neighborhood run).card :=
      newMass_mul_le_union_card hrun
    _ ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card V := Finset.card_univ

/-- A strict ambient-capacity inequality bounds the number of stages in
every valid run. -/
theorem length_le_of_card_lt_mul {S V : Type*} [Fintype V] [DecidableEq V]
    {seed : S} {eligible : List S → S → Prop}
    {neighborhood : S → Finset V} {newMass L : ℕ} {run : List S}
    (hrun : StageRunValid seed eligible neighborhood newMass run)
    (hcapacity : Fintype.card V < L * newMass) :
    run.length ≤ L := by
  have hcount := newMass_mul_le_card hrun
  have hnewMass : 0 < newMass := by
    by_contra hzero
    have : newMass = 0 := Nat.eq_zero_of_not_pos hzero
    simp [this] at hcapacity
  have hproduct : (run.length - 1) * newMass < L * newMass :=
    lt_of_le_of_lt hcount hcapacity
  have hsub : run.length - 1 < L :=
    (Nat.mul_lt_mul_right hnewMass).mp hproduct
  have hnonempty : run ≠ [] := BoundedRunValid.nonempty hrun
  have hlength : 1 ≤ run.length := by
    cases run with
    | nil => contradiction
    | cons => simp
  omega

end StageRunValid

/-- Greedy finite stopping for stage neighborhoods.  At the terminal valid
run, every still-eligible stage has fewer than `newMass` new vertices. -/
theorem exists_maximal_stageRun_and_stop {S V : Type*}
    [Fintype V] [DecidableEq V] (seed : S)
    (eligible : List S → S → Prop) (neighborhood : S → Finset V)
    (newMass L : ℕ) (hL : 0 < L)
    (hcapacity : Fintype.card V < L * newMass) :
    ∃ run,
      StageRunValid seed eligible neighborhood newMass run ∧
      run.length ≤ L ∧
      ∀ s, eligible run s →
        (neighborhood s \ stageNeighborhoodUnion neighborhood run).card <
          newMass := by
  obtain ⟨run, hvalid, hlength, hstop⟩ :=
    exists_maximal_boundedRun_and_stop seed eligible
      (stageHasNewMass neighborhood newMass) hL (by
        intro run' hrun'
        exact StageRunValid.length_le_of_card_lt_mul hrun' hcapacity)
  refine ⟨run, hvalid, hlength, ?_⟩
  intro s helig
  exact Nat.lt_of_not_ge (hstop s helig)

/-! ### Concrete specialization to seed-stage data -/

namespace CoreSeedStage

/-- The union of the typical parts supplied by one seed stage. -/
def typicalUnion {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} {C : ColoredGraph V} {edgeError : ℝ} {control : Finset V}
    {cap : ℕ} {reference redError weightedError controlLoss : ℝ}
    (A : CoreSeedStage k C edgeError control cap
      reference redError weightedError controlLoss) : Finset V :=
  (Finset.univ : Finset (Fin (delta k))).biUnion A.typical

/-- Every vertex in a stage's typical union belongs to the fixed control
set used to construct the stage. -/
theorem typicalUnion_subset_control {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} {C : ColoredGraph V} {edgeError : ℝ} {control : Finset V}
    {cap : ℕ} {reference redError weightedError controlLoss : ℝ}
    (A : CoreSeedStage k C edgeError control cap
      reference redError weightedError controlLoss) :
    A.typicalUnion ⊆ control := by
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨i, hi, hvi⟩
  exact A.typical_controlled i hvi

end CoreSeedStage

section CoreSeedStageRun

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {k : ℕ} {C : ColoredGraph V} {edgeError : ℝ} {control : Finset V}
variable {cap : ℕ} {reference redError weightedError controlLoss : ℝ}

/-- The fixed seed-stage type used by one run. -/
abbrev FixedCoreSeedStage := CoreSeedStage k C edgeError control cap
  reference redError weightedError controlLoss

/-- Typical vertices exposed by all seed stages in a prefix. -/
def coreSeedRunTypicalUnion (run : List (FixedCoreSeedStage (k := k) (C := C)
    (edgeError := edgeError) (control := control) (cap := cap)
    (reference := reference) (redError := redError)
    (weightedError := weightedError) (controlLoss := controlLoss))) : Finset V :=
  stageNeighborhoodUnion CoreSeedStage.typicalUnion run

/-- Red-neighborhood vertices covered by all seed stages in a prefix. -/
def coreSeedRunRedNeighborhoodUnion
    (run : List (FixedCoreSeedStage (k := k) (C := C)
      (edgeError := edgeError) (control := control) (cap := cap)
      (reference := reference) (redError := redError)
      (weightedError := weightedError) (controlLoss := controlLoss))) : Finset V :=
  stageNeighborhoodUnion (fun A ↦ A.redNeighborhood) run

/-- A candidate next stage is eligible when its seed is controlled and
belongs to a typical set exposed at an earlier stage. -/
def coreSeedStageEligible
    (run : List (FixedCoreSeedStage (k := k) (C := C)
      (edgeError := edgeError) (control := control) (cap := cap)
      (reference := reference) (redError := redError)
      (weightedError := weightedError) (controlLoss := controlLoss)))
    (next : FixedCoreSeedStage (k := k) (C := C)
      (edgeError := edgeError) (control := control) (cap := cap)
      (reference := reference) (redError := redError)
      (weightedError := weightedError) (controlLoss := controlLoss)) : Prop :=
  next.seed ∈ control ∧ next.seed ∈ coreSeedRunTypicalUnion run

/-- Concrete F3 stopping theorem for seed-stage objects of one cleaned
coloring.  The realization hypothesis is exactly the remaining local-Turán
obligation: every currently eligible vertex can be packaged as a stage.
The conclusion is the paper's terminal red-neighborhood mass condition. -/
theorem exists_maximal_coreSeedStageRun_and_stop
    (initial : FixedCoreSeedStage (k := k) (C := C)
      (edgeError := edgeError) (control := control) (cap := cap)
      (reference := reference) (redError := redError)
      (weightedError := weightedError) (controlLoss := controlLoss))
    (newMass L : ℕ) (hL : 0 < L)
    (hcapacity : Fintype.card V < L * newMass)
    (realize : ∀
      (run : List (FixedCoreSeedStage (k := k) (C := C)
        (edgeError := edgeError) (control := control) (cap := cap)
        (reference := reference) (redError := redError)
        (weightedError := weightedError) (controlLoss := controlLoss)))
      (v : V),
      v ∈ control → v ∈ coreSeedRunTypicalUnion run →
      ∃ next : FixedCoreSeedStage (k := k) (C := C)
        (edgeError := edgeError) (control := control) (cap := cap)
        (reference := reference) (redError := redError)
        (weightedError := weightedError) (controlLoss := controlLoss),
        next.seed = v) :
    ∃ run,
      StageRunValid initial coreSeedStageEligible
        (fun A ↦ A.redNeighborhood) newMass run ∧
      run.length ≤ L ∧
      ∀ v ∈ control, v ∈ coreSeedRunTypicalUnion run →
        (C.redNeighborFinset v \ coreSeedRunRedNeighborhoodUnion run).card <
          newMass := by
  obtain ⟨run, hvalid, hlength, hstop⟩ :=
    exists_maximal_stageRun_and_stop initial coreSeedStageEligible
      (fun A ↦ A.redNeighborhood) newMass L hL hcapacity
  refine ⟨run, hvalid, hlength, ?_⟩
  intro v hvcontrol hvtypical
  obtain ⟨next, hseed⟩ := realize run v hvcontrol hvtypical
  have hnext := hstop next ⟨by simpa [hseed] using hvcontrol,
    by simpa [hseed] using hvtypical⟩
  rw [next.redNeighborhood_eq, hseed] at hnext
  exact hnext

end CoreSeedStageRun

/-! ### Indexed seed-stage runs and terminal erasure -/

/-- Taking neighborhoods commutes with mapping a list of stage objects. -/
@[simp]
theorem stageNeighborhoodUnion_map {S T V : Type*} [DecidableEq V]
    (neighborhood : T → Finset V) (f : S → T) (run : List S) :
    stageNeighborhoodUnion neighborhood (run.map f) =
      stageNeighborhoodUnion (fun s ↦ neighborhood (f s)) run := by
  induction run with
  | nil => rfl
  | cons s run ih => simp [ih]

namespace IndexedUniformCoreSeedStage

/-- The union of the typical parts exposed by one indexed stage. -/
def typicalUnion
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)} {control : Finset (Fin n)}
    {reference : ℝ}
    (S : IndexedUniformCoreSeedStage P C control reference) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin (delta k))).biUnion S.stage.typical

/-- Every typical vertex of an indexed stage lies in its fixed control set. -/
theorem typicalUnion_subset_control
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)} {control : Finset (Fin n)}
    {reference : ℝ}
    (S : IndexedUniformCoreSeedStage P C control reference) :
    S.typicalUnion ⊆ control := by
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨i, hi, hvi⟩
  exact S.stage.typical_controlled i hvi

@[simp]
theorem terminalStage_seed
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)} {control : Finset (Fin n)}
    {reference : ℝ}
    (S : IndexedUniformCoreSeedStage P C control reference) :
    S.terminalStage.seed = S.stage.seed := rfl

@[simp]
theorem terminalStage_redNeighborhood
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)} {control : Finset (Fin n)}
    {reference : ℝ}
    (S : IndexedUniformCoreSeedStage P C control reference) :
    S.terminalStage.redNeighborhood = S.stage.redNeighborhood := rfl

@[simp]
theorem terminalStage_typical
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)} {control : Finset (Fin n)}
    {reference : ℝ}
    (S : IndexedUniformCoreSeedStage P C control reference)
    (i : Fin (delta k)) :
    S.terminalStage.typical i = S.stage.typical i := rfl

@[simp]
theorem terminalStage_typicalUnion
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)} {control : Finset (Fin n)}
    {reference : ℝ}
    (S : IndexedUniformCoreSeedStage P C control reference) :
    (Finset.univ : Finset (Fin (delta k))).biUnion
        S.terminalStage.typical = S.typicalUnion := by
  ext v
  simp [typicalUnion]

end IndexedUniformCoreSeedStage

section IndexedUniformCoreSeedStageRun

variable {k n : ℕ} {eta zeta : ℝ}
variable {P : CoreExtractionParameters k eta zeta}
variable {C : ColoredGraph (Fin n)} {control : Finset (Fin n)}
variable {reference : ℝ}

/-- The homogeneous type of level-indexed stages for one cleaned coloring. -/
abbrev IndexedCoreSeedStage :=
  IndexedUniformCoreSeedStage P C control reference

/-- Typical vertices exposed by all indexed stages in a prefix. -/
def indexedStageRunTypicalUnion
    (run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))) : Finset (Fin n) :=
  stageNeighborhoodUnion IndexedUniformCoreSeedStage.typicalUnion run

/-- Red-neighborhood vertices covered by all indexed stages in a prefix. -/
def indexedStageRunRedNeighborhoodUnion
    (run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))) : Finset (Fin n) :=
  stageNeighborhoodUnion (fun S ↦ S.stage.redNeighborhood) run

/-- A next indexed stage is eligible precisely at the next unused level, and
its seed must be both controlled and exposed by a prior typical part. -/
def indexedCoreSeedStageEligible
    (run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference)))
    (next : IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference)) : Prop :=
  next.level.val = run.length ∧
    next.stage.seed ∈ control ∧
      next.stage.seed ∈ indexedStageRunTypicalUnion run

/-- Erase the level-dependent errors in an indexed run by weakening every
stage to the common terminal error.  This is the homogeneous list consumed
by the overlap quotient. -/
noncomputable def indexedRunTerminalStages
    (run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))) :
    UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := P.terminalError n) :=
  run.map IndexedUniformCoreSeedStage.terminalStage

@[simp]
theorem indexedRunTerminalStages_length
    (run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))) :
    (indexedRunTerminalStages run).length = run.length := by
  simp [indexedRunTerminalStages]

/-- Terminal erasure preserves the red-neighborhood union exactly. -/
theorem stageNeighborhoodUnion_indexedRunTerminalStages
    (run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))) :
    stageNeighborhoodUnion
        (fun S : UniformCoreSeedStage k C control reference
          (P.terminalError n) ↦ S.redNeighborhood)
        (indexedRunTerminalStages run) =
      indexedStageRunRedNeighborhoodUnion run := by
  simp [indexedRunTerminalStages, indexedStageRunRedNeighborhoodUnion]

/-- Terminal erasure preserves the union of all typical parts exactly. -/
theorem typicalUnion_indexedRunTerminalStages
    (run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))) :
    stageNeighborhoodUnion
        (fun S : UniformCoreSeedStage k C control reference
            (P.terminalError n) ↦
          (Finset.univ : Finset (Fin (delta k))).biUnion S.typical)
        (indexedRunTerminalStages run) =
      indexedStageRunTypicalUnion run := by
  simp [indexedRunTerminalStages, indexedStageRunTypicalUnion]

/-- Looking up a terminally erased list entry is the same as looking up the
indexed entry and then erasing its level.  The natural index avoids inserting
irrelevant casts between the propositionally equal list lengths. -/
theorem getElem_indexedRunTerminalStages
    (run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference)))
    (i : ℕ) (hi : i < (indexedRunTerminalStages run).length) :
    (indexedRunTerminalStages run)[i]'hi =
      (run[i]'(by simpa [indexedRunTerminalStages] using hi)).terminalStage := by
  simp [indexedRunTerminalStages]

/-- The common cap stored in each indexed stage survives weakening to the
terminal error and passage to the erased run. -/
theorem indexedRunTerminalStages_internalNonblueCap_le
    (run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference)))
    (q : Fin (indexedRunTerminalStages run).length) :
    (uniformStageAt (indexedRunTerminalStages run) q).internalNonblueCap ≤
      coreSeedNonblueCap (P.betaSeq (Fin.last P.stageBound)) n := by
  have hmem : uniformStageAt (indexedRunTerminalStages run) q ∈
      indexedRunTerminalStages run := List.get_mem _ _
  change uniformStageAt
      (run.map IndexedUniformCoreSeedStage.terminalStage) q ∈
    run.map IndexedUniformCoreSeedStage.terminalStage at hmem
  rcases List.mem_map.mp hmem with ⟨S, _hS, hS⟩
  change (uniformStageAt
      (run.map IndexedUniformCoreSeedStage.terminalStage) q).internalNonblueCap ≤
    coreSeedNonblueCap (P.betaSeq (Fin.last P.stageBound)) n
  rw [← hS]
  exact S.terminalNonblueCap

/-- A valid indexed run uses the levels `0, ..., run.length - 1` in order. -/
theorem indexedCoreSeedStageRun_levels_eq_range
    (initial : IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))
    (hinitial : initial.level.val = 0) {newMass : ℕ}
    {run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))}
    (hrun : StageRunValid initial indexedCoreSeedStageEligible
      (fun S ↦ S.stage.redNeighborhood) newMass run) :
    run.map (fun S ↦ S.level.val) = List.range run.length := by
  induction hrun with
  | singleton => simp [hinitial]
  | @append run next hrun hnext ih =>
      have hlevel : next.level.val = run.length := hnext.1.1
      simp [ih, hlevel, List.range_succ]

/-- The finite ambient capacity bounds the length of every indexed stage run. -/
theorem indexedCoreSeedStageRun_length_le
    (initial : IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))
    {newMass L : ℕ}
    {run : List (IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))}
    (hrun : StageRunValid initial indexedCoreSeedStageEligible
      (fun S ↦ S.stage.redNeighborhood) newMass run)
    (hcapacity : n < L * newMass) :
    run.length ≤ L := by
  apply StageRunValid.length_le_of_card_lt_mul hrun
  simpa using hcapacity

/-- Maximal indexed seed iteration.  The realization input is deliberately
per-level: it only has to package an eligible vertex into a stage at a supplied
finite level.  The strict inequality `L < stageBound` ensures that the maximal
run still has a level available when the stopping condition is tested. -/
theorem exists_maximal_indexedCoreSeedStageRun_and_stop
    (initial : IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))
    (hinitial : initial.level.val = 0)
    (newMass L : ℕ) (hL : 0 < L) (hLBound : L < P.stageBound)
    (hcapacity : n < L * newMass)
    (realize : ∀
      (q : Fin P.stageBound)
      (run : List (IndexedCoreSeedStage (P := P) (C := C)
        (control := control) (reference := reference)))
      (v : Fin n),
      run.length = q.val →
      v ∈ control → v ∈ indexedStageRunTypicalUnion run →
      ∃ next : IndexedCoreSeedStage (P := P) (C := C)
        (control := control) (reference := reference),
        next.level = q ∧ next.stage.seed = v) :
    ∃ run,
      StageRunValid initial indexedCoreSeedStageEligible
        (fun S ↦ S.stage.redNeighborhood) newMass run ∧
      run.length ≤ L ∧
      run.map (fun S ↦ S.level.val) = List.range run.length ∧
      ∀ v ∈ control, v ∈ indexedStageRunTypicalUnion run →
        (C.redNeighborFinset v \ indexedStageRunRedNeighborhoodUnion run).card <
          newMass := by
  have hcard : Fintype.card (Fin n) < L * newMass := by
    simpa using hcapacity
  obtain ⟨run, hvalid, hlength, hstop⟩ :=
    exists_maximal_stageRun_and_stop initial indexedCoreSeedStageEligible
      (fun S ↦ S.stage.redNeighborhood) newMass L hL hcard
  refine ⟨run, hvalid, hlength,
    indexedCoreSeedStageRun_levels_eq_range initial hinitial hvalid, ?_⟩
  intro v hvcontrol hvtypical
  let q : Fin P.stageBound :=
    ⟨run.length, lt_of_le_of_lt hlength hLBound⟩
  obtain ⟨next, hlevel, hseed⟩ :=
    realize q run v rfl hvcontrol hvtypical
  have heligible : indexedCoreSeedStageEligible run next := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hlevel]
    · simpa [hseed] using hvcontrol
    · simpa [hseed] using hvtypical
  have hnext := hstop next heligible
  rw [next.stage.redNeighborhood_eq, hseed] at hnext
  exact hnext

end IndexedUniformCoreSeedStageRun

/-! ### Explicit terminal overlap rounding and quotient bookkeeping -/

namespace UniformStageOverlapBounds

/-- Canonical floor/ceiling rounding for the overlap-gap lemma.  Only the
common nonblue cap and the final strict natural-number separation remain as
inputs; every other integral parameter is fixed transparently from the real
reference and error. -/
noncomputable def ofFloorCeil
    {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} {C : ColoredGraph V} {control : Finset V}
    {reference error : ℝ}
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (nonblueCap : ℕ)
    (hbase : 0 ≤ reference / (delta k : ℝ) - error)
    (hcap : ∀ q : Fin run.length,
      (uniformStageAt run q).internalNonblueCap ≤ nonblueCap)
    (hlarge :
      4 * (⌈2 * error⌉₊ + nonblueCap + ⌈3 * error + 1⌉₊) <
        ⌊reference / (delta k : ℝ) - error⌋₊) :
    UniformStageOverlapBounds run := by
  refine {
    baseBlue := ⌊reference / (delta k : ℝ) - error⌋₊
    externalError := ⌈3 * error + 1⌉₊
    partLoss := ⌈2 * error⌉₊
    nonblueCap := nonblueCap
    baseBlue_round := Nat.floor_le hbase
    partLoss_round := Nat.le_ceil (2 * error)
    totalBlue_round := ?_
    internalNonblueCap_le := hcap
    large_round := ?_
  }
  · have hfloor : reference / (delta k : ℝ) - error <
        ((⌊reference / (delta k : ℝ) - error⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hceil : 3 * error + 1 ≤
        ((⌈3 * error + 1⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    norm_num [Nat.cast_add]
    linarith
  · omega

end UniformStageOverlapBounds

section UniformStageQuotientBookkeeping

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {k : ℕ} {C : ColoredGraph V} {control : Finset V}
variable {reference error : ℝ}

/-- The paper's ambient set `A`: the union of every partition part from
every stage in the terminal uniform run. -/
def uniformStageAmbientUnion
    (run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)) : Finset V :=
  (Finset.univ : Finset (UniformStagePartIndex run)).biUnion
    (uniformStagePart run)

/-- The paper's set `U`: the union of the final overlap-class intersections. -/
noncomputable def uniformStageFinalUnion
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) : Finset V :=
  (Finset.univ : Finset
      (Fin (overlapClassCount (uniformStageTypical run) B.overlapError))).biUnion
    (uniformStageFinalClusters B)

/-- The final-cluster label belonging to one original stage-part index. -/
noncomputable def uniformStageClassFinIndex
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (a : UniformStagePartIndex run) :
    Fin (overlapClassCount (uniformStageTypical run) B.overlapError) :=
  overlapClassEquivFin (uniformStageTypical run) B.overlapError
    (overlapClassIndexOf (uniformStageTypical run) B.overlapError a)

theorem uniformStageFinalClusters_at_classFinIndex
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (a : UniformStagePartIndex run) :
    uniformStageFinalClusters B (uniformStageClassFinIndex B a) =
      overlapClassIntersection (uniformStageTypical run) B.overlapError a := by
  exact overlapFinalClusters_at_indexOf
    (uniformStageTypical run) B.overlapError a

/-- The original stage-part index chosen as the representative of a final
overlap-quotient cluster.  Keeping this choice visible is useful when
transferring the pointwise estimates stored in that stage. -/
noncomputable def uniformStageFinalClusterSource
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    UniformStagePartIndex run :=
  overlapClassSource (uniformStageTypical run) B.overlapError
    ((overlapClassEquivFin (uniformStageTypical run) B.overlapError).symm q)

/-- A final quotient cluster is definitionally the intersection attached to
its chosen stage-part representative. -/
theorem uniformStageFinalClusters_eq_sourceIntersection
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    uniformStageFinalClusters B q =
      overlapClassIntersection (uniformStageTypical run) B.overlapError
        (uniformStageFinalClusterSource B q) := by
  rfl

/-- Relabeling the chosen representative's concrete overlap class recovers
the original final-cluster label. -/
theorem uniformStageClassFinIndex_source
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    uniformStageClassFinIndex B (uniformStageFinalClusterSource B q) = q := by
  let E := overlapClassEquivFin (uniformStageTypical run) B.overlapError
  have hindex :
      overlapClassIndexOf (uniformStageTypical run) B.overlapError
          (uniformStageFinalClusterSource B q) = E.symm q := by
    apply Subtype.ext
    exact overlapClassSource_spec (uniformStageTypical run) B.overlapError
      (E.symm q)
  change E (overlapClassIndexOf (uniformStageTypical run) B.overlapError
      (uniformStageFinalClusterSource B q)) = q
  rw [hindex, E.apply_symm_apply]

/-- Every final cluster lies in the typical set of its chosen representative. -/
theorem uniformStageFinalCluster_subset_sourceTypical
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    uniformStageFinalClusters B q ⊆
      uniformStageTypical run (uniformStageFinalClusterSource B q) := by
  rw [uniformStageFinalClusters_eq_sourceIntersection]
  exact overlapClassIntersection_subset_rep
    (uniformStageTypical run) B.overlapError
      (uniformStageFinalClusterSource B q)

/-- Every final cluster lies in the ambient part of its chosen representative. -/
theorem uniformStageFinalCluster_subset_sourcePart
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    uniformStageFinalClusters B q ⊆
      uniformStagePart run (uniformStageFinalClusterSource B q) :=
  (uniformStageFinalCluster_subset_sourceTypical B q).trans
    (uniformStageTypical_subset_part run (uniformStageFinalClusterSource B q))

/-- Every final cluster remains inside the stage-wise control set. -/
theorem uniformStageFinalCluster_subset_control
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    uniformStageFinalClusters B q ⊆ control := by
  exact (uniformStageFinalCluster_subset_sourceTypical B q).trans
    ((uniformStageAt run (uniformStageFinalClusterSource B q).1).typical_controlled
      (uniformStageFinalClusterSource B q).2)

/-- Every final cluster lies in the union of all stage parts. -/
theorem uniformStageFinalCluster_subset_ambientUnion
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    uniformStageFinalClusters B q ⊆ uniformStageAmbientUnion run := by
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨uniformStageFinalClusterSource B q, Finset.mem_univ _,
      uniformStageFinalCluster_subset_sourcePart B q hv⟩

/-- The final cluster union lies in the ambient union of all stage parts. -/
theorem uniformStageFinalUnion_subset_ambientUnion
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) :
    uniformStageFinalUnion B ⊆ uniformStageAmbientUnion run := by
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨q, _, hvq⟩
  exact uniformStageFinalCluster_subset_ambientUnion B q hvq

/-- The final cluster union lies in the common control set. -/
theorem uniformStageFinalUnion_subset_control
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) :
    uniformStageFinalUnion B ⊆ control := by
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨q, _, hvq⟩
  exact uniformStageFinalCluster_subset_control B q hvq

/-- The rounded loss from one ambient part to its typical subset. -/
theorem uniformStagePart_sdiff_typical_card_le
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (a : UniformStagePartIndex run) :
    (uniformStagePart run a \ uniformStageTypical run a).card ≤ B.partLoss := by
  have hloss := (uniformStageAt run a.1).partTypicalLoss a.2
  have hloss' :
      (((uniformStagePart run a \ uniformStageTypical run a).card : ℕ) : ℝ) ≤
        2 * error := by
    simpa [uniformStagePart, uniformStageTypical] using hloss
  have hreal :
      (((uniformStagePart run a \ uniformStageTypical run a).card : ℕ) : ℝ) ≤
        (B.partLoss : ℝ) := hloss'.trans B.partLoss_round
  exact_mod_cast hreal

/-- Intersecting an overlap class removes at most one overlap error per stage
from any representative typical set. -/
theorem uniformStageTypical_sdiff_finalCluster_card_le
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (a : UniformStagePartIndex run) :
    (uniformStageTypical run a \
        uniformStageFinalClusters B (uniformStageClassFinIndex B a)).card ≤
      run.length * B.overlapError := by
  rw [uniformStageFinalClusters_at_classFinIndex]
  have hsubset := overlapClassIntersection_subset_rep
    (uniformStageTypical run) B.overlapError a
  have hdecompose := Finset.card_sdiff_add_card_eq_card hsubset
  have hmain := overlapClass_card_le_intersection_add_error
    (W := uniformStageTypical run) (error := B.overlapError) a
  have hclass := uniformStageOverlapClass_card_le_length B a
  have hmul :
      (overlapClass (uniformStageTypical run) B.overlapError a).card *
          B.overlapError ≤ run.length * B.overlapError :=
    Nat.mul_le_mul_right B.overlapError hclass
  omega

/-- Each ambient part loses at most its typical-set loss plus the accumulated
class-intersection loss before reaching its selected final cluster. -/
theorem uniformStagePart_sdiff_finalCluster_card_le
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (a : UniformStagePartIndex run) :
    (uniformStagePart run a \
        uniformStageFinalClusters B (uniformStageClassFinIndex B a)).card ≤
      B.partLoss + run.length * B.overlapError := by
  have hsubset :
      uniformStagePart run a \
          uniformStageFinalClusters B (uniformStageClassFinIndex B a) ⊆
        (uniformStagePart run a \ uniformStageTypical run a) ∪
          (uniformStageTypical run a \
            uniformStageFinalClusters B (uniformStageClassFinIndex B a)) := by
    intro v hv
    have hvpart := (Finset.mem_sdiff.mp hv).1
    have hvfinal := (Finset.mem_sdiff.mp hv).2
    by_cases hvtypical : v ∈ uniformStageTypical run a
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hvtypical, hvfinal⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hvpart, hvtypical⟩)
  exact (Finset.card_le_card hsubset).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (uniformStagePart_sdiff_typical_card_le B a)
        (uniformStageTypical_sdiff_finalCluster_card_le B a)))

/-- The ambient part chosen for a final cluster loses only the rounded
typical-set loss and one overlap loss for each stage. -/
theorem uniformStageSourcePart_sdiff_finalCluster_card_le
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError)) :
    (uniformStagePart run (uniformStageFinalClusterSource B q) \
        uniformStageFinalClusters B q).card ≤
      B.partLoss + run.length * B.overlapError := by
  have h := uniformStagePart_sdiff_finalCluster_card_le B
    (uniformStageFinalClusterSource B q)
  rw [uniformStageClassFinIndex_source B q] at h
  exact h

/-- Restricted color degree is monotone in its restricting finite set. -/
theorem degreeIn_mono_finset (C : ColoredGraph V) (c : EdgeColor) (v : V)
    {S T : Finset V} (hST : S ⊆ T) :
    C.degreeIn c v S ≤ C.degreeIn c v T := by
  unfold ColoredGraph.degreeIn ColoredGraph.neighborFinsetIn
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hw).1, hST (Finset.mem_inter.mp hw).2⟩

/-- If every target vertex lies either in a controlled set or in an
exceptional set, its restricted degree is bounded by the controlled degree
plus the size of the exceptional set. -/
theorem degreeIn_le_degreeIn_add_card_of_subset_union
    (C : ColoredGraph V) (c : EdgeColor) (v : V)
    {T U E : Finset V} (hT : T ⊆ U ∪ E) :
    C.degreeIn c v T ≤ C.degreeIn c v U + E.card := by
  unfold ColoredGraph.degreeIn ColoredGraph.neighborFinsetIn
  let N := C.neighborFinset c v
  have hsubset : N ∩ T ⊆ (N ∩ U) ∪ E := by
    intro w hw
    rcases Finset.mem_union.mp (hT (Finset.mem_inter.mp hw).2) with hwU | hwE
    · exact Finset.mem_union_left E
        (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1, hwU⟩)
    · exact Finset.mem_union_right _ hwE
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)

/-- Pointwise Stage F6 internal-blue estimate for a final quotient cluster.
The only loss is exactly `cap + 1`: the common nonblue cap plus the excluded
self-loop. -/
theorem uniformStageFinalCluster_internalBlueDegree_lower
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError))
    {v : V} (hv : v ∈ uniformStageFinalClusters B q) :
    ((uniformStageFinalClusters B q).card : ℝ) -
        ((B.nonblueCap : ℝ) + 1) ≤
      (C.blueDegreeIn v (uniformStageFinalClusters B q) : ℝ) := by
  let a := uniformStageFinalClusterSource B q
  let S := uniformStageFinalClusters B q
  let A := uniformStagePart run a
  have hvTypical : v ∈ uniformStageTypical run a :=
    uniformStageFinalCluster_subset_sourceTypical B q hv
  have hSA : S ⊆ A := uniformStageFinalCluster_subset_sourcePart B q
  have hred : C.redDegreeIn v S ≤ C.redDegreeIn v A :=
    degreeIn_mono_finset C .red v hSA
  have hgreen : C.greenDegreeIn v S ≤ C.greenDegreeIn v A :=
    degreeIn_mono_finset C .green v hSA
  have hnonblueStage :
      C.redDegreeIn v A + C.greenDegreeIn v A ≤
        (uniformStageAt run a.1).internalNonblueCap := by
    simpa [A, a, uniformStagePart] using
      (uniformStageAt run a.1).lowInternalNonblue a.2 v hvTypical
  have hnonblue :
      C.redDegreeIn v S + C.greenDegreeIn v S ≤ B.nonblueCap :=
    (Nat.add_le_add hred hgreen).trans
      (hnonblueStage.trans (B.internalNonblueCap_le a.1))
  have hcard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨v, hv⟩
  have hcolors := C.redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_mem hv
  have hcolorsReal :
      (C.redDegreeIn v S : ℝ) + (C.greenDegreeIn v S : ℝ) +
          (C.blueDegreeIn v S : ℝ) = (S.card : ℝ) - 1 := by
    have hcast := congrArg (fun m : ℕ ↦ (m : ℝ)) hcolors
    have hcard' : 1 ≤ (uniformStageFinalClusters B q).card := by
      simpa only [S] using hcard
    rw [Nat.cast_sub hcard'] at hcast
    norm_num [Nat.cast_add] at hcast
    simpa only [S] using hcast
  have hnonblueReal :
      (C.redDegreeIn v S : ℝ) + (C.greenDegreeIn v S : ℝ) ≤
        (B.nonblueCap : ℝ) := by
    exact_mod_cast hnonblue
  dsimp only [S] at hcolorsReal hnonblueReal ⊢
  linarith

/-- Pointwise Stage F6 outside-blue estimate for a final quotient cluster.
Edges leaving its source part cost the terminal stage error; vertices lost
inside the source part cost the explicit quotient loss. -/
theorem uniformStageFinalCluster_outsideBlueDegree_le
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError))
    {v : V} (hv : v ∈ uniformStageFinalClusters B q) :
    (C.blueDegreeIn v
        (uniformStageFinalUnion B \ uniformStageFinalClusters B q) : ℝ) ≤
      error + ((B.partLoss + run.length * B.overlapError : ℕ) : ℝ) := by
  let a := uniformStageFinalClusterSource B q
  let S := uniformStageFinalClusters B q
  let A := uniformStagePart run a
  let T := uniformStageFinalUnion B \ S
  have hvTypical : v ∈ uniformStageTypical run a :=
    uniformStageFinalCluster_subset_sourceTypical B q hv
  have htarget : T ⊆ Aᶜ ∪ (A \ S) := by
    intro w hw
    by_cases hwA : w ∈ A
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hwA, (Finset.mem_sdiff.mp hw).2⟩)
    · exact Finset.mem_union_left _ (by simpa using hwA)
  have hdegreeNat :
      C.blueDegreeIn v T ≤ C.blueDegreeIn v Aᶜ + (A \ S).card :=
    degreeIn_le_degreeIn_add_card_of_subset_union C .blue v htarget
  have hdegree :
      (C.blueDegreeIn v T : ℝ) ≤
        (C.blueDegreeIn v Aᶜ : ℝ) + ((A \ S).card : ℝ) := by
    exact_mod_cast hdegreeNat
  have hexternal : (C.blueDegreeIn v Aᶜ : ℝ) ≤ error := by
    simpa [A, a, uniformStagePart] using
      (uniformStageAt run a.1).lowExternalBlue a.2 v hvTypical
  have hlossNat : (A \ S).card ≤
      B.partLoss + run.length * B.overlapError := by
    simpa [A, S, a] using
      uniformStageSourcePart_sdiff_finalCluster_card_le B q
  have hloss : ((A \ S).card : ℝ) ≤
      ((B.partLoss + run.length * B.overlapError : ℕ) : ℝ) := by
    exact_mod_cast hlossNat
  dsimp only [T] at hdegree ⊢
  linarith

/-- Any pointwise property known on the common control set is inherited by
vertices of every final quotient cluster. -/
theorem uniformStageFinalCluster_inherits_control
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) {P : V → Prop}
    (hcontrol : ∀ v ∈ control, P v)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError))
    {v : V} (hv : v ∈ uniformStageFinalClusters B q) : P v :=
  hcontrol v (uniformStageFinalCluster_subset_control B q hv)

/-- In particular, pointwise restricted weighted-degree control on the
control set transfers verbatim to each final quotient cluster. -/
theorem uniformStageFinalCluster_weightedDegree_le
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (weightedError : ℝ)
    (hweighted : ∀ v ∈ control,
      |(weightedDegreeIn k C v (uniformStageFinalUnion B) : ℝ)| ≤
        weightedError)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError))
    {v : V} (hv : v ∈ uniformStageFinalClusters B q) :
    |(weightedDegreeIn k C v (uniformStageFinalUnion B) : ℝ)| ≤
      weightedError :=
  uniformStageFinalCluster_inherits_control B hweighted q hv

/-! ### Generic exact bridges from quotient estimates -/

/-- Pointwise outside-blue control gives a between-cluster blue-density
bound once the target cluster is large enough to absorb the outside error.
The pairwise-disjointness hypothesis is used only to place `clusters j`
inside `clusterUnion clusters \ clusters i`. -/
theorem blueColorDensity_le_of_outsideDegree_and_denominator
    {I : Type*} [Fintype I] [DecidableEq I]
    (C : ColoredGraph V) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    {i j : I} (hij : i ≠ j)
    (hi : (clusters i).Nonempty) (hj : (clusters j).Nonempty)
    (outsideError beta : ℝ)
    (houtside : ∀ v ∈ clusters i,
      (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
        outsideError)
    (hdenominator :
      outsideError ≤ beta * ((clusters j).card : ℝ)) :
    C.colorDensity .blue (clusters i) (clusters j) ≤ beta := by
  have hijDisjoint : Disjoint (clusters i) (clusters j) :=
    hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  have hjSubset : clusters j ⊆ clusterUnion clusters \ clusters i := by
    intro w hwj
    refine Finset.mem_sdiff.mpr
      ⟨cluster_subset_clusterUnion clusters j hwj, ?_⟩
    intro hwi
    exact Finset.disjoint_left.mp hijDisjoint hwi hwj
  have hpoint : ∀ v ∈ clusters i,
      (C.blueDegreeIn v (clusters j) : ℝ) ≤
        beta * ((clusters j).card : ℝ) := by
    intro v hv
    have hmonoNat := degreeIn_mono_finset C .blue v hjSubset
    have hmono : (C.blueDegreeIn v (clusters j) : ℝ) ≤
        (C.blueDegreeIn v
          (clusterUnion clusters \ clusters i) : ℝ) := by
      exact_mod_cast hmonoNat
    exact hmono.trans ((houtside v hv).trans hdenominator)
  have hcount :
      (C.colorEdgeCountBetween .blue (clusters i) (clusters j) : ℝ) ≤
        ((clusters i).card : ℝ) *
          (beta * ((clusters j).card : ℝ)) := by
    calc
      (C.colorEdgeCountBetween .blue (clusters i) (clusters j) : ℝ) =
          ∑ v ∈ clusters i, (C.blueDegreeIn v (clusters j) : ℝ) := by
        symm
        exact_mod_cast C.sum_degreeIn_eq_colorEdgeCountBetween
          .blue (clusters i) (clusters j)
      _ ≤ ∑ _v ∈ clusters i,
          beta * ((clusters j).card : ℝ) :=
        Finset.sum_le_sum fun v hv ↦ hpoint v hv
      _ = ((clusters i).card : ℝ) *
          (beta * ((clusters j).card : ℝ)) := by simp
  have hiCard : 0 < ((clusters i).card : ℝ) := by
    exact_mod_cast hi.card_pos
  have hjCard : 0 < ((clusters j).card : ℝ) := by
    exact_mod_cast hj.card_pos
  unfold colorDensity
  rw [div_le_iff₀ (mul_pos hiCard hjCard)]
  calc
    (C.colorEdgeCountBetween .blue (clusters i) (clusters j) : ℝ) ≤
        ((clusters i).card : ℝ) *
          (beta * ((clusters j).card : ℝ)) := hcount
    _ = beta *
        (((clusters i).card : ℝ) * ((clusters j).card : ℝ)) := by ring

/-- Exact natural-number handshake bound supplied by a pointwise internal
nonblue cap.  Keeping the factor `2` avoids any rounding loss. -/
theorem two_mul_redEdgeCountIn_le_card_mul_of_internalNonblueCap
    (C : ColoredGraph V) (S : Finset V) (cap : ℕ)
    (hcap : ∀ v ∈ S,
      C.redDegreeIn v S + C.greenDegreeIn v S ≤ cap) :
    2 * C.redEdgeCountIn S ≤ S.card * cap := by
  have hred : ∀ v ∈ S, C.redDegreeIn v S ≤ cap := by
    intro v hv
    have := hcap v hv
    omega
  calc
    2 * C.redEdgeCountIn S = ∑ v ∈ S, C.redDegreeIn v S := by
      exact (C.sum_degreeIn_eq_two_mul_edgeCountIn .red S).symm
    _ ≤ ∑ _v ∈ S, cap := Finset.sum_le_sum fun v hv ↦ hred v hv
    _ = S.card * cap := by simp

/-- Real-valued form of
`two_mul_redEdgeCountIn_le_card_mul_of_internalNonblueCap`, matching the
internal-red error field of the final-cluster certificate. -/
theorem redEdgeCountIn_le_card_mul_internalNonblueCap_div_two
    (C : ColoredGraph V) (S : Finset V) (cap : ℕ)
    (hcap : ∀ v ∈ S,
      C.redDegreeIn v S + C.greenDegreeIn v S ≤ cap) :
    (C.redEdgeCountIn S : ℝ) ≤
      ((S.card : ℝ) * (cap : ℝ)) / 2 := by
  have hnat :=
    two_mul_redEdgeCountIn_le_card_mul_of_internalNonblueCap C S cap hcap
  have hreal :
      (2 : ℝ) * (C.redEdgeCountIn S : ℝ) ≤
        (S.card : ℝ) * (cap : ℝ) := by
    exact_mod_cast hnat
  linarith

/-- Restricting a weighted degree costs at most the absolute full weighted
degree plus the red and `Δ`-weighted blue degrees into the complement. -/
theorem abs_weightedDegreeIn_le_abs_weightedDegree_add_complDegrees
    (k : ℕ) (C : ColoredGraph V) (v : V) (U : Finset V) :
    |(weightedDegreeIn k C v U : ℝ)| ≤
      |(weightedDegree k C v : ℝ)| +
        ((C.redDegreeIn v Uᶜ : ℝ) +
          (delta k : ℝ) * (C.blueDegreeIn v Uᶜ : ℝ)) := by
  have hdecompZ := weightedDegreeIn_add_compl k C v U
  have hdecomp := congrArg (fun z : ℤ ↦ (z : ℝ)) hdecompZ
  push_cast at hdecomp
  have hin : (weightedDegreeIn k C v U : ℝ) =
      (weightedDegree k C v : ℝ) -
        (weightedDegreeIn k C v Uᶜ : ℝ) := by
    linarith
  have hcomplForm : (weightedDegreeIn k C v Uᶜ : ℝ) =
      (C.redDegreeIn v Uᶜ : ℝ) -
        (delta k : ℝ) * (C.blueDegreeIn v Uᶜ : ℝ) := by
    simp [weightedDegreeIn]
  have hcompl : |(weightedDegreeIn k C v Uᶜ : ℝ)| ≤
      (C.redDegreeIn v Uᶜ : ℝ) +
        (delta k : ℝ) * (C.blueDegreeIn v Uᶜ : ℝ) := by
    rw [hcomplForm]
    calc
      |(C.redDegreeIn v Uᶜ : ℝ) -
          (delta k : ℝ) * (C.blueDegreeIn v Uᶜ : ℝ)| ≤
          |(C.redDegreeIn v Uᶜ : ℝ)| +
            |(delta k : ℝ) * (C.blueDegreeIn v Uᶜ : ℝ)| :=
        abs_sub _ _
      _ = (C.redDegreeIn v Uᶜ : ℝ) +
          (delta k : ℝ) * (C.blueDegreeIn v Uᶜ : ℝ) := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  rw [hin]
  calc
    |(weightedDegree k C v : ℝ) -
        (weightedDegreeIn k C v Uᶜ : ℝ)| ≤
        |(weightedDegree k C v : ℝ)| +
          |(weightedDegreeIn k C v Uᶜ : ℝ)| := abs_sub _ _
    _ ≤ |(weightedDegree k C v : ℝ)| +
        ((C.redDegreeIn v Uᶜ : ℝ) +
          (delta k : ℝ) * (C.blueDegreeIn v Uᶜ : ℝ)) := by
      gcongr

/-- A final cluster inherits any common upper bound on the internal
nonblue cap of the erased stages.  Unlike the rounded overlap bound, this
form lets the caller retain the sharper cap exported by the indexed run. -/
theorem uniformStageFinalCluster_internalNonblue_le_of_cap
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (cap : ℕ)
    (hcap : ∀ q : Fin run.length,
      (uniformStageAt run q).internalNonblueCap ≤ cap)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError))
    {v : V} (hv : v ∈ uniformStageFinalClusters B q) :
    C.redDegreeIn v (uniformStageFinalClusters B q) +
        C.greenDegreeIn v (uniformStageFinalClusters B q) ≤ cap := by
  let a := uniformStageFinalClusterSource B q
  let S := uniformStageFinalClusters B q
  let A := uniformStagePart run a
  have hvTypical : v ∈ uniformStageTypical run a :=
    uniformStageFinalCluster_subset_sourceTypical B q hv
  have hSA : S ⊆ A := uniformStageFinalCluster_subset_sourcePart B q
  have hred : C.redDegreeIn v S ≤ C.redDegreeIn v A :=
    degreeIn_mono_finset C .red v hSA
  have hgreen : C.greenDegreeIn v S ≤ C.greenDegreeIn v A :=
    degreeIn_mono_finset C .green v hSA
  have hstage : C.redDegreeIn v A + C.greenDegreeIn v A ≤
      (uniformStageAt run a.1).internalNonblueCap := by
    simpa [A, a, uniformStagePart] using
      (uniformStageAt run a.1).lowInternalNonblue a.2 v hvTypical
  exact (Nat.add_le_add hred hgreen).trans (hstage.trans (hcap a.1))

/-- The exact `cap + 1` internal-blue lower bound using a caller-supplied
common cap for the erased stages. -/
theorem uniformStageFinalCluster_internalBlueDegree_lower_of_cap
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (cap : ℕ)
    (hcap : ∀ q : Fin run.length,
      (uniformStageAt run q).internalNonblueCap ≤ cap)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError))
    {v : V} (hv : v ∈ uniformStageFinalClusters B q) :
    ((uniformStageFinalClusters B q).card : ℝ) - ((cap : ℝ) + 1) ≤
      (C.blueDegreeIn v (uniformStageFinalClusters B q) : ℝ) := by
  let S := uniformStageFinalClusters B q
  have hnonblue :=
    uniformStageFinalCluster_internalNonblue_le_of_cap B cap hcap q hv
  have hcard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨v, hv⟩
  have hcolors := C.redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_mem hv
  have hcolorsReal :
      (C.redDegreeIn v S : ℝ) + (C.greenDegreeIn v S : ℝ) +
          (C.blueDegreeIn v S : ℝ) = (S.card : ℝ) - 1 := by
    have hcast := congrArg (fun m : ℕ ↦ (m : ℝ)) hcolors
    have hcard' : 1 ≤ (uniformStageFinalClusters B q).card := by
      simpa only [S] using hcard
    rw [Nat.cast_sub hcard'] at hcast
    norm_num [Nat.cast_add] at hcast
    simpa only [S] using hcast
  have hnonblueReal :
      (C.redDegreeIn v S : ℝ) + (C.greenDegreeIn v S : ℝ) ≤
        (cap : ℝ) := by
    exact_mod_cast hnonblue
  dsimp only [S] at hcolorsReal hnonblueReal ⊢
  linarith

/-- Total-blue control from the representative stage, the exact internal
`cap + 1` bound, and a lower size estimate control all blue neighbors outside
the final cluster. -/
theorem uniformStageFinalCluster_complBlueDegree_le_of_cap_and_balance
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (cap : ℕ)
    (hcap : ∀ q : Fin run.length,
      (uniformStageAt run q).internalNonblueCap ≤ cap)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError))
    (sizeError : ℝ)
    (hsize : reference / (delta k : ℝ) - sizeError ≤
      ((uniformStageFinalClusters B q).card : ℝ))
    {v : V} (hv : v ∈ uniformStageFinalClusters B q) :
    (C.blueDegreeIn v (uniformStageFinalClusters B q)ᶜ : ℝ) ≤
      sizeError + ((cap : ℝ) + 1) + 2 * error := by
  let a := uniformStageFinalClusterSource B q
  have hvTypical : v ∈ uniformStageTypical run a :=
    uniformStageFinalCluster_subset_sourceTypical B q hv
  have htotal : (C.blueDegree v : ℝ) ≤
      reference / (delta k : ℝ) + 2 * error := by
    simpa [a] using
      (uniformStageAt run a.1).totalBlueUpper a.2 v hvTypical
  have hinternal :=
    uniformStageFinalCluster_internalBlueDegree_lower_of_cap B cap hcap q hv
  have hsplitNat := C.degreeIn_add_degreeIn_compl .blue v
    (uniformStageFinalClusters B q)
  have hsplit :
      (C.blueDegreeIn v (uniformStageFinalClusters B q) : ℝ) +
          (C.blueDegreeIn v (uniformStageFinalClusters B q)ᶜ : ℝ) =
        (C.blueDegree v : ℝ) := by
    exact_mod_cast hsplitNat
  linarith

/-- The complement of the entire final union is contained in the complement
of each final cluster, so it satisfies the same cap-and-balance blue bound. -/
theorem uniformStageFinalUnion_compl_blueDegree_le_of_cap_and_balance
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (cap : ℕ)
    (hcap : ∀ q : Fin run.length,
      (uniformStageAt run q).internalNonblueCap ≤ cap)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError))
    (sizeError : ℝ)
    (hsize : reference / (delta k : ℝ) - sizeError ≤
      ((uniformStageFinalClusters B q).card : ℝ))
    {v : V} (hv : v ∈ uniformStageFinalClusters B q) :
    (C.blueDegreeIn v (uniformStageFinalUnion B)ᶜ : ℝ) ≤
      sizeError + ((cap : ℝ) + 1) + 2 * error := by
  have hsubset : (uniformStageFinalUnion B)ᶜ ⊆
      (uniformStageFinalClusters B q)ᶜ := by
    intro w hw
    simp only [Finset.mem_compl] at hw ⊢
    intro hwq
    apply hw
    exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, hwq⟩
  have hmonoNat := degreeIn_mono_finset C .blue v hsubset
  have hmono : (C.blueDegreeIn v (uniformStageFinalUnion B)ᶜ : ℝ) ≤
      (C.blueDegreeIn v (uniformStageFinalClusters B q)ᶜ : ℝ) := by
    exact_mod_cast hmonoNat
  exact hmono.trans
    (uniformStageFinalCluster_complBlueDegree_le_of_cap_and_balance
      B cap hcap q sizeError hsize hv)

/-- Blue degree from one final cluster into all other final clusters obeys
the same cap-and-balance bound. -/
theorem uniformStageFinalCluster_outsideBlueDegree_le_of_cap_and_balance
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (cap : ℕ)
    (hcap : ∀ q : Fin run.length,
      (uniformStageAt run q).internalNonblueCap ≤ cap)
    (q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError))
    (sizeError : ℝ)
    (hsize : reference / (delta k : ℝ) - sizeError ≤
      ((uniformStageFinalClusters B q).card : ℝ))
    {v : V} (hv : v ∈ uniformStageFinalClusters B q) :
    (C.blueDegreeIn v
        (uniformStageFinalUnion B \ uniformStageFinalClusters B q) : ℝ) ≤
      sizeError + ((cap : ℝ) + 1) + 2 * error := by
  have hsubset : uniformStageFinalUnion B \ uniformStageFinalClusters B q ⊆
      (uniformStageFinalClusters B q)ᶜ := by
    intro w hw
    simpa using (Finset.mem_sdiff.mp hw).2
  have hmonoNat := degreeIn_mono_finset C .blue v hsubset
  have hmono :
      (C.blueDegreeIn v
          (uniformStageFinalUnion B \ uniformStageFinalClusters B q) : ℝ) ≤
        (C.blueDegreeIn v (uniformStageFinalClusters B q)ᶜ : ℝ) := by
    exact_mod_cast hmonoNat
  exact hmono.trans
    (uniformStageFinalCluster_complBlueDegree_le_of_cap_and_balance
      B cap hcap q sizeError hsize hv)

/-- The selected final cluster is one of the terms in the final union. -/
theorem uniformStageFinalCluster_subset_finalUnion
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (a : UniformStagePartIndex run) :
    uniformStageFinalClusters B (uniformStageClassFinIndex B a) ⊆
      uniformStageFinalUnion B := by
  intro v hv
  exact Finset.mem_biUnion.mpr
    ⟨uniformStageClassFinIndex B a, Finset.mem_univ _, hv⟩

/-- Exact finite union-bound analogue of the paper's estimate on `|A \ U|`. -/
theorem uniformStageAmbient_sdiff_finalUnion_card_le
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) :
    (uniformStageAmbientUnion run \ uniformStageFinalUnion B).card ≤
      (run.length * delta k) *
        (B.partLoss + run.length * B.overlapError) := by
  let loss := B.partLoss + run.length * B.overlapError
  have hpiece : ∀ a : UniformStagePartIndex run,
      (uniformStagePart run a \ uniformStageFinalUnion B).card ≤ loss := by
    intro a
    have hsubset :
        uniformStagePart run a \ uniformStageFinalUnion B ⊆
          uniformStagePart run a \
            uniformStageFinalClusters B (uniformStageClassFinIndex B a) := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1,
        fun hvcluster ↦ (Finset.mem_sdiff.mp hv).2
          (uniformStageFinalCluster_subset_finalUnion B a hvcluster)⟩
    exact (Finset.card_le_card hsubset).trans
      (uniformStagePart_sdiff_finalCluster_card_le B a)
  have hsubset : uniformStageAmbientUnion run \ uniformStageFinalUnion B ⊆
      (Finset.univ : Finset (UniformStagePartIndex run)).biUnion
        (fun a ↦ uniformStagePart run a \ uniformStageFinalUnion B) := by
    intro v hv
    rcases Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hv).1 with ⟨a, ha, hva⟩
    exact Finset.mem_biUnion.mpr
      ⟨a, ha, Finset.mem_sdiff.mpr ⟨hva, (Finset.mem_sdiff.mp hv).2⟩⟩
  calc
    (uniformStageAmbientUnion run \ uniformStageFinalUnion B).card ≤
        ((Finset.univ : Finset (UniformStagePartIndex run)).biUnion
          (fun a ↦ uniformStagePart run a \ uniformStageFinalUnion B)).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset (UniformStagePartIndex run)).card * loss :=
      Finset.card_biUnion_le_card_mul _ _ loss (fun a _ ↦ hpiece a)
    _ = (run.length * delta k) *
        (B.partLoss + run.length * B.overlapError) := by
      simp [loss]

/-- The exact natural threshold which forces a stage to contribute a typical
part outside all earlier overlap classes. -/
def uniformStageNewClassThreshold
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) : ℕ :=
  delta k * (B.overlapError + B.partLoss)

/-- Concrete new-class creation for one position of a uniform run.  The
earlier index set and its covered vertex set are explicit, so this statement
can be instantiated either with list prefixes or with a separately maintained
set of discovered indices. -/
theorem uniformStage_exists_newOverlapClass_of_newMass
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (q : Fin run.length)
    (old : Finset (UniformStagePartIndex run)) (covered : Finset V)
    (newMass : ℕ)
    (hold : ∀ j ∈ old, uniformStageTypical run j ⊆ covered)
    (hnew : newMass ≤
      ((uniformStageAt run q).redNeighborhood \ covered).card)
    (hmass : uniformStageNewClassThreshold B < newMass) :
    ∃ i : Fin (delta k), ∀ j ∈ old,
      overlapClass (uniformStageTypical run) B.overlapError (q, i) ≠
        overlapClass (uniformStageTypical run) B.overlapError j := by
  apply exists_new_overlapClass_of_newNeighborhoodMass
    (uniformStageTypical run) old (uniformStageAt run q)
    (fun i ↦ (q, i)) covered B.overlapError B.partLoss newMass
  · intro i
    rfl
  · exact hold
  · intro i
    exact uniformStagePart_sdiff_typical_card_le B (q, i)
  · exact hnew
  · exact hmass

/-- All reusable output of the overlap quotient, including the exact `A \ U`
loss and the input-output form of the new-class argument. -/
structure UniformStageQuotientCertificate
    (run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error))
    (B : UniformStageOverlapBounds run) : Prop where
  pairwiseDisjoint :
    Set.PairwiseDisjoint
      (Set.univ : Set
        (Fin (overlapClassCount (uniformStageTypical run) B.overlapError)))
      (uniformStageFinalClusters B)
  classCount_pos :
    0 < overlapClassCount (uniformStageTypical run) B.overlapError
  ambientOutsideFinal :
    (uniformStageAmbientUnion run \ uniformStageFinalUnion B).card ≤
      (run.length * delta k) *
        (B.partLoss + run.length * B.overlapError)
  clusterLower : ∀
      q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError),
    B.baseBlue - run.length * B.overlapError ≤
      (uniformStageFinalClusters B q).card
  clusterBalanced : ∀
      q : Fin (overlapClassCount (uniformStageTypical run) B.overlapError),
    |((uniformStageFinalClusters B q).card : ℝ) -
        reference / (delta k : ℝ)| ≤
      error + ((run.length * B.overlapError : ℕ) : ℝ)
  newClass_of_mass : ∀
      (q : Fin run.length)
      (old : Finset (UniformStagePartIndex run))
      (covered : Finset V) (newMass : ℕ),
    (∀ j ∈ old, uniformStageTypical run j ⊆ covered) →
    newMass ≤ ((uniformStageAt run q).redNeighborhood \ covered).card →
    uniformStageNewClassThreshold B < newMass →
    ∃ i : Fin (delta k), ∀ j ∈ old,
      overlapClass (uniformStageTypical run) B.overlapError (q, i) ≠
        overlapClass (uniformStageTypical run) B.overlapError j

/-- Assemble the quotient certificate from the overlap bounds. -/
theorem uniformStageQuotientCertificate_of_bounds
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (hk : 3 ≤ k) (hrun : run ≠ []) :
    UniformStageQuotientCertificate run B where
  pairwiseDisjoint := uniformStageFinalClusters_pairwiseDisjoint B
  classCount_pos := uniformStageOverlapClassCount_pos B hk hrun
  ambientOutsideFinal := uniformStageAmbient_sdiff_finalUnion_card_le B
  clusterLower := uniformStageFinalClusters_card_lower B
  clusterBalanced := uniformStageFinalClusters_balanced B
  newClass_of_mass := fun q old covered newMass hold hnew hmass ↦
    uniformStage_exists_newOverlapClass_of_newMass B q old covered newMass
      hold hnew hmass

/-- The different parts of one fixed stage belong to different overlap
classes. -/
theorem uniformStageOverlapClass_ne_of_sameStage
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (q : Fin run.length)
    {i j : Fin (delta k)} (hij : i ≠ j) :
    overlapClass (uniformStageTypical run) B.overlapError (q, i) ≠
      overlapClass (uniformStageTypical run) B.overlapError (q, j) := by
  intro hclasses
  have hclose : overlapClose (uniformStageTypical run) B.overlapError
      (q, i) (q, j) := overlapClose_of_overlapClass_eq hclasses
  have hindex : (q, i) ≠ (q, j) := by
    intro h
    apply hij
    exact congrArg Prod.snd h
  have hdisjoint : Disjoint (uniformStageTypical run (q, i))
      (uniformStageTypical run (q, j)) :=
    uniformStageTypical_sameStage_disjoint run (q, i) (q, j) hindex rfl
  have hsubset : uniformStageTypical run (q, i) ⊆
      (uniformStageTypical run (q, i) \ uniformStageTypical run (q, j)) ∪
        (uniformStageTypical run (q, j) \ uniformStageTypical run (q, i)) := by
    intro v hvi
    have hvj : v ∉ uniformStageTypical run (q, j) := by
      intro hvj
      exact Finset.disjoint_left.mp hdisjoint hvi hvj
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvi, hvj⟩)
  have hcard : (uniformStageTypical run (q, i)).card ≤ B.overlapError :=
    (Finset.card_le_card hsubset).trans hclose
  have hlarge := B.typical_large (q, i)
  omega

/-- Inject the `delta k` parts of one fixed stage into the concrete overlap
class type. -/
noncomputable def uniformStageFixedStageClassEmbedding
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (q : Fin run.length) :
    Fin (delta k) ↪
      OverlapClassIndex (uniformStageTypical run) B.overlapError where
  toFun i := overlapClassIndexOf (uniformStageTypical run) B.overlapError (q, i)
  inj' := by
    intro i j h
    by_contra hij
    apply uniformStageOverlapClass_ne_of_sameStage B q hij
    exact congrArg Subtype.val h

/-- The same fixed-stage injection after relabeling overlap classes by
`Fin`. -/
noncomputable def uniformStageFixedStageClassFinEmbedding
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (q : Fin run.length) :
    Fin (delta k) ↪
      Fin (overlapClassCount (uniformStageTypical run) B.overlapError) :=
  (uniformStageFixedStageClassEmbedding B q).trans
    (overlapClassEquivFin (uniformStageTypical run) B.overlapError).toEmbedding

/-- Every fixed stage already supplies at least `delta k` distinct final
overlap classes. -/
theorem delta_le_uniformStageOverlapClassCount
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (q : Fin run.length) :
    delta k ≤ overlapClassCount (uniformStageTypical run) B.overlapError := by
  change delta k ≤ Fintype.card
    (OverlapClassIndex (uniformStageTypical run) B.overlapError)
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective
      (uniformStageFixedStageClassEmbedding B q)
      (uniformStageFixedStageClassEmbedding B q).injective

/-- One class outside all parts of a fixed stage upgrades the class-count
bound from `delta k` to `delta k + 1`. -/
theorem delta_add_one_le_uniformStageOverlapClassCount_of_newClass
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) (q : Fin run.length)
    (a : UniformStagePartIndex run)
    (hnew : ∀ i : Fin (delta k),
      overlapClass (uniformStageTypical run) B.overlapError a ≠
        overlapClass (uniformStageTypical run) B.overlapError (q, i)) :
    delta k + 1 ≤
      overlapClassCount (uniformStageTypical run) B.overlapError := by
  let fixed := uniformStageFixedStageClassEmbedding B q
  let extra := overlapClassIndexOf (uniformStageTypical run) B.overlapError a
  let f : Fin (delta k) ⊕ Unit →
      OverlapClassIndex (uniformStageTypical run) B.overlapError
    | Sum.inl i => fixed i
    | Sum.inr _ => extra
  have hf : Function.Injective f := by
    intro x y hxy
    rcases x with i | u <;> rcases y with j | v
    · apply congrArg Sum.inl
      apply fixed.injective
      exact hxy
    · exfalso
      have hclasses := congrArg Subtype.val hxy
      exact hnew i hclasses.symm
    · exfalso
      have hclasses := congrArg Subtype.val hxy
      exact hnew j hclasses
    · exact congrArg Sum.inr (Subsingleton.elim u v)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [f, overlapClassCount] using hcard

end UniformStageQuotientBookkeeping

/-! ## Stages F9--F11: assembling the extracted core

The recursive construction proves the geometric fields below, while the
last objective argument only needs three quantitative inputs: a one-`ζ`
near-extremality loss, the one-`ζ` boundary estimate, and absorption of the
linear Mantel bound into one further `ζ n²`.  Keeping these inputs separate
makes the exact `δ + 3ζ` loss explicit.
-/

/-- The complete pre-output certificate for Stages F9--F11 of core
extraction.

All geometric conclusions are already stated for the original coloring
`C`.  The last three fields are precisely the inputs to the exact objective
decomposition over the full core and its complement.  In particular,
`coreMantelAbsorbed` does not assume a new extremal estimate: its left-hand
side is the integer bound supplied by `objectiveIn_le_kthOrderMantel` and is
absorbed by the eventual large-`n` threshold. -/
structure CoreExtractionAssemblyCertificate
    (k n : ℕ) (C : ColoredGraph (Fin n)) (η δ ζ c : ℝ) where
  clusterCount : ℕ
  clusterCount_ge : k - 1 ≤ clusterCount
  exceptional : Finset (Fin n)
  clusters : Fin clusterCount → Finset (Fin n)
  clusters_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin clusterCount)) clusters
  exceptional_disjoint_clusters : ∀ i, Disjoint exceptional (clusters i)
  reducedGraph : SimpleGraph (Fin clusterCount)
  reducedGraphAdjDecidable : DecidableRel reducedGraph.Adj
  reducedGraph_regular :
    letI := reducedGraphAdjDecidable
    ∀ i, reducedGraph.degree i = delta k
  blueDense : ∀ i,
    (1 - ζ) * (Nat.choose (clusters i).card 2 : ℝ) ≤
      (C.blueEdgeCountIn (clusters i) : ℝ)
  clusterLowerBound : ∀ i,
    c * (n : ℝ) ≤ ((clusters i).card : ℝ)
  clusterBalanced : ∀ i j,
    |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| ≤
      ζ * (n : ℝ)
  exceptionalSmall : (exceptional.card : ℝ) ≤ ζ * (n : ℝ)
  clusterUnionLarge :
    (η - 3 * ζ) * (n : ℝ) ≤
      ((coreExtractionClusterUnion clusters).card : ℝ)
  redDenseOnEdges : ∀ i j,
    reducedGraph.Adj i j →
      1 - ζ ≤ C.colorDensity .red (clusters i) (clusters j)
  greenDenseOnNonedges : ∀ i j,
    i ≠ j → ¬ reducedGraph.Adj i j →
      1 - ζ ≤ C.colorDensity .green (clusters i) (clusters j)
  boundarySmall :
    (C.colorEdgeCountBetween .red
          (coreExtractionCore exceptional clusters)
          (coreExtractionRemainder exceptional clusters) : ℝ) +
        (C.colorEdgeCountBetween .blue
          (coreExtractionCore exceptional clusters)
          (coreExtractionRemainder exceptional clusters) : ℝ) ≤
      ζ * (n : ℝ) ^ 2
  coloring_mem_Ck : C ∈ Ck k n
  wholeNearExtremal :
    -((δ + ζ) * (n : ℝ) ^ 2) ≤ (objective k C : ℝ)
  coreMantelAbsorbed :
    (((delta k *
        (coreExtractionCore exceptional clusters).card / 2 : ℕ) : ℝ)) ≤
      ζ * (n : ℝ) ^ 2

/-! ### F9--F10 terminal geometry -/

/-- The transparent terminal data needed to assemble the raw core-extraction
output.

Here `retained` is the paper's `\widetilde X`, `covered` is the union `A` of
the red neighborhoods selected by the recursion, and `finalUnion` is the
union `U` of the final quotient clusters.  Cluster color data are deliberately
stated for `C.greenOutside retained`, the coloring used during the recursion;
the converter below transfers them back to `C` on subsets of `retained`.

The three error coefficients separately expose the losses from
`retainedᶜ`, `covered \ finalUnion`, and the pointwise boundary from
`finalUnion` to `retained \ covered`.  Their single budget inequality is
exactly what is needed for both the exceptional-set and boundary conclusions.
Thus none of the six paper-facing conclusions is hidden in this certificate.
-/
structure CoreExtractionTerminalGeometryCertificate
    (k n : ℕ) (C : ColoredGraph (Fin n)) (η δ ζ c : ℝ) where
  retained : Finset (Fin n)
  covered : Finset (Fin n)
  finalUnion : Finset (Fin n)
  clusterCount : ℕ
  clusterCount_ge : k - 1 ≤ clusterCount
  clusters : Fin clusterCount → Finset (Fin n)
  clusters_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin clusterCount)) clusters
  clusterUnion_eq : coreExtractionClusterUnion clusters = finalUnion
  finalUnion_subset_covered : finalUnion ⊆ covered
  covered_subset_retained : covered ⊆ retained
  reducedGraph : SimpleGraph (Fin clusterCount)
  reducedGraphAdjDecidable : DecidableRel reducedGraph.Adj
  reducedGraph_regular :
    letI := reducedGraphAdjDecidable
    ∀ i, reducedGraph.degree i = delta k
  /-- The pointwise form whose handshake consequence is output (i). -/
  cleanedBlueDegree : ∀ i v, v ∈ clusters i →
    (1 - ζ) * (((clusters i).card : ℝ) - 1) ≤
      ((C.greenOutside retained).blueDegreeIn v (clusters i) : ℝ)
  clusterLowerBound : ∀ i,
    c * (n : ℝ) ≤ ((clusters i).card : ℝ)
  clusterBalanced : ∀ i j,
    |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| ≤
      ζ * (n : ℝ)
  finalUnionLarge :
    (η - 3 * ζ) * (n : ℝ) ≤ (finalUnion.card : ℝ)
  cleanedRedDenseOnEdges : ∀ i j,
    reducedGraph.Adj i j →
      1 - ζ ≤
        (C.greenOutside retained).colorDensity .red (clusters i) (clusters j)
  cleanedGreenDenseOnNonedges : ∀ i j,
    i ≠ j → ¬ reducedGraph.Adj i j →
      1 - ζ ≤
        (C.greenOutside retained).colorDensity .green (clusters i) (clusters j)
  retainedError : ℝ
  uncoveredError : ℝ
  boundaryError : ℝ
  retainedError_nonneg : 0 ≤ retainedError
  uncoveredError_nonneg : 0 ≤ uncoveredError
  boundaryError_nonneg : 0 ≤ boundaryError
  errorBudget : retainedError + uncoveredError + boundaryError ≤ ζ
  retainedComplementSmall :
    (retainedᶜ.card : ℝ) ≤ retainedError * (n : ℝ)
  uncoveredSmall :
    ((covered \ finalUnion).card : ℝ) ≤ uncoveredError * (n : ℝ)
  cleanedBoundaryPointwise : ∀ v ∈ finalUnion,
    ((C.greenOutside retained).redDegreeIn v (retained \ covered) : ℝ) +
        ((C.greenOutside retained).blueDegreeIn v (retained \ covered) : ℝ) ≤
      boundaryError * (n : ℝ)
  coloring_mem_Ck : C ∈ Ck k n
  wholeNearExtremal :
    -((δ + ζ) * (n : ℝ) ^ 2) ≤ (objective k C : ℝ)
  /-- The eventual large-`n` absorption, stated on the transparent core
  identity `retainedᶜ ∪ covered`. -/
  coreMantelAbsorbed :
    (((delta k * (retainedᶜ ∪ covered).card / 2 : ℕ) : ℝ)) ≤
      ζ * (n : ℝ) ^ 2

namespace CoreExtractionTerminalGeometryCertificate

/-- Every final cluster lies in the explicitly named union `U`. -/
theorem cluster_subset_finalUnion
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ c : ℝ}
    (A : CoreExtractionTerminalGeometryCertificate k n C η δ ζ c)
    (i : Fin A.clusterCount) : A.clusters i ⊆ A.finalUnion := by
  rw [← A.clusterUnion_eq]
  exact cluster_subset_clusterUnion A.clusters i

/-- Every final cluster lies in the retained set, so cleaning-to-original
color transfers apply to all its internal and between-cluster data. -/
theorem cluster_subset_retained
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ c : ℝ}
    (A : CoreExtractionTerminalGeometryCertificate k n C η δ ζ c)
    (i : Fin A.clusterCount) : A.clusters i ⊆ A.retained :=
  (A.cluster_subset_finalUnion i).trans
    (A.finalUnion_subset_covered.trans A.covered_subset_retained)

/-- The output exceptional set is literally
`U₀ = retainedᶜ ∪ (covered \ finalUnion)`. -/
@[simp]
theorem outputExceptional_eq
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ c : ℝ}
    (A : CoreExtractionTerminalGeometryCertificate k n C η δ ζ c) :
    coreExtractionExceptional A.retained A.covered A.finalUnion =
      A.retainedᶜ ∪ (A.covered \ A.finalUnion) := rfl

/-- The full output core is literally `retainedᶜ ∪ covered`. -/
theorem outputCore_eq
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ c : ℝ}
    (A : CoreExtractionTerminalGeometryCertificate k n C η δ ζ c) :
    coreExtractionCore
        (coreExtractionExceptional A.retained A.covered A.finalUnion)
        A.clusters =
      A.retainedᶜ ∪ A.covered :=
  coreExtractionCore_eq_retained_compl_union
    A.finalUnion_subset_covered A.clusterUnion_eq

/-- The output remainder is literally `retained \ covered`. -/
theorem outputRemainder_eq
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ c : ℝ}
    (A : CoreExtractionTerminalGeometryCertificate k n C η δ ζ c) :
    coreExtractionRemainder
        (coreExtractionExceptional A.retained A.covered A.finalUnion)
        A.clusters =
      A.retained \ A.covered :=
  coreExtractionRemainder_eq_retained_sdiff
    A.finalUnion_subset_covered A.clusterUnion_eq

/-- Stages F9--F10: turn the terminal quotient geometry into the complete
assembly certificate.

The proof performs exactly the elementary bookkeeping suppressed in the
paper: define `U₀`, transfer cleaned color data back to the original coloring,
double-count the pointwise `U` boundary, bound the `U₀` boundary by its
cardinality, and use the transparent core/remainder identities. -/
noncomputable def toAssemblyCertificate
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ c : ℝ}
    (A : CoreExtractionTerminalGeometryCertificate k n C η δ ζ c) :
    CoreExtractionAssemblyCertificate k n C η δ ζ c := by
  classical
  let E := coreExtractionExceptional A.retained A.covered A.finalUnion
  let T := A.retained \ A.covered
  have hUretained : A.finalUnion ⊆ A.retained :=
    A.finalUnion_subset_covered.trans A.covered_subset_retained
  have hTretained : T ⊆ A.retained := by
    intro v hv
    exact (Finset.mem_sdiff.mp hv).1
  have hEU : Disjoint E A.finalUnion := by
    dsimp only [E]
    exact coreExtractionExceptional_disjoint
      A.finalUnion_subset_covered A.covered_subset_retained
  have hET : Disjoint E T := by
    rw [Finset.disjoint_left]
    intro v hvE hvT
    have hvT' := Finset.mem_sdiff.mp hvT
    rcases Finset.mem_union.mp hvE with hvOutside | hvCovered
    · exact (Finset.mem_compl.mp hvOutside) hvT'.1
    · exact hvT'.2 (Finset.mem_sdiff.mp hvCovered).1
  have hEcluster : ∀ i, Disjoint E (A.clusters i) := by
    intro i
    rw [Finset.disjoint_left]
    intro v hvE hvCluster
    exact Finset.disjoint_left.mp hEU hvE
      (A.cluster_subset_finalUnion i hvCluster)
  have herrorSumNonneg : 0 ≤ A.retainedError + A.uncoveredError :=
    add_nonneg A.retainedError_nonneg A.uncoveredError_nonneg
  have herrorSum_le : A.retainedError + A.uncoveredError ≤ ζ := by
    calc
      A.retainedError + A.uncoveredError ≤
          A.retainedError + A.uncoveredError + A.boundaryError :=
        le_add_of_nonneg_right A.boundaryError_nonneg
      _ ≤ ζ := A.errorBudget
  have hEcardError :
      (E.card : ℝ) ≤
        (A.retainedError + A.uncoveredError) * (n : ℝ) := by
    have hcardNat : E.card ≤
        A.retainedᶜ.card + (A.covered \ A.finalUnion).card := by
      dsimp only [E, coreExtractionExceptional]
      exact Finset.card_union_le _ _
    have hcard : (E.card : ℝ) ≤
        (A.retainedᶜ.card : ℝ) +
          ((A.covered \ A.finalUnion).card : ℝ) := by
      exact_mod_cast hcardNat
    calc
      (E.card : ℝ) ≤
          (A.retainedᶜ.card : ℝ) +
            ((A.covered \ A.finalUnion).card : ℝ) := hcard
      _ ≤ A.retainedError * (n : ℝ) +
          A.uncoveredError * (n : ℝ) :=
        add_le_add A.retainedComplementSmall A.uncoveredSmall
      _ = (A.retainedError + A.uncoveredError) * (n : ℝ) := by ring
  have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hEsmall : (E.card : ℝ) ≤ ζ * (n : ℝ) := by
    exact hEcardError.trans
      (mul_le_mul_of_nonneg_right herrorSum_le hnNonneg)
  have hblueDense : ∀ i,
      (1 - ζ) * (Nat.choose (A.clusters i).card 2 : ℝ) ≤
        (C.blueEdgeCountIn (A.clusters i) : ℝ) := by
    intro i
    have hclean := blueEdgeCountIn_lower_of_pointwise_degree
      (C.greenOutside A.retained) (A.clusters i) ζ
      (A.cleanedBlueDegree i)
    change (1 - ζ) * (Nat.choose (A.clusters i).card 2 : ℝ) ≤
      (((C.greenOutside A.retained).edgeCountIn .blue
        (A.clusters i) : ℕ) : ℝ) at hclean
    rw [C.greenOutside_edgeCountIn_of_subset A.retained .blue
      (A.cluster_subset_retained i)] at hclean
    simpa only using hclean
  have hredDense : ∀ i j, A.reducedGraph.Adj i j →
      1 - ζ ≤ C.colorDensity .red (A.clusters i) (A.clusters j) := by
    intro i j hij
    have h := A.cleanedRedDenseOnEdges i j hij
    rw [C.greenOutside_colorDensity_of_subsets A.retained .red
      (A.cluster_subset_retained i) (A.cluster_subset_retained j)] at h
    exact h
  have hgreenDense : ∀ i j, i ≠ j → ¬ A.reducedGraph.Adj i j →
      1 - ζ ≤ C.colorDensity .green (A.clusters i) (A.clusters j) := by
    intro i j hij hnonadj
    have h := A.cleanedGreenDenseOnNonedges i j hij hnonadj
    rw [C.greenOutside_colorDensity_of_subsets A.retained .green
      (A.cluster_subset_retained i) (A.cluster_subset_retained j)] at h
    exact h
  have hUboundary :
      (C.colorEdgeCountBetween .red A.finalUnion T : ℝ) +
          (C.colorEdgeCountBetween .blue A.finalUnion T : ℝ) ≤
        A.boundaryError * (n : ℝ) ^ 2 := by
    have hclean := redBlueColorEdgeCountBetween_le_sq_of_pointwise
      (C.greenOutside A.retained) A.finalUnion T A.boundaryError
      A.boundaryError_nonneg A.cleanedBoundaryPointwise
    rw [C.greenOutside_colorEdgeCountBetween_of_subsets A.retained .red
        hUretained hTretained,
      C.greenOutside_colorEdgeCountBetween_of_subsets A.retained .blue
        hUretained hTretained] at hclean
    exact hclean
  have hTcardNat : T.card ≤ n := by
    simpa using Finset.card_le_univ T
  have hTcard : (T.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hTcardNat
  have hEredBluePairs :
      (C.colorEdgeCountBetween .red E T : ℝ) +
          (C.colorEdgeCountBetween .blue E T : ℝ) ≤
        (E.card : ℝ) * (T.card : ℝ) := by
    have hpartitionNat := C.red_add_green_add_blue_colorEdgeCountBetween hET
    have hpartition :
        (C.colorEdgeCountBetween .red E T : ℝ) +
            (C.colorEdgeCountBetween .green E T : ℝ) +
            (C.colorEdgeCountBetween .blue E T : ℝ) =
          (E.card : ℝ) * (T.card : ℝ) := by
      exact_mod_cast hpartitionNat
    have hgreen :
        0 ≤ (C.colorEdgeCountBetween .green E T : ℝ) := by positivity
    linarith
  have hEboundary :
      (C.colorEdgeCountBetween .red E T : ℝ) +
          (C.colorEdgeCountBetween .blue E T : ℝ) ≤
        (A.retainedError + A.uncoveredError) * (n : ℝ) ^ 2 := by
    calc
      (C.colorEdgeCountBetween .red E T : ℝ) +
            (C.colorEdgeCountBetween .blue E T : ℝ) ≤
          (E.card : ℝ) * (T.card : ℝ) := hEredBluePairs
      _ ≤ ((A.retainedError + A.uncoveredError) * (n : ℝ)) *
          (T.card : ℝ) :=
        mul_le_mul_of_nonneg_right hEcardError (Nat.cast_nonneg T.card)
      _ ≤ ((A.retainedError + A.uncoveredError) * (n : ℝ)) *
          (n : ℝ) :=
        mul_le_mul_of_nonneg_left hTcard
          (mul_nonneg herrorSumNonneg hnNonneg)
      _ = (A.retainedError + A.uncoveredError) * (n : ℝ) ^ 2 := by ring
  have hsplit (color : EdgeColor) :
      C.colorEdgeCountBetween color (E ∪ A.finalUnion) T =
        C.colorEdgeCountBetween color E T +
          C.colorEdgeCountBetween color A.finalUnion T := by
    calc
      C.colorEdgeCountBetween color (E ∪ A.finalUnion) T =
          ∑ v ∈ E ∪ A.finalUnion, C.degreeIn color v T :=
        (C.sum_degreeIn_eq_colorEdgeCountBetween color
          (E ∪ A.finalUnion) T).symm
      _ = (∑ v ∈ E, C.degreeIn color v T) +
          ∑ v ∈ A.finalUnion, C.degreeIn color v T :=
        Finset.sum_union hEU
      _ = C.colorEdgeCountBetween color E T +
          C.colorEdgeCountBetween color A.finalUnion T := by
        rw [C.sum_degreeIn_eq_colorEdgeCountBetween,
          C.sum_degreeIn_eq_colorEdgeCountBetween]
  have hcoreEU :
      coreExtractionCore E A.clusters = E ∪ A.finalUnion := by
    rw [coreExtractionCore, A.clusterUnion_eq]
  have hremT : coreExtractionRemainder E A.clusters = T := by
    dsimp only [E, T]
    exact A.outputRemainder_eq
  have hboundary :
      (C.colorEdgeCountBetween .red
            (coreExtractionCore E A.clusters)
            (coreExtractionRemainder E A.clusters) : ℝ) +
          (C.colorEdgeCountBetween .blue
            (coreExtractionCore E A.clusters)
            (coreExtractionRemainder E A.clusters) : ℝ) ≤
        ζ * (n : ℝ) ^ 2 := by
    rw [hcoreEU, hremT, hsplit .red, hsplit .blue]
    push_cast
    calc
      ((C.colorEdgeCountBetween .red E T : ℝ) +
            (C.colorEdgeCountBetween .red A.finalUnion T : ℝ)) +
          ((C.colorEdgeCountBetween .blue E T : ℝ) +
            (C.colorEdgeCountBetween .blue A.finalUnion T : ℝ)) =
          ((C.colorEdgeCountBetween .red E T : ℝ) +
            (C.colorEdgeCountBetween .blue E T : ℝ)) +
          ((C.colorEdgeCountBetween .red A.finalUnion T : ℝ) +
            (C.colorEdgeCountBetween .blue A.finalUnion T : ℝ)) := by ring
      _ ≤ (A.retainedError + A.uncoveredError) * (n : ℝ) ^ 2 +
          A.boundaryError * (n : ℝ) ^ 2 :=
        add_le_add hEboundary hUboundary
      _ = (A.retainedError + A.uncoveredError + A.boundaryError) *
          (n : ℝ) ^ 2 := by ring
      _ ≤ ζ * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right A.errorBudget (sq_nonneg (n : ℝ))
  have hcoreTransparent :
      coreExtractionCore E A.clusters = A.retainedᶜ ∪ A.covered := by
    dsimp only [E]
    exact A.outputCore_eq
  exact {
    clusterCount := A.clusterCount
    clusterCount_ge := A.clusterCount_ge
    exceptional := E
    clusters := A.clusters
    clusters_pairwiseDisjoint := A.clusters_pairwiseDisjoint
    exceptional_disjoint_clusters := hEcluster
    reducedGraph := A.reducedGraph
    reducedGraphAdjDecidable := A.reducedGraphAdjDecidable
    reducedGraph_regular := A.reducedGraph_regular
    blueDense := hblueDense
    clusterLowerBound := A.clusterLowerBound
    clusterBalanced := A.clusterBalanced
    exceptionalSmall := hEsmall
    clusterUnionLarge := by simpa only [A.clusterUnion_eq] using A.finalUnionLarge
    redDenseOnEdges := hredDense
    greenDenseOnNonedges := hgreenDense
    boundarySmall := hboundary
    coloring_mem_Ck := A.coloring_mem_Ck
    wholeNearExtremal := A.wholeNearExtremal
    coreMantelAbsorbed := by
      rw [hcoreTransparent]
      exact A.coreMantelAbsorbed
  }

end CoreExtractionTerminalGeometryCertificate

namespace CoreExtractionAssemblyCertificate

/-- The exact integer objective decomposition attached to an assembly
certificate.  The complement on the right is definitionally the paper's
remainder `T`. -/
theorem objective_decomposition
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ c : ℝ}
    (A : CoreExtractionAssemblyCertificate k n C η δ ζ c) :
    objective k C =
      objectiveIn k C (coreExtractionCore A.exceptional A.clusters) +
        objectiveBetween k C
          (coreExtractionCore A.exceptional A.clusters)
          (coreExtractionRemainder A.exceptional A.clusters) +
        objectiveIn k C
          (coreExtractionRemainder A.exceptional A.clusters) := by
  simpa only [coreExtractionRemainder] using
    objective_eq_objectiveIn_add_between_add_compl
      (k := k) C (coreExtractionCore A.exceptional A.clusters)

/-- Stage F11: the exact decomposition, the favorable sign of the blue cut,
and the induced Mantel bound leave at most the three explicitly allocated
`ζ n²` losses on the remainder. -/
theorem remainderNearExtremal
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ c : ℝ}
    (A : CoreExtractionAssemblyCertificate k n C η δ ζ c)
    (hk : 3 ≤ k) :
    -((δ + 3 * ζ) * (n : ℝ) ^ 2) ≤
      (C.redEdgeCountIn
          (coreExtractionRemainder A.exceptional A.clusters) : ℝ) -
        (delta k : ℝ) *
          (C.blueEdgeCountIn
            (coreExtractionRemainder A.exceptional A.clusters) : ℝ) := by
  let S := coreExtractionCore A.exceptional A.clusters
  have hblueCut : 0 ≤
      (C.colorEdgeCountBetween .blue S (Finset.univ \ S) : ℝ) := by
    positivity
  have hredCut :
      (C.colorEdgeCountBetween .red S (Finset.univ \ S) : ℝ) ≤
        ζ * (n : ℝ) ^ 2 := by
    have hboundary := A.boundarySmall
    change
      (C.colorEdgeCountBetween .red S (Finset.univ \ S) : ℝ) +
          (C.colorEdgeCountBetween .blue S (Finset.univ \ S) : ℝ) ≤
        ζ * (n : ℝ) ^ 2 at hboundary
    linarith
  have hcore : (((delta k * S.card / 2 : ℕ) : ℝ)) ≤
      ζ * (n : ℝ) ^ 2 := by
    exact A.coreMantelAbsorbed
  have hrem := objectiveIn_compl_lower_bound (k := k) (n := n)
    hk A.coloring_mem_Ck S
    (a := δ + ζ) (b := ζ) (g := ζ)
    A.wholeNearExtremal hredCut hcore
  have hcoefficient : (δ + ζ) + ζ + ζ = δ + 3 * ζ := by ring
  rw [hcoefficient] at hrem
  simpa only [S, coreExtractionRemainder, objectiveIn, Int.cast_sub,
    Int.cast_mul, Int.cast_natCast] using hrem

/-- Package the F9--F11 assembly certificate as the raw recursion output.
The only proof performed here is F11; all other fields are copied
transparently so later users retain direct access to the six conclusions. -/
noncomputable def toRawResult
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ζ c : ℝ}
    (A : CoreExtractionAssemblyCertificate k n C η δ ζ c)
    (hk : 3 ≤ k) :
    CoreExtractionRawResult k n C η δ ζ c := {
  clusterCount := A.clusterCount
  clusterCount_ge := A.clusterCount_ge
  exceptional := A.exceptional
  clusters := A.clusters
  clusters_pairwiseDisjoint := A.clusters_pairwiseDisjoint
  exceptional_disjoint_clusters := A.exceptional_disjoint_clusters
  reducedGraph := A.reducedGraph
  reducedGraphAdjDecidable := A.reducedGraphAdjDecidable
  reducedGraph_regular := A.reducedGraph_regular
  blueDense := A.blueDense
  clusterLowerBound := A.clusterLowerBound
  clusterBalanced := A.clusterBalanced
  exceptionalSmall := A.exceptionalSmall
  clusterUnionLarge := A.clusterUnionLarge
  redDenseOnEdges := A.redDenseOnEdges
  greenDenseOnNonedges := A.greenDenseOnNonedges
  boundarySmall := A.boundarySmall
  remainderNearExtremal := A.remainderNearExtremal hk
}

end CoreExtractionAssemblyCertificate

/-! ## Concrete bounded seed run -/

/-- Membership in a finite stage-neighborhood union is witnessed by one
stage in the list. -/
theorem mem_stageNeighborhoodUnion_iff
    {S V : Type*} [DecidableEq V] (neighborhood : S → Finset V)
    (run : List S) (v : V) :
    v ∈ stageNeighborhoodUnion neighborhood run ↔
      ∃ s ∈ run, v ∈ neighborhood s := by
  induction run with
  | nil => simp
  | cons s run ih => simp [ih]

/-- A cleaned red edge can only join retained vertices. -/
theorem CleanedCoreStart.cleaned_redNeighborFinset_subset_retained
    {k n : ℕ} {eta tailScale : ℝ} {C : ColoredGraph (Fin n)}
    (A : CleanedCoreStart k n C eta tailScale) (v : Fin n) :
    A.cleaned.redNeighborFinset v ⊆ A.retained := by
  classical
  intro w hw
  have hred := (A.cleaned.mem_neighborFinset .red v w).1 hw
  by_contra hwRetained
  have hgreen := C.greenOutside_color_of_not_both A.retained hred.1
    (by simp [hwRetained])
  have hredOutside :
      (C.greenOutside A.retained).color v w = .red := by
    simpa only [A.cleaned_eq] using hred.2
  rw [hgreen] at hredOutside
  simpa using hredOutside

/-- The terminal hierarchy error is at most a quarter of the red-density
scale once the sole additive master-constant slot has been absorbed. -/
theorem CoreExtractionParameters.terminalError_le_eta_quarter_mul
    {k n : ℕ} {eta zeta : ℝ} (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k eta zeta)
    (hn : ⌈(8 * P.master) / eta⌉₊ ≤ n) :
    P.terminalError n ≤ (eta / 4) * (n : ℝ) := by
  let qlast : Fin (P.stageBound + 1) := Fin.last P.stageBound
  have hmasterOne : (1 : ℝ) ≤ P.master := by
    linarith [P.one_ninety_two_le_master]
  have htauLe : P.tau ≤ P.master * P.tau := by
    nlinarith [P.tau_pos]
  have htauEta : P.tau < eta / 100 :=
    htauLe.trans_lt P.tau_lt_eta
  have hfactor : (1 : ℝ) ≤ (P.stageBound + 1 : ℝ) ^ 2 := by
    have hstageNonneg : (0 : ℝ) ≤ (P.stageBound : ℝ) :=
      Nat.cast_nonneg _
    nlinarith [sq_nonneg ((P.stageBound : ℝ) + 1)]
  have hrootNonneg :
      0 ≤ Real.sqrt (P.betaSeq qlast) := Real.sqrt_nonneg _
  have hbaseLe :
      P.master * Real.sqrt (P.betaSeq qlast) ≤
        P.master * (P.stageBound + 1 : ℝ) ^ 2 *
          Real.sqrt (P.betaSeq qlast) := by
    calc
      P.master * Real.sqrt (P.betaSeq qlast) =
          (P.master * Real.sqrt (P.betaSeq qlast)) * 1 := by ring
      _ ≤ (P.master * Real.sqrt (P.betaSeq qlast)) *
          (P.stageBound + 1 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg P.master_pos.le hrootNonneg)
      _ = P.master * (P.stageBound + 1 : ℝ) ^ 2 *
          Real.sqrt (P.betaSeq qlast) := by ring
  have hbaseLt :
      P.master * Real.sqrt (P.betaSeq qlast) < P.tau / 2 :=
    hbaseLe.trans_lt (by simpa [qlast] using P.betaLast_overlap)
  have hcoefficient :
      (P.master / 100) * Real.sqrt (P.betaSeq qlast) ≤ eta / 8 := by
    have : (P.master / 100) * Real.sqrt (P.betaSeq qlast) < eta / 20000 := by
      nlinarith
    linarith [heta.1]
  have hceil : (8 * P.master) / eta ≤
      (⌈(8 * P.master) / eta⌉₊ : ℕ) := Nat.le_ceil _
  have hnReal : ((⌈(8 * P.master) / eta⌉₊ : ℕ) : ℝ) ≤
      (n : ℝ) := by exact_mod_cast hn
  have habsorbRatio : (8 * P.master) / eta ≤ (n : ℝ) :=
    hceil.trans hnReal
  have habsorb : P.master ≤ (eta / 8) * (n : ℝ) := by
    have hmul := (div_le_iff₀ heta.1).mp habsorbRatio
    nlinarith
  have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlinear := mul_le_mul_of_nonneg_right hcoefficient hnNonneg
  have hlinear' :
      (P.master / 100) *
          Real.sqrt (P.betaSeq (Fin.last P.stageBound)) * (n : ℝ) ≤
        (eta / 8) * (n : ℝ) := by
    simpa [qlast] using hlinear
  unfold CoreExtractionParameters.terminalError
    CoreExtractionParameters.levelError
  nlinarith

/-- The stage-count choice has enough aggregate `τ n` capacity to force
finite stopping. -/
theorem CoreExtractionParameters.card_lt_stageBound_sub_one_mul_ceil
    {k n : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta)
    (hn : 0 < n) :
    n < (P.stageBound - 1) * ⌈P.tau * (n : ℝ)⌉₊ := by
  have hmasterOne : (1 : ℝ) ≤ P.master := by
    linarith [P.one_ninety_two_le_master]
  have hstageTwo : 2 ≤ P.stageBound := by
    have hratioPos : 0 < P.master / P.tau :=
      div_pos P.master_pos P.tau_pos
    have : (1 : ℝ) < (P.stageBound : ℕ) := by
      linarith [P.stageBound_covers]
    exact_mod_cast this
  have hsubAdd : P.stageBound - 1 + 1 = P.stageBound := by omega
  have hLReal : P.master / P.tau < (P.stageBound - 1 : ℕ) := by
    have hcast : ((P.stageBound - 1 : ℕ) : ℝ) + 1 =
        (P.stageBound : ℝ) := by exact_mod_cast hsubAdd
    linarith [P.stageBound_covers]
  have hinvLe : 1 / P.tau ≤ P.master / P.tau := by
    exact (div_le_div_iff_of_pos_right P.tau_pos).2 hmasterOne
  have honeLt : (1 : ℝ) <
      (P.stageBound - 1 : ℕ) * P.tau := by
    have := hinvLe.trans_lt hLReal
    exact (div_lt_iff₀ P.tau_pos).mp (by simpa using this)
  have hceil : P.tau * (n : ℝ) ≤
      (⌈P.tau * (n : ℝ)⌉₊ : ℕ) := Nat.le_ceil _
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hproduct : (n : ℝ) <
      (P.stageBound - 1 : ℕ) * (P.tau * (n : ℝ)) := by
    nlinarith
  have hLNonneg : (0 : ℝ) ≤ (P.stageBound - 1 : ℕ) := by positivity
  have hproductCeil :
      (P.stageBound - 1 : ℕ) * (P.tau * (n : ℝ)) ≤
        (P.stageBound - 1 : ℕ) *
          (⌈P.tau * (n : ℝ)⌉₊ : ℕ) :=
    mul_le_mul_of_nonneg_left hceil hLNonneg
  exact_mod_cast hproduct.trans_le hproductCeil

/-- Validity-aware form of maximal indexed stopping.  The valid-prefix
hypothesis is essential: it certifies that all earlier levels precede the
requested realization level. -/
theorem exists_maximal_indexedCoreSeedStageRun_and_stop_of_valid_realize
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)} {control : Finset (Fin n)} {reference : ℝ}
    (initial : IndexedCoreSeedStage (P := P) (C := C)
      (control := control) (reference := reference))
    (hinitial : initial.level.val = 0)
    (newMass L : ℕ) (hL : 0 < L) (hLBound : L < P.stageBound)
    (hcapacity : n < L * newMass)
    (realize : ∀
      (q : Fin P.stageBound)
      (run : List (IndexedCoreSeedStage (P := P) (C := C)
        (control := control) (reference := reference))),
      StageRunValid initial indexedCoreSeedStageEligible
          (fun S ↦ S.stage.redNeighborhood) newMass run →
      ∀ v : Fin n,
      run.length = q.val →
      v ∈ control → v ∈ indexedStageRunTypicalUnion run →
      ∃ next : IndexedCoreSeedStage (P := P) (C := C)
        (control := control) (reference := reference),
        next.level = q ∧ next.stage.seed = v) :
    ∃ run,
      StageRunValid initial indexedCoreSeedStageEligible
        (fun S ↦ S.stage.redNeighborhood) newMass run ∧
      run.length ≤ L ∧
      run.map (fun S ↦ S.level.val) = List.range run.length ∧
      ∀ v ∈ control, v ∈ indexedStageRunTypicalUnion run →
        (C.redNeighborFinset v \ indexedStageRunRedNeighborhoodUnion run).card <
          newMass := by
  have hcard : Fintype.card (Fin n) < L * newMass := by simpa using hcapacity
  obtain ⟨run, hvalid, hlength, hstop⟩ :=
    exists_maximal_stageRun_and_stop initial indexedCoreSeedStageEligible
      (fun S ↦ S.stage.redNeighborhood) newMass L hL hcard
  refine ⟨run, hvalid, hlength,
    indexedCoreSeedStageRun_levels_eq_range initial hinitial hvalid, ?_⟩
  intro v hvcontrol hvtypical
  let q : Fin P.stageBound :=
    ⟨run.length, lt_of_le_of_lt hlength hLBound⟩
  obtain ⟨next, hlevel, hseed⟩ :=
    realize q run hvalid v rfl hvcontrol hvtypical
  have heligible : indexedCoreSeedStageEligible run next := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hlevel]
    · simpa [hseed] using hvcontrol
    · simpa [hseed] using hvtypical
  have hnext := hstop next heligible
  rw [next.stage.redNeighborhood_eq, hseed] at hnext
  exact hnext

/-- A typical vertex has many red neighbors outside its own seed
neighborhood.  This is the exact one-stage estimate used to show that the
concrete seed run cannot stop after its initial stage. -/
theorem UniformCoreSeedStage.redDegreeOutside_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} {C : ColoredGraph V} {control : Finset V}
    {reference error : ℝ}
    (S : UniformCoreSeedStage k C control reference error)
    (i : Fin (delta k)) (v : V) (hv : v ∈ S.typical i) :
    reference / (delta k : ℝ) - 3 * error - S.internalNonblueCap ≤
      ((C.redNeighborFinset v \ S.redNeighborhood).card : ℝ) := by
  have hpartSubset : S.parts i ⊆ S.redNeighborhood := by
    intro w hw
    rw [← S.parts_cover]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hw⟩
  have hsplitInsideNat :=
    C.degreeIn_add_degreeIn_sdiff .red v hpartSubset
  have hsplitInside :
      (C.redDegreeIn v (S.parts i) : ℝ) +
          (C.redDegreeIn v (S.redNeighborhood \ S.parts i) : ℝ) =
        (C.redDegreeIn v S.redNeighborhood : ℝ) := by
    exact_mod_cast hsplitInsideNat
  have hpartRedNat :
      C.redDegreeIn v (S.parts i) ≤ S.internalNonblueCap := by
    have hnonblue := S.lowInternalNonblue i v hv
    omega
  have hpartRed :
      (C.redDegreeIn v (S.parts i) : ℝ) ≤
        (S.internalNonblueCap : ℝ) := by
    exact_mod_cast hpartRedNat
  have hrestNat :=
    degreeIn_le_card C .red v (S.redNeighborhood \ S.parts i)
  have hrest :
      (C.redDegreeIn v (S.redNeighborhood \ S.parts i) : ℝ) ≤
        ((S.redNeighborhood \ S.parts i).card : ℝ) := by
    exact_mod_cast hrestNat
  have hcardSplitNat := Finset.card_sdiff_add_card_eq_card hpartSubset
  have hcardSplit :
      ((S.redNeighborhood \ S.parts i).card : ℝ) +
          ((S.parts i).card : ℝ) =
        (S.redNeighborhood.card : ℝ) := by
    exact_mod_cast hcardSplitNat
  have hredNeighborhoodCard :
      S.redNeighborhood.card = C.redDegree S.seed := by
    rw [S.redNeighborhood_eq]
    rfl
  have hseedUpper :
      (S.redNeighborhood.card : ℝ) ≤ reference + error := by
    have h := (abs_le.mp S.seedRedNearReference).2
    rw [hredNeighborhoodCard]
    linarith
  have hpartLower :
      reference / (delta k : ℝ) - error ≤
        ((S.parts i).card : ℝ) := by
    have h := (abs_le.mp (S.partBalanced i)).1
    linarith
  have hinsideUpper :
      (C.redDegreeIn v S.redNeighborhood : ℝ) ≤
        reference - reference / (delta k : ℝ) +
          (S.internalNonblueCap : ℝ) + 2 * error := by
    linarith
  have hsplitOutsideNat :=
    degreeIn_add_degreeIn_compl C .red v S.redNeighborhood
  have hsplitOutside :
      (C.redDegreeIn v S.redNeighborhood : ℝ) +
          (C.redDegreeIn v S.redNeighborhoodᶜ : ℝ) =
        (C.redDegree v : ℝ) := by
    exact_mod_cast hsplitOutsideNat
  have houtsideCard :
      (C.redNeighborFinset v \ S.redNeighborhood).card =
        C.redDegreeIn v S.redNeighborhoodᶜ := by
    change (C.neighborFinset .red v \ S.redNeighborhood).card =
      (C.neighborFinset .red v ∩ S.redNeighborhoodᶜ).card
    rw [Finset.sdiff_eq_inter_compl]
  rw [houtsideCard]
  linarith [S.highTotalRed i v hv]

/-- At the concrete parameter scale, every typical vertex of an indexed
stage has at least `⌈τ n⌉` red neighbors outside that stage's seed
neighborhood.  The explicit threshold only absorbs the additive ceiling and
the constant slot in `levelError`. -/
theorem IndexedUniformCoreSeedStage.newMass_le_redDegreeOutside
    {k n : ℕ} {eta zeta : ℝ} (hk : 3 ≤ k)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k eta zeta)
    {C : ColoredGraph (Fin n)}
    (A : CleanedCoreStart k n C eta P.tailScale)
    (S : IndexedUniformCoreSeedStage P A.cleaned A.goodSet
      (C.redDegree A.seed : ℝ))
    (i : Fin (delta k)) (v : Fin n) (hv : v ∈ S.stage.typical i)
    (hn : ⌈(4 * P.master + 2) / P.tau⌉₊ ≤ n) :
    ⌈P.tau * (n : ℝ)⌉₊ ≤
      (A.cleaned.redNeighborFinset v \ S.stage.redNeighborhood).card := by
  let D : ℝ := delta k
  let N : ℝ := n
  let K : ℝ := P.master
  let b : ℝ := Real.sqrt (P.betaSeq (Fin.last P.stageBound))
  have hDpos : 0 < D := by
    change 0 < (delta k : ℝ)
    exact_mod_cast (show 0 < delta k by unfold delta; omega)
  have hNnonneg : 0 ≤ N := by positivity
  have hKpos : 0 < K := by simpa only [K] using P.master_pos
  have hKone : 1 ≤ K := by
    have := P.one_ninety_two_le_master
    change (192 : ℝ) ≤ K at this
    linarith
  have hbNonneg : 0 ≤ b := by
    exact Real.sqrt_nonneg _
  have hfactor : (1 : ℝ) ≤ (P.stageBound + 1 : ℝ) ^ 2 := by
    have hstageNonneg : (0 : ℝ) ≤ (P.stageBound : ℝ) :=
      Nat.cast_nonneg _
    nlinarith [sq_nonneg ((P.stageBound : ℝ) + 1)]
  have hKbLe : K * b ≤
      K * (P.stageBound + 1 : ℝ) ^ 2 * b := by
    calc
      K * b = (K * b) * 1 := by ring
      _ ≤ (K * b) * (P.stageBound + 1 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg hKpos.le hbNonneg)
      _ = K * (P.stageBound + 1 : ℝ) ^ 2 * b := by ring
  have hKbSmall : K * b < eta * P.tau / 100000 := by
    exact hKbLe.trans_lt (by simpa only [K, b] using P.betaLast_overlap_strong)
  have hetaTauLt : eta * P.tau < P.tau :=
    mul_lt_of_lt_one_left P.tau_pos heta.2
  have hsmallTau : eta * P.tau / 100000 < P.tau := by
    calc
      eta * P.tau / 100000 < P.tau / 100000 :=
        div_lt_div_of_pos_right hetaTauLt (by norm_num)
      _ < P.tau := by nlinarith [P.tau_pos]
  have hbLeTau : b ≤ P.tau := by
    have hbLeKb : b ≤ K * b := by nlinarith
    exact hbLeKb.trans (hKbSmall.trans hsmallTau).le
  have herrorLe :
      P.levelError S.level.succ n ≤ P.tau * N + K := by
    have hterminal := P.levelError_le_terminal S.level.succ n
    have hcoefficient : (K / 100) * b ≤ P.tau := by
      exact (calc
        (K / 100) * b = (K * b) / 100 := by ring
        _ < (eta * P.tau / 100000) / 100 :=
          div_lt_div_of_pos_right hKbSmall (by norm_num)
        _ < P.tau := by nlinarith [hsmallTau, P.tau_pos]).le
    have hlinear := mul_le_mul_of_nonneg_right hcoefficient hNnonneg
    calc
      P.levelError S.level.succ n ≤ P.terminalError n := hterminal
      _ = (K / 100) * b * N + K := by
        simp only [CoreExtractionParameters.terminalError,
          CoreExtractionParameters.levelError, K, b, N]
      _ ≤ P.tau * N + K := by linarith
  have hcapLe :
      (S.stage.internalNonblueCap : ℝ) ≤ P.tau * N + 1 := by
    have hcapCast :
        (S.stage.internalNonblueCap : ℝ) ≤
          (coreSeedNonblueCap
            (P.betaSeq (Fin.last P.stageBound)) n : ℝ) := by
      exact_mod_cast S.terminalNonblueCap
    have hcap := coreSeedNonblueCap_lt_add_one
      (P.betaSeq_pos (Fin.last P.stageBound)).le n
    have hbN := mul_le_mul_of_nonneg_right hbLeTau hNnonneg
    change (coreSeedNonblueCap
        (P.betaSeq (Fin.last P.stageBound)) n : ℝ) < b * N + 1 at hcap
    linarith
  have hDleK : D ≤ K := by
    have hmaster := P.ten_thousand_mul_delta_add_one_le_master
    change 10000 * (D + 1) ≤ K at hmaster
    nlinarith
  have hDtau : 100 * D * P.tau ≤ eta := by
    have hmul := mul_le_mul_of_nonneg_right hDleK P.tau_pos.le
    have htauSmall := P.tau_lt_eta
    change K * P.tau < eta / 100 at htauSmall
    nlinarith
  have hmain :
      100 * P.tau * N ≤ (C.redDegree A.seed : ℝ) / D := by
    apply (le_div_iff₀ hDpos).2
    have hmul := mul_le_mul_of_nonneg_right hDtau hNnonneg
    calc
      100 * P.tau * N * D = (100 * D * P.tau) * N := by ring
      _ ≤ eta * N := hmul
      _ ≤ (C.redDegree A.seed : ℝ) := by
        simpa only [N] using A.seed_red_lower
  have hthreshold : 4 * K + 2 ≤ P.tau * N := by
    have hceil : (4 * K + 2) / P.tau ≤
        (⌈(4 * P.master + 2) / P.tau⌉₊ : ℕ) := by
      simpa only [K] using Nat.le_ceil ((4 * P.master + 2) / P.tau)
    have hnReal :
        ((⌈(4 * P.master + 2) / P.tau⌉₊ : ℕ) : ℝ) ≤ N := by
      change ((⌈(4 * P.master + 2) / P.tau⌉₊ : ℕ) : ℝ) ≤
        (n : ℝ)
      exact_mod_cast hn
    have hratio := hceil.trans hnReal
    have := (div_le_iff₀ P.tau_pos).mp hratio
    nlinarith
  have hceilMass :
      ((⌈P.tau * (n : ℝ)⌉₊ : ℕ) : ℝ) < P.tau * N + 1 := by
    simpa only [N] using
      Nat.ceil_lt_add_one (mul_nonneg P.tau_pos.le (Nat.cast_nonneg n))
  have houtside := S.stage.redDegreeOutside_lower i v hv
  change (C.redDegree A.seed : ℝ) / D -
      3 * P.levelError S.level.succ n -
        (S.stage.internalNonblueCap : ℝ) ≤
      ((A.cleaned.redNeighborFinset v \
        S.stage.redNeighborhood).card : ℝ) at houtside
  have hreal :
      ((⌈P.tau * (n : ℝ)⌉₊ : ℕ) : ℝ) ≤
        ((A.cleaned.redNeighborFinset v \
          S.stage.redNeighborhood).card : ℝ) := by
    linarith
  exact_mod_cast hreal

/-- Every hierarchy error is bounded by one `τ n` slot plus the fixed
master-constant slot. -/
theorem CoreExtractionParameters.levelError_le_tau_mul_add_master
    {k n : ℕ} {eta zeta : ℝ} (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k eta zeta)
    (q : Fin (P.stageBound + 1)) :
    P.levelError q n ≤ P.tau * (n : ℝ) + P.master := by
  let b : ℝ := Real.sqrt (P.betaSeq (Fin.last P.stageBound))
  have hbNonneg : 0 ≤ b := Real.sqrt_nonneg _
  have hfactor : (1 : ℝ) ≤ (P.stageBound + 1 : ℝ) ^ 2 := by
    have hstageNonneg : (0 : ℝ) ≤ (P.stageBound : ℝ) :=
      Nat.cast_nonneg _
    nlinarith [sq_nonneg ((P.stageBound : ℝ) + 1)]
  have hKbLe : P.master * b ≤
      P.master * (P.stageBound + 1 : ℝ) ^ 2 * b := by
    calc
      P.master * b = (P.master * b) * 1 := by ring
      _ ≤ (P.master * b) * (P.stageBound + 1 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg P.master_pos.le hbNonneg)
      _ = P.master * (P.stageBound + 1 : ℝ) ^ 2 * b := by ring
  have hKbSmall : P.master * b < eta * P.tau / 100000 := by
    exact hKbLe.trans_lt
      (by simpa only [b] using P.betaLast_overlap_strong)
  have hetaTauLt : eta * P.tau < P.tau :=
    mul_lt_of_lt_one_left P.tau_pos heta.2
  have hsmallTau : eta * P.tau / 100000 < P.tau := by
    calc
      eta * P.tau / 100000 < P.tau / 100000 :=
        div_lt_div_of_pos_right hetaTauLt (by norm_num)
      _ < P.tau := by nlinarith [P.tau_pos]
  have hcoefficient : (P.master / 100) * b ≤ P.tau := by
    exact (calc
      (P.master / 100) * b = (P.master * b) / 100 := by ring
      _ < (eta * P.tau / 100000) / 100 :=
        div_lt_div_of_pos_right hKbSmall (by norm_num)
      _ < P.tau := by nlinarith [hsmallTau, P.tau_pos]).le
  have hlinear := mul_le_mul_of_nonneg_right hcoefficient
    (Nat.cast_nonneg n)
  calc
    P.levelError q n ≤ P.terminalError n :=
      P.levelError_le_terminal q n
    _ = (P.master / 100) * b * (n : ℝ) + P.master := by
      simp only [CoreExtractionParameters.terminalError,
        CoreExtractionParameters.levelError, b]
    _ ≤ P.tau * (n : ℝ) + P.master := by linarith

/-- The original maximum red degree, divided by `Δ`, dominates one hundred
continuation-mass slots. -/
theorem CleanedCoreStart.hundred_tau_mul_le_seed_red_div_delta
    {k n : ℕ} {eta zeta : ℝ} (hk : 3 ≤ k)
    (P : CoreExtractionParameters k eta zeta)
    {C : ColoredGraph (Fin n)}
    (A : CleanedCoreStart k n C eta P.tailScale) :
    100 * P.tau * (n : ℝ) ≤
      (C.redDegree A.seed : ℝ) / (delta k : ℝ) := by
  have hDpos : 0 < (delta k : ℝ) := by
    exact_mod_cast (show 0 < delta k by unfold delta; omega)
  have hDleK : (delta k : ℝ) ≤ P.master := by
    have hmaster := P.ten_thousand_mul_delta_add_one_le_master
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hDleK P.tau_pos.le
  have hDtau : 100 * (delta k : ℝ) * P.tau ≤ eta := by
    nlinarith [P.tau_lt_eta]
  apply (le_div_iff₀ hDpos).2
  have hN := mul_le_mul_of_nonneg_right hDtau (Nat.cast_nonneg n)
  calc
    100 * P.tau * (n : ℝ) * (delta k : ℝ) =
        (100 * (delta k : ℝ) * P.tau) * (n : ℝ) := by ring
    _ ≤ eta * (n : ℝ) := hN
    _ ≤ (C.redDegree A.seed : ℝ) := A.seed_red_lower

/-- The explicit second-stage threshold absorbs all fixed additive slots. -/
theorem CoreExtractionParameters.four_master_add_two_le_tau_mul
    {k n : ℕ} {eta zeta : ℝ}
    (P : CoreExtractionParameters k eta zeta)
    (hn : ⌈(4 * P.master + 2) / P.tau⌉₊ ≤ n) :
    4 * P.master + 2 ≤ P.tau * (n : ℝ) := by
  have hceil : (4 * P.master + 2) / P.tau ≤
      (⌈(4 * P.master + 2) / P.tau⌉₊ : ℕ) :=
    Nat.le_ceil _
  have hnReal :
      ((⌈(4 * P.master + 2) / P.tau⌉₊ : ℕ) : ℝ) ≤
        (n : ℝ) := by
    exact_mod_cast hn
  have hratio := hceil.trans hnReal
  calc
    4 * P.master + 2 ≤ (n : ℝ) * P.tau :=
      (div_le_iff₀ P.tau_pos).mp hratio
    _ = P.tau * (n : ℝ) := mul_comm _ _

/-- Each part of a sufficiently large indexed stage has a typical vertex. -/
theorem IndexedUniformCoreSeedStage.exists_mem_typical
    {k n : ℕ} {eta zeta : ℝ} (hk : 3 ≤ k)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k eta zeta)
    {C : ColoredGraph (Fin n)}
    (A : CleanedCoreStart k n C eta P.tailScale)
    (S : IndexedUniformCoreSeedStage P A.cleaned A.goodSet
      (C.redDegree A.seed : ℝ))
    (i : Fin (delta k))
    (hn : ⌈(4 * P.master + 2) / P.tau⌉₊ ≤ n) :
    ∃ v, v ∈ S.stage.typical i := by
  classical
  have herror :=
    P.levelError_le_tau_mul_add_master (n := n) heta S.level.succ
  have hmain := A.hundred_tau_mul_le_seed_red_div_delta hk P
  have hthreshold := P.four_master_add_two_le_tau_mul hn
  have hbalanced := (abs_le.mp (S.stage.typicalBalanced i)).1
  have hlower :
      99 * P.tau * (n : ℝ) - P.master ≤
        ((S.stage.typical i).card : ℝ) := by
    linarith
  have hlowerPos :
      0 < 99 * P.tau * (n : ℝ) - P.master := by
    linarith [P.master_pos]
  have hcardPos : 0 < ((S.stage.typical i).card : ℝ) := by
    exact hlowerPos.trans_le hlower
  have hcardPosNat : 0 < (S.stage.typical i).card := by
    exact_mod_cast hcardPos
  exact Finset.card_pos.mp hcardPosNat

/-- Any valid run of length at least two has a genuine second stage.  Its
new-mass estimate is measured only against the initial neighborhood. -/
theorem StageRunValid.exists_second_stage
    {S V : Type*} [DecidableEq V]
    {initial : S} {eligible : List S → S → Prop}
    {neighborhood : S → Finset V} {newMass : ℕ} {run : List S}
    (hrun : StageRunValid initial eligible neighborhood newMass run)
    (htwo : 2 ≤ run.length) :
    ∃ second tail,
      run = initial :: second :: tail ∧
      eligible [initial] second ∧
      newMass ≤ (neighborhood second \ neighborhood initial).card := by
  induction hrun with
  | singleton => simp at htwo
  | @append priorRun next hprior hnext ih =>
      by_cases hone : priorRun.length = 1
      · obtain ⟨first, hpriorEq⟩ := List.length_eq_one_iff.mp hone
        have hhead := BoundedRunValid.head?_eq hprior
        rw [hpriorEq] at hhead
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst first
        rw [hpriorEq] at hnext
        refine ⟨next, [], ?_, hnext.1, ?_⟩
        · simp [hpriorEq]
        · simpa [stageHasNewMass, hpriorEq] using hnext.2
      · have hpriorNonempty : priorRun ≠ [] :=
          BoundedRunValid.nonempty hprior
        have hpriorPos : 0 < priorRun.length :=
          List.length_pos_iff.mpr hpriorNonempty
        have hpriorTwo : 2 ≤ priorRun.length := by omega
        obtain ⟨second, tail, hpriorEq, heligible, hmass⟩ := ih hpriorTwo
        refine ⟨second, tail ++ [next], ?_, heligible, hmass⟩
        simp [hpriorEq]

/-- The concrete data produced by the bounded F3 seed iteration. -/
structure CleanedCoreSeedRunCertificate
    {k n : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta)
    {C : ColoredGraph (Fin n)} (A : CleanedCoreStart k n C eta P.tailScale) where
  initial : IndexedCoreSeedStage (P := P) (C := A.cleaned)
    (control := A.goodSet) (reference := (C.redDegree A.seed : ℝ))
  initial_level : initial.level.val = 0
  initial_seed : initial.stage.seed = A.seed
  run : List (IndexedCoreSeedStage (P := P) (C := A.cleaned)
    (control := A.goodSet) (reference := (C.redDegree A.seed : ℝ)))
  valid : StageRunValid initial indexedCoreSeedStageEligible
    (fun S ↦ S.stage.redNeighborhood) ⌈P.tau * (n : ℝ)⌉₊ run
  length_le : run.length ≤ P.stageBound - 1
  levels_eq_range :
    run.map (fun S ↦ S.level.val) = List.range run.length
  terminalStop : ∀ v ∈ A.goodSet,
    v ∈ indexedStageRunTypicalUnion run →
      (A.cleaned.redNeighborFinset v \
          indexedStageRunRedNeighborhoodUnion run).card <
        ⌈P.tau * (n : ℝ)⌉₊
  covered_subset_retained :
    indexedStageRunRedNeighborhoodUnion run ⊆ A.retained
  typical_subset_goodSet :
    indexedStageRunTypicalUnion run ⊆ A.goodSet
  terminalNonblueCap : ∀ S ∈ run,
    S.stage.internalNonblueCap ≤
      coreSeedNonblueCap (P.betaSeq (Fin.last P.stageBound)) n
  redUnion_terminalStages :
    stageNeighborhoodUnion
        (fun S : UniformCoreSeedStage k A.cleaned A.goodSet
          (C.redDegree A.seed : ℝ) (P.terminalError n) ↦ S.redNeighborhood)
        (indexedRunTerminalStages run) =
      indexedStageRunRedNeighborhoodUnion run
  typicalUnion_terminalStages :
    stageNeighborhoodUnion
        (fun S : UniformCoreSeedStage k A.cleaned A.goodSet
            (C.redDegree A.seed : ℝ) (P.terminalError n) ↦
          (Finset.univ : Finset (Fin (delta k))).biUnion S.typical)
        (indexedRunTerminalStages run) =
      indexedStageRunTypicalUnion run

/-- The second entry of a nontrivial cleaned run is at level one, is seeded
in one of the initial typical parts (hence in the corresponding old part and
old red neighborhood), and contributes the prescribed new red mass. -/
theorem CleanedCoreSeedRunCertificate.exists_second_stage
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A) (htwo : 2 ≤ R.run.length) :
    ∃ second tail i,
      R.run = R.initial :: second :: tail ∧
      second.level.val = 1 ∧
      second.stage.seed ∈ A.goodSet ∧
      second.stage.seed ∈ R.initial.stage.typical i ∧
      second.stage.seed ∈ R.initial.stage.parts i ∧
      second.stage.seed ∈ R.initial.stage.redNeighborhood ∧
      ⌈P.tau * (n : ℝ)⌉₊ ≤
        (second.stage.redNeighborhood \
          R.initial.stage.redNeighborhood).card := by
  classical
  obtain ⟨second, tail, hrun, heligible, hmass⟩ :=
    StageRunValid.exists_second_stage R.valid htwo
  change second.level.val = [R.initial].length ∧
      second.stage.seed ∈ A.goodSet ∧
      second.stage.seed ∈ indexedStageRunTypicalUnion [R.initial] at heligible
  rcases heligible with ⟨hlevel, hcontrol, htypical⟩
  have htypical' : second.stage.seed ∈
      (Finset.univ : Finset (Fin (delta k))).biUnion
        R.initial.stage.typical := by
    simpa [indexedStageRunTypicalUnion,
      IndexedUniformCoreSeedStage.typicalUnion] using htypical
  obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp htypical'
  have hvPart := R.initial.stage.typical_subset_part i hvi
  have hvRed : second.stage.seed ∈ R.initial.stage.redNeighborhood := by
    rw [← R.initial.stage.parts_cover]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hvPart⟩
  refine ⟨second, tail, i, hrun, ?_, hcontrol, hvi, hvPart, hvRed, ?_⟩
  · simpa using hlevel
  · simpa using hmass

/-- One typical vertex of the initial stage forces the maximal run to append
a second stage: its red mass outside the initial neighborhood meets the
continuation threshold, contradicting terminal stopping at a singleton. -/
theorem CleanedCoreSeedRunCertificate.two_le_length_of_initial_typical
    {k n : ℕ} {eta zeta : ℝ} (hk : 3 ≤ k)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A)
    (i : Fin (delta k)) (v : Fin n)
    (hv : v ∈ R.initial.stage.typical i)
    (hn : ⌈(4 * P.master + 2) / P.tau⌉₊ ≤ n) :
    2 ≤ R.run.length := by
  classical
  by_contra htwo
  have hnonempty : R.run ≠ [] := BoundedRunValid.nonempty R.valid
  have hpositive : 0 < R.run.length := List.length_pos_iff.mpr hnonempty
  have hone : R.run.length = 1 := by omega
  obtain ⟨only, hrun⟩ := List.length_eq_one_iff.mp hone
  have hhead := BoundedRunValid.head?_eq R.valid
  rw [hrun] at hhead
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst only
  have htypicalRun : v ∈ indexedStageRunTypicalUnion R.run := by
    rw [hrun]
    simp only [indexedStageRunTypicalUnion, stageNeighborhoodUnion_cons,
      stageNeighborhoodUnion_nil, Finset.union_empty]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩
  have hstop := R.terminalStop v
    (R.initial.stage.typical_controlled i hv) htypicalRun
  have hlower :=
    R.initial.newMass_le_redDegreeOutside hk heta P A i v hv hn
  rw [hrun] at hstop
  simp only [indexedStageRunRedNeighborhoodUnion,
    stageNeighborhoodUnion_cons, stageNeighborhoodUnion_nil,
    Finset.union_empty] at hstop
  omega

/-- A concrete maximal cleaned run has at least two stages once the explicit
additive-error threshold is met. -/
theorem CleanedCoreSeedRunCertificate.two_le_length
    {k n : ℕ} {eta zeta : ℝ} (hk : 3 ≤ k)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A)
    (hn : ⌈(4 * P.master + 2) / P.tau⌉₊ ≤ n) :
    2 ≤ R.run.length := by
  let i : Fin (delta k) :=
    ⟨0, by unfold delta; omega⟩
  obtain ⟨v, hv⟩ := R.initial.exists_mem_typical hk heta P A i hn
  exact R.two_le_length_of_initial_typical hk heta i v hv hn

/-- The level-one stage supplies an overlap class beyond the `Δ` distinct
classes already supplied by the initial stage.  This is the direct bridge
from the concrete run's new-mass certificate to the terminal quotient's
`Δ + 1` class count. -/
theorem CleanedCoreSeedRunCertificate.delta_add_one_le_terminalOverlapClassCount
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A) (htwo : 2 ≤ R.run.length)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run))
    (hmass : uniformStageNewClassThreshold B <
      ⌈P.tau * (n : ℝ)⌉₊) :
    delta k + 1 ≤ overlapClassCount
      (uniformStageTypical (indexedRunTerminalStages R.run))
      B.overlapError := by
  classical
  obtain ⟨second, tail, iSeed, hrun, hlevel, hcontrol,
      htypical, hpart, hred, hnewMass⟩ := R.exists_second_stage htwo
  let terminalRun := indexedRunTerminalStages R.run
  have hzero : 0 < terminalRun.length := by
    simp only [terminalRun, indexedRunTerminalStages_length]
    omega
  have hone : 1 < terminalRun.length := by
    simp only [terminalRun, indexedRunTerminalStages_length]
    omega
  let q₀ : Fin terminalRun.length := ⟨0, hzero⟩
  let q₁ : Fin terminalRun.length := ⟨1, hone⟩
  have hstage₀ : uniformStageAt terminalRun q₀ =
      R.initial.terminalStage := by
    simp [terminalRun, q₀, uniformStageAt, indexedRunTerminalStages, hrun]
  have hstage₁ : uniformStageAt terminalRun q₁ =
      second.terminalStage := by
    simp [terminalRun, q₁, uniformStageAt, indexedRunTerminalStages, hrun]
  let old : Finset (UniformStagePartIndex terminalRun) :=
    Finset.univ.image (fun i : Fin (delta k) ↦ (q₀, i))
  have hold : ∀ j ∈ old,
      uniformStageTypical terminalRun j ⊆
        R.initial.stage.redNeighborhood := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    intro v hv
    have hvInitial : v ∈ R.initial.stage.typical i := by
      change v ∈ (uniformStageAt terminalRun q₀).typical i at hv
      rw [hstage₀] at hv
      exact hv
    have hvPart := R.initial.stage.typical_subset_part i hvInitial
    rw [← R.initial.stage.parts_cover]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hvPart⟩
  have hnew : ⌈P.tau * (n : ℝ)⌉₊ ≤
      ((uniformStageAt terminalRun q₁).redNeighborhood \
        R.initial.stage.redNeighborhood).card := by
    rw [hstage₁]
    exact hnewMass
  obtain ⟨iNew, hnewClass⟩ :=
    uniformStage_exists_newOverlapClass_of_newMass B q₁ old
      R.initial.stage.redNeighborhood ⌈P.tau * (n : ℝ)⌉₊
      hold hnew hmass
  apply delta_add_one_le_uniformStageOverlapClassCount_of_newClass
    B q₀ (q₁, iNew)
  intro i
  exact hnewClass (q₀, i)
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The union of all parts of a uniform stage list is exactly the union of
the stages' red neighborhoods. -/
theorem uniformStageAmbientUnion_eq_stageNeighborhoodUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} {C : ColoredGraph V} {control : Finset V}
    {reference error : ℝ}
    (run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)) :
    uniformStageAmbientUnion run =
      stageNeighborhoodUnion (fun S ↦ S.redNeighborhood) run := by
  ext v
  rw [uniformStageAmbientUnion, mem_stageNeighborhoodUnion_iff]
  constructor
  · intro hv
    obtain ⟨a, ha, hva⟩ := Finset.mem_biUnion.mp hv
    rcases a with ⟨q, i⟩
    have hvPart : v ∈ (uniformStageAt run q).parts i := by
      simpa only [uniformStagePart] using hva
    have hvRed : v ∈ (uniformStageAt run q).redNeighborhood := by
      rw [← (uniformStageAt run q).parts_cover]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hvPart⟩
    exact ⟨uniformStageAt run q, List.get_mem run q, hvRed⟩
  · rintro ⟨S, hS, hvRed⟩
    obtain ⟨q, hq⟩ :=
      (List.exists_mem_iff_get
        (l := run) (p := fun T ↦ v ∈ T.redNeighborhood)).mp
        ⟨S, hS, hvRed⟩
    change v ∈ (uniformStageAt run q).redNeighborhood at hq
    rw [← (uniformStageAt run q).parts_cover] at hq
    obtain ⟨i, hi, hvPart⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_biUnion.mpr
      ⟨(q, i), Finset.mem_univ (q, i), by
        simpa only [uniformStagePart] using hvPart⟩

/-- Terminal erasure identifies the quotient ambient set with the exact red
neighborhood union covered by the indexed run. -/
theorem uniformStageAmbientUnion_indexedRunTerminalStages
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)} {control : Finset (Fin n)}
    {reference : ℝ}
    (run : List (IndexedUniformCoreSeedStage P C control reference)) :
    uniformStageAmbientUnion (indexedRunTerminalStages run) =
      indexedStageRunRedNeighborhoodUnion run := by
  calc
    uniformStageAmbientUnion (indexedRunTerminalStages run) =
        stageNeighborhoodUnion
          (fun S : UniformCoreSeedStage k C control reference
            (P.terminalError n) ↦ S.redNeighborhood)
          (indexedRunTerminalStages run) :=
      uniformStageAmbientUnion_eq_stageNeighborhoodUnion _
    _ = indexedStageRunRedNeighborhoodUnion run :=
      stageNeighborhoodUnion_indexedRunTerminalStages run

/-- Certificate-facing name for the exact ambient/covered identity. -/
theorem CleanedCoreSeedRunCertificate.terminalAmbientUnion_eq_covered
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A) :
    uniformStageAmbientUnion (indexedRunTerminalStages R.run) =
      indexedStageRunRedNeighborhoodUnion R.run :=
  uniformStageAmbientUnion_indexedRunTerminalStages R.run

/-- Every terminal quotient cluster remains inside the exact set covered by
the indexed seed run. -/
theorem CleanedCoreSeedRunCertificate.terminalFinalUnion_subset_covered
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run)) :
    uniformStageFinalUnion B ⊆ indexedStageRunRedNeighborhoodUnion R.run := by
  rw [← R.terminalAmbientUnion_eq_covered]
  exact uniformStageFinalUnion_subset_ambientUnion B

/-- The generic core-extraction cluster union is definitionally the terminal
quotient's final union when the clusters are `uniformStageFinalClusters`. -/
theorem coreExtractionClusterUnion_uniformStageFinalClusters
    {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} {C : ColoredGraph V} {control : Finset V}
    {reference error : ℝ}
    {run : UniformStageList (k := k) (C := C) (control := control)
      (reference := reference) (error := error)}
    (B : UniformStageOverlapBounds run) :
    coreExtractionClusterUnion (uniformStageFinalClusters B) =
      uniformStageFinalUnion B := rfl

/-- Removing the terminal quotient loss from the covered-cardinality count
leaves no more than the final union itself. -/
theorem CleanedCoreSeedRunCertificate.covered_card_sub_loss_le_finalUnion_card
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run)) :
    (indexedStageRunRedNeighborhoodUnion R.run).card -
        (indexedStageRunRedNeighborhoodUnion R.run \
          uniformStageFinalUnion B).card ≤
      (uniformStageFinalUnion B).card := by
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (R.terminalFinalUnion_subset_covered B)
  omega

/-- Real-valued form of the exact covered-versus-final cardinality bridge. -/
theorem CleanedCoreSeedRunCertificate.covered_card_sub_loss_le_finalUnion_card_real
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run)) :
    ((indexedStageRunRedNeighborhoodUnion R.run).card : ℝ) -
        ((indexedStageRunRedNeighborhoodUnion R.run \
          uniformStageFinalUnion B).card : ℝ) ≤
      ((uniformStageFinalUnion B).card : ℝ) := by
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (R.terminalFinalUnion_subset_covered B)
  have hsplitReal :
      ((indexedStageRunRedNeighborhoodUnion R.run \
          uniformStageFinalUnion B).card : ℝ) +
        ((uniformStageFinalUnion B).card : ℝ) =
          ((indexedStageRunRedNeighborhoodUnion R.run).card : ℝ) := by
    exact_mod_cast hsplit
  linarith

/-- Every vertex of a terminal quotient cluster belongs to the typical-set
union of the original indexed run. -/
theorem CleanedCoreSeedRunCertificate.terminalFinalCluster_subset_typicalUnion
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run))
    (q : Fin (overlapClassCount
      (uniformStageTypical (indexedRunTerminalStages R.run)) B.overlapError)) :
    uniformStageFinalClusters B q ⊆ indexedStageRunTypicalUnion R.run := by
  rw [← R.typicalUnion_terminalStages]
  intro v hv
  let a := uniformStageFinalClusterSource B q
  have hvTypical : v ∈ uniformStageTypical
      (indexedRunTerminalStages R.run) a :=
    uniformStageFinalCluster_subset_sourceTypical B q hv
  rw [mem_stageNeighborhoodUnion_iff]
  refine ⟨uniformStageAt (indexedRunTerminalStages R.run) a.1,
    List.get_mem _ _, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨a.2, Finset.mem_univ _, hvTypical⟩

/-- Terminal stopping and the exact covered-to-final loss bound the red
degree of a final-cluster vertex into the complement of the final union. -/
theorem CleanedCoreSeedRunCertificate.terminalFinalUnion_compl_redDegree_le
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run))
    (q : Fin (overlapClassCount
      (uniformStageTypical (indexedRunTerminalStages R.run)) B.overlapError))
    {v : Fin n} (hv : v ∈ uniformStageFinalClusters B q) :
    (A.cleaned.redDegreeIn v (uniformStageFinalUnion B)ᶜ : ℝ) ≤
      P.tau * (n : ℝ) + 1 +
        ((uniformStageAmbientUnion (indexedRunTerminalStages R.run) \
          uniformStageFinalUnion B).card : ℝ) := by
  let ambient := uniformStageAmbientUnion (indexedRunTerminalStages R.run)
  let final := uniformStageFinalUnion B
  have hvGood : v ∈ A.goodSet :=
    uniformStageFinalCluster_subset_control B q hv
  have hvTypical : v ∈ indexedStageRunTypicalUnion R.run :=
    R.terminalFinalCluster_subset_typicalUnion B q hv
  have hstop := R.terminalStop v hvGood hvTypical
  have houtsideEq :
      A.cleaned.redDegreeIn v ambientᶜ =
        (A.cleaned.redNeighborFinset v \ ambient).card := by
    change (A.cleaned.redNeighborFinset v ∩ ambientᶜ).card =
      (A.cleaned.redNeighborFinset v \ ambient).card
    congr 1
    ext w
    simp
  have houtsideNat : A.cleaned.redDegreeIn v ambientᶜ <
      ⌈P.tau * (n : ℝ)⌉₊ := by
    rw [houtsideEq]
    dsimp only [ambient]
    rw [R.terminalAmbientUnion_eq_covered]
    exact hstop
  have htarget : finalᶜ ⊆ ambientᶜ ∪ (ambient \ final) := by
    intro w hw
    by_cases hwAmbient : w ∈ ambient
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hwAmbient, by simpa [final] using hw⟩)
    · exact Finset.mem_union_left _ (by simpa using hwAmbient)
  have hdegreeNat : A.cleaned.redDegreeIn v finalᶜ ≤
      A.cleaned.redDegreeIn v ambientᶜ + (ambient \ final).card :=
    degreeIn_le_degreeIn_add_card_of_subset_union A.cleaned .red v htarget
  have hdegree : (A.cleaned.redDegreeIn v finalᶜ : ℝ) ≤
      (A.cleaned.redDegreeIn v ambientᶜ : ℝ) +
        ((ambient \ final).card : ℝ) := by
    exact_mod_cast hdegreeNat
  have houtside : (A.cleaned.redDegreeIn v ambientᶜ : ℝ) <
      P.tau * (n : ℝ) + 1 := by
    have hcast : (A.cleaned.redDegreeIn v ambientᶜ : ℝ) <
        ((⌈P.tau * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast houtsideNat
    exact hcast.trans (Nat.ceil_lt_add_one
      (mul_nonneg P.tau_pos.le (Nat.cast_nonneg n)))
  dsimp only [ambient, final] at hdegree ⊢
  linarith

/-- Assemble the cleaned initial stage and every subsequent eligible stage
into one maximal indexed run.  The threshold is uniform in the hierarchy
level; `newMass` and the run bound are the paper's concrete choices
`⌈τ n⌉` and `stageBound - 1`. -/
theorem exists_cleanedCoreSeedRunCertificate
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n),
      ∀ A : CleanedCoreStart k n C eta P.tailScale,
        Nonempty (CleanedCoreSeedRunCertificate P A) := by
  classical
  obtain ⟨nRealize, hrealize⟩ :=
    exists_uniformIndexedCoreSeedStage_atLevel k hk eta heta P
  obtain ⟨nInitial, hinitial⟩ :=
    exists_initialIndexedUniformCoreSeedStage k hk eta heta P
  let nError : ℕ := ⌈(8 * P.master) / eta⌉₊
  let n₀ : ℕ := max nRealize (max nInitial (max nError 1))
  refine ⟨n₀, ?_⟩
  intro n hn C A
  have hnRealize : nRealize ≤ n :=
    (le_max_left _ _).trans hn
  have hnInitial : nInitial ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnError : nError ≤ n :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnOne : 1 ≤ n :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnPos : 0 < n := by omega
  have hterminalError :
      P.terminalError n ≤ (eta / 4) * (n : ℝ) := by
    apply P.terminalError_le_eta_quarter_mul heta
    simpa [nError] using hnError
  obtain ⟨initial, hinitialLevel, hinitialSeed⟩ :=
    hinitial n hnInitial C A
  have hinitialZero : initial.level.val = 0 := by
    simpa [hinitialLevel]
  have hstageTwo : 2 ≤ P.stageBound := by
    have hratioPos : 0 < P.master / P.tau :=
      div_pos P.master_pos P.tau_pos
    have : (1 : ℝ) < (P.stageBound : ℕ) := by
      linarith [P.stageBound_covers]
    exact_mod_cast this
  have hLPos : 0 < P.stageBound - 1 := by omega
  have hLBound : P.stageBound - 1 < P.stageBound := by omega
  have hcapacity :
      n < (P.stageBound - 1) * ⌈P.tau * (n : ℝ)⌉₊ :=
    P.card_lt_stageBound_sub_one_mul_ceil hnPos
  obtain ⟨run, hvalid, hlength, hlevels, hstop⟩ :=
    exists_maximal_indexedCoreSeedStageRun_and_stop_of_valid_realize
      initial hinitialZero ⌈P.tau * (n : ℝ)⌉₊ (P.stageBound - 1)
      hLPos hLBound hcapacity (by
        intro q runPrefix hprefix v hprefixLength hvGood hvTypical
        rw [indexedStageRunTypicalUnion,
          mem_stageNeighborhoodUnion_iff] at hvTypical
        obtain ⟨prior, hpriorMem, hvPrior⟩ := hvTypical
        rw [IndexedUniformCoreSeedStage.typicalUnion] at hvPrior
        obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvPrior
        have hprefixLevels :=
          indexedCoreSeedStageRun_levels_eq_range initial hinitialZero hprefix
        have hpriorLevelMem : prior.level.val ∈
            runPrefix.map (fun S ↦ S.level.val) :=
          List.mem_map.mpr ⟨prior, hpriorMem, rfl⟩
        rw [hprefixLevels] at hpriorLevelMem
        have hpriorLevelLt : prior.level.val < runPrefix.length := by
          simpa using hpriorLevelMem
        have hlevelLe : prior.level.succ ≤ q.castSucc := by
          change prior.level.val + 1 ≤ q.val
          omega
        have herrorLe : P.levelError prior.level.succ n ≤
            P.levelError q.castSucc n :=
          P.levelError_mono hlevelLe n
        have hhigh := prior.stage.highTotalRed i v hvi
        have hseedLower :
            (C.redDegree A.seed : ℝ) - P.levelError q.castSucc n ≤
              (A.cleaned.redDegree v : ℝ) :=
          (sub_le_sub_left herrorLe (C.redDegree A.seed : ℝ)).trans hhigh
        have href : eta * (n : ℝ) ≤ (C.redDegree A.seed : ℝ) :=
          A.seed_red_lower
        have hcurrentTerminal : P.levelError q.castSucc n ≤
            P.terminalError n := P.levelError_le_terminal q.castSucc n
        have hetaN : 0 ≤ eta * (n : ℝ) :=
          mul_nonneg heta.1.le (Nat.cast_nonneg n)
        have hseedLarge : (eta / 4) * (n : ℝ) ≤
            (A.cleaned.redDegree v : ℝ) := by
          linarith
        exact hrealize q n hnRealize C A v hseedLower hseedLarge)
  have hcovered : indexedStageRunRedNeighborhoodUnion run ⊆ A.retained := by
    intro v hv
    rw [indexedStageRunRedNeighborhoodUnion,
      mem_stageNeighborhoodUnion_iff] at hv
    obtain ⟨S, hSRun, hvS⟩ := hv
    rw [S.stage.redNeighborhood_eq] at hvS
    exact A.cleaned_redNeighborFinset_subset_retained S.stage.seed hvS
  have htypical : indexedStageRunTypicalUnion run ⊆ A.goodSet := by
    intro v hv
    rw [indexedStageRunTypicalUnion,
      mem_stageNeighborhoodUnion_iff] at hv
    obtain ⟨S, hSRun, hvS⟩ := hv
    exact S.typicalUnion_subset_control hvS
  exact ⟨{
    initial := initial
    initial_level := hinitialZero
    initial_seed := hinitialSeed
    run := run
    valid := hvalid
    length_le := hlength
    levels_eq_range := hlevels
    terminalStop := hstop
    covered_subset_retained := hcovered
    typical_subset_goodSet := htypical
    terminalNonblueCap := fun S hS ↦ S.terminalNonblueCap
    redUnion_terminalStages :=
      stageNeighborhoodUnion_indexedRunTerminalStages run
    typicalUnion_terminalStages :=
      typicalUnion_indexedRunTerminalStages run
  }⟩

/-- Strengthened concrete assembly: the returned maximal run is nontrivial,
so `CleanedCoreSeedRunCertificate.exists_second_stage` immediately exposes
its level-one stage and its `⌈τ n⌉` new red mass. -/
theorem exists_nontrivial_cleanedCoreSeedRunCertificate
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n),
      ∀ A : CleanedCoreStart k n C eta P.tailScale,
        ∃ R : CleanedCoreSeedRunCertificate P A, 2 ≤ R.run.length := by
  obtain ⟨nBase, hbase⟩ :=
    exists_cleanedCoreSeedRunCertificate k hk eta heta P
  refine ⟨max nBase ⌈(4 * P.master + 2) / P.tau⌉₊, ?_⟩
  intro n hn C A
  have hnBase : nBase ≤ n := (le_max_left _ _).trans hn
  have hnTwo : ⌈(4 * P.master + 2) / P.tau⌉₊ ≤ n :=
    (le_max_right _ _).trans hn
  obtain ⟨R⟩ := hbase n hnBase C A
  exact ⟨R, R.two_le_length hk heta hnTwo⟩

/-! ### Terminal error budgets -/

/-- The ambient threshold needed after the terminal quotient.  Its first
term absorbs the ceiling and the additive master-constant in the pointwise
boundary estimate; its second term absorbs the linear Mantel error on the
transparent core. -/
noncomputable def CoreExtractionParameters.terminalBudgetThreshold
    {k : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta) : ℕ :=
  max ⌈(P.master + 1) / P.tau⌉₊ ⌈(delta k : ℝ) / zeta⌉₊

/-- The output error parameter is positive already from the continuation
scale reserve. -/
theorem CoreExtractionParameters.zeta_pos
    {k : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    0 < zeta := by
  have hprod : 0 < P.master * P.tau :=
    mul_pos P.master_pos P.tau_pos
  nlinarith [P.master_mul_tau_lt_zeta]

/-- The fixed deleted-tail coefficient fits in one `zeta / 100` slot. -/
theorem CoreExtractionParameters.betaSeq_zero_fourth_lt_zeta_slot
    {k : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    (P.betaSeq 0) ^ 4 < zeta / 100 := by
  have hbetaPos : 0 < P.betaSeq 0 := P.betaSeq_pos 0
  have hbetaOne : P.betaSeq 0 ≤ 1 := (P.betaSeq_lt_one 0).le
  have hsqLe : (P.betaSeq 0) ^ 2 ≤ P.betaSeq 0 := by
    nlinarith [mul_nonneg hbetaPos.le (sub_nonneg.mpr hbetaOne)]
  have hsqOne : (P.betaSeq 0) ^ 2 ≤ 1 := hsqLe.trans hbetaOne
  have hfourthLeSq : ((P.betaSeq 0) ^ 2) ^ 2 ≤
      (P.betaSeq 0) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (P.betaSeq 0))
      (sub_nonneg.mpr hsqOne)]
  have hfourthLe : (P.betaSeq 0) ^ 4 ≤ P.betaSeq 0 := by
    nlinarith
  exact (hfourthLe.trans_lt (P.betaSeq_lt_tau 0)).trans P.tau_lt_zeta

/-- The five terminal estimates consumed by the F9 geometry constructor.

The three actual error sources—deleted vertices, quotient loss, and the
pointwise red--blue boundary—are each allocated only `zeta / 100`.  The last
field is the eventual absorption of the linear kth-order Mantel term on the
transparent core `retainedᶜ ∪ covered`. -/
structure CoreExtractionTerminalBudgetCertificate
    {k n : ℕ} {eta zeta : ℝ} (P : CoreExtractionParameters k eta zeta)
    {C : ColoredGraph (Fin n)} (A : CleanedCoreStart k n C eta P.tailScale)
    (R : CleanedCoreSeedRunCertificate P A)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run)) where
  retainedComplementSmall :
    (A.retainedᶜ.card : ℝ) ≤ (zeta / 100) * (n : ℝ)
  uncoveredSmall :
    ((indexedStageRunRedNeighborhoodUnion R.run \
        uniformStageFinalUnion B).card : ℝ) ≤
      (zeta / 100) * (n : ℝ)
  finalUnionLarge :
    (eta - 3 * zeta) * (n : ℝ) ≤
      (uniformStageFinalUnion B).card
  cleanedBoundaryPointwise : ∀ v ∈ uniformStageFinalUnion B,
    (A.cleaned.redDegreeIn v
          (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) +
        (A.cleaned.blueDegreeIn v
          (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) ≤
      (zeta / 100) * (n : ℝ)
  threeErrorSlots_le :
    zeta / 100 + zeta / 100 + zeta / 100 ≤ zeta
  coreMantelAbsorbed :
    (((delta k *
        (A.retainedᶜ ∪ indexedStageRunRedNeighborhoodUnion R.run).card /
          2 : ℕ) : ℝ)) ≤
      zeta * (n : ℝ) ^ 2

/-- The initial seed neighborhood is contained in the red-neighborhood union
recorded by a valid cleaned run. -/
theorem CleanedCoreSeedRunCertificate.initial_redNeighborhood_subset_covered
    {k n : ℕ} {eta zeta : ℝ} {P : CoreExtractionParameters k eta zeta}
    {C : ColoredGraph (Fin n)}
    {A : CleanedCoreStart k n C eta P.tailScale}
    (R : CleanedCoreSeedRunCertificate P A) :
    R.initial.stage.redNeighborhood ⊆
      indexedStageRunRedNeighborhoodUnion R.run := by
  classical
  have hhead := BoundedRunValid.head?_eq R.valid
  cases hrun : R.run with
  | nil =>
      rw [hrun] at hhead
      simp at hhead
  | cons first tail =>
      rw [hrun] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst first
      simp [indexedStageRunRedNeighborhoodUnion]

/-- A single explicit large-`n` threshold supplies every terminal budget.
The ambient-loss hypothesis is exactly the final estimate returned by
`exists_terminalQuotient_of_indexedRun`. -/
theorem coreExtractionTerminalBudgetCertificate_of_large
    {k n : ℕ} (hk : 3 ≤ k) {eta zeta : ℝ}
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k eta zeta)
    {C : ColoredGraph (Fin n)}
    (A : CleanedCoreStart k n C eta P.tailScale)
    (R : CleanedCoreSeedRunCertificate P A)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run))
    (hn : P.terminalBudgetThreshold ≤ n)
    (hambient :
      ((uniformStageAmbientUnion (indexedRunTerminalStages R.run) \
          uniformStageFinalUnion B).card : ℝ) ≤
        P.master * P.tau * (n : ℝ) / 100) :
    CoreExtractionTerminalBudgetCertificate P A R B := by
  classical
  have hzeta : 0 < zeta := P.zeta_pos
  have hnNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hretained : (A.retainedᶜ.card : ℝ) ≤
      (zeta / 100) * (n : ℝ) := by
    calc
      (A.retainedᶜ.card : ℝ) =
          ((Finset.univ \ A.retained).card : ℝ) := by
            rw [Finset.compl_eq_univ_sdiff]
      _ ≤ (P.betaSeq 0) ^ 4 * (n : ℝ) :=
        A.deleted_le_betaSeq_zero_fourth_mul P
      _ ≤ (zeta / 100) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right
          (P.betaSeq_zero_fourth_lt_zeta_slot.le) hnNonneg
  have huncoveredRaw :
      ((indexedStageRunRedNeighborhoodUnion R.run \
          uniformStageFinalUnion B).card : ℝ) ≤
        P.master * P.tau * (n : ℝ) / 100 := by
    rw [← R.terminalAmbientUnion_eq_covered]
    exact hambient
  have huncovered :
      ((indexedStageRunRedNeighborhoodUnion R.run \
          uniformStageFinalUnion B).card : ℝ) ≤
        (zeta / 100) * (n : ℝ) := by
    have hcoeff : P.master * P.tau / 100 ≤ zeta / 100 := by
      nlinarith [P.master_mul_tau_lt_zeta]
    calc
      ((indexedStageRunRedNeighborhoodUnion R.run \
          uniformStageFinalUnion B).card : ℝ) ≤
          P.master * P.tau * (n : ℝ) / 100 := huncoveredRaw
      _ = (P.master * P.tau / 100) * (n : ℝ) := by ring
      _ ≤ (zeta / 100) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff hnNonneg
  have hseedCard : R.initial.stage.redNeighborhood.card =
      A.cleaned.redDegree A.seed := by
    rw [R.initial.stage.redNeighborhood_eq, R.initial_seed]
    rfl
  have hseedCardReal :
      (R.initial.stage.redNeighborhood.card : ℝ) =
        (A.cleaned.redDegree A.seed : ℝ) := by
    exact_mod_cast hseedCard
  have hinitialCardNat : R.initial.stage.redNeighborhood.card ≤
      (indexedStageRunRedNeighborhoodUnion R.run).card :=
    Finset.card_le_card R.initial_redNeighborhood_subset_covered
  have hinitialCard :
      (R.initial.stage.redNeighborhood.card : ℝ) ≤
        ((indexedStageRunRedNeighborhoodUnion R.run).card : ℝ) := by
    exact_mod_cast hinitialCardNat
  have hsplitNat := Finset.card_sdiff_add_card_eq_card
    (R.terminalFinalUnion_subset_covered B)
  have hsplit :
      ((indexedStageRunRedNeighborhoodUnion R.run \
          uniformStageFinalUnion B).card : ℝ) +
        ((uniformStageFinalUnion B).card : ℝ) =
          ((indexedStageRunRedNeighborhoodUnion R.run).card : ℝ) := by
    exact_mod_cast hsplitNat
  have hfinalLarge : (eta - 3 * zeta) * (n : ℝ) ≤
      ((uniformStageFinalUnion B).card : ℝ) := by
    have hseedLower := A.cleaned_seed_red_lower
    have hdeletedEq :
        ((Finset.univ \ A.retained).card : ℝ) =
          (A.retainedᶜ.card : ℝ) := by
      rw [Finset.compl_eq_univ_sdiff]
    rw [hdeletedEq] at hseedLower
    nlinarith
  have hnBoundary : ⌈(P.master + 1) / P.tau⌉₊ ≤ n := by
    exact (le_max_left _ _).trans (by
      simpa only [CoreExtractionParameters.terminalBudgetThreshold] using hn)
  have hceilBoundary : (P.master + 1) / P.tau ≤
      (⌈(P.master + 1) / P.tau⌉₊ : ℕ) := Nat.le_ceil _
  have hnBoundaryReal :
      ((⌈(P.master + 1) / P.tau⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnBoundary
  have habsorb : P.master + 1 ≤ P.tau * (n : ℝ) := by
    have hratio := hceilBoundary.trans hnBoundaryReal
    have := (div_le_iff₀ P.tau_pos).mp hratio
    nlinarith
  have hterminalError : P.terminalError n ≤
      P.tau * (n : ℝ) + P.master := by
    simpa only [CoreExtractionParameters.terminalError] using
      P.levelError_le_tau_mul_add_master (n := n) heta
        (Fin.last P.stageBound)
  have hboundary : ∀ v ∈ uniformStageFinalUnion B,
      (A.cleaned.redDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) +
          (A.cleaned.blueDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) ≤
        (zeta / 100) * (n : ℝ) := by
    intro v hvFinal
    obtain ⟨q, hq, hvq⟩ := Finset.mem_biUnion.mp hvFinal
    let a := uniformStageFinalClusterSource B q
    have hvTypical : v ∈
        uniformStageTypical (indexedRunTerminalStages R.run) a :=
      uniformStageFinalCluster_subset_sourceTypical B q hvq
    have hvGood : v ∈ A.goodSet :=
      uniformStageFinalCluster_subset_control B q hvq
    have hvTypicalTerminal : v ∈
        stageNeighborhoodUnion
          (fun S : UniformCoreSeedStage k A.cleaned A.goodSet
              (C.redDegree A.seed : ℝ) (P.terminalError n) ↦
            (Finset.univ : Finset (Fin (delta k))).biUnion S.typical)
          (indexedRunTerminalStages R.run) := by
      rw [mem_stageNeighborhoodUnion_iff]
      refine ⟨uniformStageAt (indexedRunTerminalStages R.run) a.1,
        List.get_mem _ _, ?_⟩
      exact Finset.mem_biUnion.mpr
        ⟨a.2, Finset.mem_univ _, hvTypical⟩
    have hvTypicalRun : v ∈ indexedStageRunTypicalUnion R.run := by
      rw [← R.typicalUnion_terminalStages]
      exact hvTypicalTerminal
    have hstop := R.terminalStop v hvGood hvTypicalRun
    have hredSubset :
        A.cleaned.neighborFinsetIn .red v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) ⊆
          A.cleaned.redNeighborFinset v \
            indexedStageRunRedNeighborhoodUnion R.run := by
      intro w hw
      have hw' := Finset.mem_inter.mp hw
      exact Finset.mem_sdiff.mpr
        ⟨hw'.1, (Finset.mem_sdiff.mp hw'.2).2⟩
    have hredNat :
        A.cleaned.redDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) ≤
          (A.cleaned.redNeighborFinset v \
            indexedStageRunRedNeighborhoodUnion R.run).card := by
      exact Finset.card_le_card hredSubset
    have hredLtNat :
        A.cleaned.redDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) <
          ⌈P.tau * (n : ℝ)⌉₊ := hredNat.trans_lt hstop
    have hredLt :
        (A.cleaned.redDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) <
          (⌈P.tau * (n : ℝ)⌉₊ : ℕ) := by
      exact_mod_cast hredLtNat
    have hceilMass : ((⌈P.tau * (n : ℝ)⌉₊ : ℕ) : ℝ) <
        P.tau * (n : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg P.tau_pos.le hnNonneg)
    have hred :
        (A.cleaned.redDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) ≤
          P.tau * (n : ℝ) + 1 := (hredLt.trans hceilMass).le
    have hpartCovered :
        uniformStagePart (indexedRunTerminalStages R.run) a ⊆
          indexedStageRunRedNeighborhoodUnion R.run := by
      intro w hw
      have hwAmbient : w ∈
          uniformStageAmbientUnion (indexedRunTerminalStages R.run) :=
        Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hw⟩
      rw [R.terminalAmbientUnion_eq_covered] at hwAmbient
      exact hwAmbient
    have htarget : A.retained \
          indexedStageRunRedNeighborhoodUnion R.run ⊆
        (uniformStagePart (indexedRunTerminalStages R.run) a)ᶜ := by
      intro w hw
      rw [Finset.mem_compl]
      intro hwPart
      exact (Finset.mem_sdiff.mp hw).2 (hpartCovered hwPart)
    have hblueMonoNat := degreeIn_mono_finset A.cleaned .blue v htarget
    have hblueMono :
        (A.cleaned.blueDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) ≤
          (A.cleaned.blueDegreeIn v
            (uniformStagePart (indexedRunTerminalStages R.run) a)ᶜ : ℝ) := by
      exact_mod_cast hblueMonoNat
    have hblueExternal :
        (A.cleaned.blueDegreeIn v
            (uniformStagePart (indexedRunTerminalStages R.run) a)ᶜ : ℝ) ≤
          P.terminalError n := by
      simpa only [uniformStagePart, uniformStageTypical, a] using
        (uniformStageAt (indexedRunTerminalStages R.run) a.1).lowExternalBlue
          a.2 v hvTypical
    have hblue :
        (A.cleaned.blueDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) ≤
          P.tau * (n : ℝ) + P.master :=
      hblueMono.trans (hblueExternal.trans hterminalError)
    have hmasterThree : (3 : ℝ) ≤ P.master := by
      linarith [P.one_ninety_two_le_master]
    have hcoefficient : 3 * P.tau ≤ zeta / 100 := by
      have hmul := mul_le_mul_of_nonneg_right hmasterThree P.tau_pos.le
      exact hmul.trans P.master_mul_tau_lt_zeta.le
    calc
      (A.cleaned.redDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) +
          (A.cleaned.blueDegreeIn v
            (A.retained \ indexedStageRunRedNeighborhoodUnion R.run) : ℝ) ≤
          (P.tau * (n : ℝ) + 1) +
            (P.tau * (n : ℝ) + P.master) := add_le_add hred hblue
      _ ≤ (3 * P.tau) * (n : ℝ) := by nlinarith
      _ ≤ (zeta / 100) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcoefficient hnNonneg
  have hnCore : ⌈(delta k : ℝ) / zeta⌉₊ ≤ n := by
    exact (le_max_right _ _).trans (by
      simpa only [CoreExtractionParameters.terminalBudgetThreshold] using hn)
  have hceilCore : (delta k : ℝ) / zeta ≤
      (⌈(delta k : ℝ) / zeta⌉₊ : ℕ) := Nat.le_ceil _
  have hnCoreReal : ((⌈(delta k : ℝ) / zeta⌉₊ : ℕ) : ℝ) ≤
      (n : ℝ) := by
    exact_mod_cast hnCore
  have hdeltaLe : (delta k : ℝ) ≤ zeta * (n : ℝ) := by
    have hratio := hceilCore.trans hnCoreReal
    simpa [mul_comm] using (div_le_iff₀ hzeta).mp hratio
  have hcoreCardNat :
      (A.retainedᶜ ∪ indexedStageRunRedNeighborhoodUnion R.run).card ≤ n := by
    simpa using Finset.card_le_univ
      (A.retainedᶜ ∪ indexedStageRunRedNeighborhoodUnion R.run)
  have hcoreCard :
      ((A.retainedᶜ ∪
          indexedStageRunRedNeighborhoodUnion R.run).card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcoreCardNat
  have hdivNat :
      delta k *
          (A.retainedᶜ ∪ indexedStageRunRedNeighborhoodUnion R.run).card / 2 ≤
        delta k *
          (A.retainedᶜ ∪ indexedStageRunRedNeighborhoodUnion R.run).card :=
    Nat.div_le_self _ _
  have hcoreMantel :
      (((delta k *
          (A.retainedᶜ ∪ indexedStageRunRedNeighborhoodUnion R.run).card /
            2 : ℕ) : ℝ)) ≤ zeta * (n : ℝ) ^ 2 := by
    calc
      (((delta k *
          (A.retainedᶜ ∪ indexedStageRunRedNeighborhoodUnion R.run).card /
            2 : ℕ) : ℝ)) ≤
          ((delta k *
            (A.retainedᶜ ∪
              indexedStageRunRedNeighborhoodUnion R.run).card : ℕ) : ℝ) := by
        exact_mod_cast hdivNat
      _ = (delta k : ℝ) *
          ((A.retainedᶜ ∪
            indexedStageRunRedNeighborhoodUnion R.run).card : ℝ) := by
        norm_num [Nat.cast_mul]
      _ ≤ (delta k : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hcoreCard (Nat.cast_nonneg _)
      _ ≤ (zeta * (n : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hdeltaLe hnNonneg
      _ = zeta * (n : ℝ) ^ 2 := by ring
  exact {
    retainedComplementSmall := hretained
    uncoveredSmall := huncovered
    finalUnionLarge := hfinalLarge
    cleanedBoundaryPointwise := hboundary
    threeErrorSlots_le := by nlinarith
    coreMantelAbsorbed := hcoreMantel
  }

/-- Eventual form of `coreExtractionTerminalBudgetCertificate_of_large`,
uniform in the coloring, cleaned start, run, and terminal quotient. -/
theorem eventually_coreExtractionTerminalBudgetCertificate
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n),
      ∀ A : CleanedCoreStart k n C eta P.tailScale,
      ∀ R : CleanedCoreSeedRunCertificate P A,
      ∀ B : UniformStageOverlapBounds (indexedRunTerminalStages R.run),
        ((uniformStageAmbientUnion (indexedRunTerminalStages R.run) \
            uniformStageFinalUnion B).card : ℝ) ≤
          P.master * P.tau * (n : ℝ) / 100 →
        CoreExtractionTerminalBudgetCertificate P A R B := by
  refine ⟨P.terminalBudgetThreshold, ?_⟩
  intro n hn C A R B hambient
  exact coreExtractionTerminalBudgetCertificate_of_large
    hk heta P A R B hn hambient

set_option maxHeartbeats 800000 in
-- The explicit floor/ceiling absorption and quotient-loss hierarchy needs the larger budget.
theorem exists_terminalQuotient_of_indexedRun
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ C : ColoredGraph (Fin n), ∀ control : Finset (Fin n), ∀ reference : ℝ,
      ∀ indexedRun : List (IndexedUniformCoreSeedStage P C control reference),
      eta * (n : ℝ) ≤ reference →
      indexedRun ≠ [] → indexedRun.length ≤ P.stageBound →
      ∃ B : UniformStageOverlapBounds (indexedRunTerminalStages indexedRun),
        UniformStageQuotientCertificate (indexedRunTerminalStages indexedRun) B ∧
        (∀ q, P.clusterScale * (n : ℝ) ≤
          (uniformStageFinalClusters B q).card) ∧
        (∀ q, (eta / P.master) * (n : ℝ) ≤
          (uniformStageFinalClusters B q).card) ∧
        (∀ q, |((uniformStageFinalClusters B q).card : ℝ) -
            reference / (delta k : ℝ)| ≤
          eta * P.tau / 10000 * (n : ℝ)) ∧
        (∀ q, |((uniformStageFinalClusters B q).card : ℝ) -
            reference / (delta k : ℝ)| ≤ P.mixedInput * (n : ℝ)) ∧
        delta k ≤ overlapClassCount
          (uniformStageTypical (indexedRunTerminalStages indexedRun))
          B.overlapError ∧
        uniformStageNewClassThreshold B < ⌈P.tau * (n : ℝ)⌉₊ ∧
        (((uniformStageAmbientUnion (indexedRunTerminalStages indexedRun) \
            uniformStageFinalUnion B).card : ℕ) : ℝ) ≤
          P.master * P.tau * (n : ℝ) / 100 := by
  let D : ℝ := delta k
  let K : ℝ := P.master
  let s : ℝ := Real.sqrt (P.betaSeq (Fin.last P.stageBound))
  let T : ℝ := P.tau
  let R : ℝ := (P.stageBound + 1 : ℕ)
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (show 0 < delta k by unfold delta; omega)
  have hK : 0 < K := P.master_pos
  have hT : 0 < T := P.tau_pos
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (P.betaSeq_pos _)
  have hR : 1 ≤ R := by
    dsimp [R]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le P.stageBound))
  have hmaster : 10000 * (D + 1) ≤ K := by
    simpa [D, K] using P.ten_thousand_mul_delta_add_one_le_master
  have hDK : D ≤ K := by nlinarith only [hmaster, hD]
  have hKone : 1 ≤ K := by nlinarith only [hmaster, hD]
  have hKdiv100 : K / 100 ≤ K := div_le_self hK.le (by norm_num)
  have hsmallKs : (K / 100) * s ≤ K * s :=
    mul_le_mul_of_nonneg_right hKdiv100 hs.le
  have hbeta : K * R ^ 2 * s < T / 2 := by
    simpa [K, R, s, T] using P.betaLast_overlap
  have hbetaStrong : K * R ^ 2 * s < eta * T / 100000 := by
    simpa [K, R, s, T] using P.betaLast_overlap_strong
  have hetaTau : K * T < eta / 100 := by
    simpa [K, T] using P.tau_lt_eta
  have hKs : 0 ≤ K * s := mul_nonneg hK.le hs.le
  have hKsTau : K * s < T / 2 := by
    have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
    have hle : K * s ≤ K * R ^ 2 * s := by
      nlinarith only [mul_nonneg hKs (sub_nonneg.mpr hR2)]
    exact hle.trans_lt hbeta
  have hDT : D * T < eta / 100 := by
    exact (mul_le_mul_of_nonneg_right hDK hT.le).trans_lt hetaTau
  have hbaseCoeff : 5 * T + K * s < eta / D := by
    rw [lt_div_iff₀ hD]
    have h1 := mul_lt_mul_of_pos_left hKsTau hD
    nlinarith only [h1, hDT, hD, hT]
  have hlargeCoeff : 8 * (K * s) < 5 * T := by
    nlinarith only [hKsTau, hT]
  have hbalCoeff : 5 * R * (K * s) < eta * T / 10000 := by
    have hR2Ks : R * (K * s) ≤ R ^ 2 * (K * s) := by
      have hRLeSq : R ≤ R ^ 2 := by
        nlinarith only [sq_nonneg (R - 1), hR]
      exact mul_le_mul_of_nonneg_right hRLeSq hKs
    have hb' : R ^ 2 * (K * s) < eta * T / 100000 := by
      nlinarith only [hbetaStrong]
    have hetaT : 0 < eta * T := mul_pos heta.1 hT
    nlinarith only [hR2Ks, hb', hetaT]
  have hambCoeff : 6 * D * R ^ 2 * (K * s) < K * T / 100 := by
    have hb' : R ^ 2 * (K * s) < T / 2 := by
      nlinarith only [hbeta]
    have hDKhundred : 3 * D ≤ K / 100 := by
      nlinarith only [hmaster, hD]
    have hmul := mul_le_mul_of_nonneg_right hDKhundred hT.le
    nlinarith only [hb', hmul, hD]
  have hKR : K < R := by
    have hcover : K / T + 1 < (P.stageBound : ℝ) := by
      simpa [K, T] using P.stageBound_covers
    have hKDiv : K < K / T := by
      rw [lt_div_iff₀ hT]
      nlinarith only [P.tau_lt_one, hK]
    dsimp [R]
    push_cast
    nlinarith only [hcover, hKDiv]
  have hDRSq : D ≤ R ^ 2 := by
    have hRLeSq : R ≤ R ^ 2 := by
      nlinarith only [sq_nonneg (R - 1), hR]
    exact (hDK.trans hKR.le).trans hRLeSq
  have hnewCoeff : 6 * D * (K * s) < T / 1000 := by
    have hmul : D * (K * s) ≤ R ^ 2 * (K * s) :=
      mul_le_mul_of_nonneg_right hDRSq hKs
    have hb' : R ^ 2 * (K * s) < eta * T / 100000 := by
      nlinarith only [hbetaStrong]
    have hetaTLt : eta * T < T := by
      simpa using mul_lt_mul_of_pos_right heta.2 hT
    have hDX : D * (K * s) < eta * T / 100000 := hmul.trans_lt hb'
    calc
      6 * D * (K * s) = 6 * (D * (K * s)) := by ring
      _ < 6 * (eta * T / 100000) :=
        mul_lt_mul_of_pos_left hDX (by norm_num)
      _ = (6 / 100000 : ℝ) * (eta * T) := by ring
      _ < (6 / 100000 : ℝ) * T :=
        mul_lt_mul_of_pos_left hetaTLt (by norm_num)
      _ < (1 / 1000 : ℝ) * T :=
        mul_lt_mul_of_pos_right (by norm_num) hT
      _ = T / 1000 := by ring
  obtain ⟨nBase, hnBase⟩ := exists_nat_forall_mul_add_le_mul
    hbaseCoeff (show 0 ≤ K + 1 by positivity)
  obtain ⟨nLarge, hnLarge⟩ := exists_nat_forall_mul_add_le_mul
    hlargeCoeff (show 0 ≤ 4 * (5 * K + 4) by positivity)
  obtain ⟨nBal, hnBal⟩ := exists_nat_forall_mul_add_le_mul
    hbalCoeff
      (show 0 ≤ K + 2 * (P.stageBound : ℝ) * (5 * K + 4) by positivity)
  obtain ⟨nAmb, hnAmb⟩ := exists_nat_forall_mul_add_le_mul
    hambCoeff
      (show 0 ≤ (P.stageBound : ℝ) * D *
        ((2 * K + 1) + 2 * (P.stageBound : ℝ) * (5 * K + 4)) by positivity)
  obtain ⟨nNew, hnNew⟩ := exists_nat_forall_mul_add_le_mul
    hnewCoeff (show 0 ≤ D * (12 * K + 9) by positivity)
  let n₀ := max 1 (max nBase (max nLarge (max nBal (max nAmb nNew))))
  refine ⟨n₀, ?_⟩
  intro n hn C control reference indexedRun href hrun hlength
  have hnPos : 0 < n := by
    have : 1 ≤ n := (le_max_left _ _).trans hn
    omega
  have hnTail : max nBase (max nLarge (max nBal (max nAmb nNew))) ≤ n :=
    (le_max_right 1 _).trans hn
  have hnBase' : nBase ≤ n := by
    exact (le_max_left nBase _).trans hnTail
  have hnTailLarge : max nLarge (max nBal (max nAmb nNew)) ≤ n :=
    (le_max_right nBase _).trans hnTail
  have hnLarge' : nLarge ≤ n := by
    exact (le_max_left nLarge _).trans hnTailLarge
  have hnTailBal : max nBal (max nAmb nNew) ≤ n :=
    (le_max_right nLarge _).trans hnTailLarge
  have hnBal' : nBal ≤ n := by
    exact (le_max_left nBal _).trans hnTailBal
  have hnTailAmb : max nAmb nNew ≤ n :=
    (le_max_right nBal _).trans hnTailBal
  have hnAmb' : nAmb ≤ n := by
    exact (le_max_left nAmb nNew).trans hnTailAmb
  have hnNew' : nNew ≤ n := by
    exact (le_max_right nAmb nNew).trans hnTailAmb
  let N : ℝ := n
  let run := indexedRunTerminalStages indexedRun
  let E : ℝ := P.terminalError n
  let cap : ℕ := ⌈s * N⌉₊
  let part : ℕ := ⌈2 * E⌉₊
  let external : ℕ := ⌈3 * E + 1⌉₊
  let sum : ℕ := part + cap + external
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hnPos
  have hE : E = (K / 100) * s * N + K := by
    simp [E, CoreExtractionParameters.terminalError,
      CoreExtractionParameters.levelError, K, s, N]
  have hENonneg : 0 ≤ E := (P.levelError_pos _ n).le
  have haNonneg : 0 ≤ (K / 100) * s := by positivity
  have hcapLt : (cap : ℝ) < s * N + 1 := by
    dsimp [cap]
    exact Nat.ceil_lt_add_one (mul_nonneg hs.le hN.le)
  have hpartLt : (part : ℝ) < 2 * E + 1 := by
    dsimp [part]
    exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hENonneg)
  have hexternalLt : (external : ℝ) < 3 * E + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 3 * E + 1 by positivity)
    dsimp [external]
    norm_num [Nat.cast_add] at this ⊢
    linarith
  have hsumLt : (sum : ℝ) < 2 * (K * s) * N + (5 * K + 4) := by
    have hcoef : s + 5 * ((K / 100) * s) ≤ 2 * (K * s) := by
      have hsLe : s ≤ K * s := by
        simpa using mul_le_mul_of_nonneg_right hKone hs.le
      have hfive : 5 * ((K / 100) * s) ≤ K * s := by
        nlinarith only [hKs]
      calc
        s + 5 * ((K / 100) * s) ≤ K * s + K * s :=
          add_le_add hsLe hfive
        _ = 2 * (K * s) := by ring
    dsimp [sum]
    norm_num [Nat.cast_add]
    rw [hE] at hpartLt hexternalLt
    nlinarith only [hcapLt, hpartLt, hexternalLt,
      mul_le_mul_of_nonneg_right hcoef hN.le]
  have hpartCoarse : (part : ℝ) < 2 * (K * s) * N + (2 * K + 1) := by
    rw [hE] at hpartLt
    have hcoef : 2 * ((K / 100) * s) ≤ 2 * (K * s) :=
      mul_le_mul_of_nonneg_left hsmallKs (by norm_num)
    nlinarith only [hpartLt, mul_le_mul_of_nonneg_right hcoef hN.le]
  have hbaseAbsorb := hnBase n hnBase'
  have hlargeAbsorb := hnLarge n hnLarge'
  have hbalAbsorb := hnBal n hnBal'
  have hambAbsorb := hnAmb n hnAmb'
  have hnewAbsorb := hnNew n hnNew'
  have hrefDiv : eta / D * N ≤ reference / D := by
    rw [div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hD).2 (by simpa [N] using href)
  have hbaseFloor : 5 * T * N <
      ((⌊reference / D - E⌋₊ : ℕ) : ℝ) := by
    have hECoarse : E ≤ K * s * N + K := by
      rw [hE]
      simpa [add_comm] using add_le_add_right
        (mul_le_mul_of_nonneg_right hsmallKs hN.le) K
    have hbefore : 5 * T * N + E + 1 ≤ reference / D := by
      calc
        5 * T * N + E + 1 ≤
            (5 * T + K * s) * N + (K + 1) := by
          nlinarith only [hECoarse]
        _ ≤ eta / D * N := by simpa [N] using hbaseAbsorb
        _ ≤ reference / D := hrefDiv
    have hfloor := Nat.lt_floor_add_one (reference / D - E)
    nlinarith only [hbefore, hfloor]
  have hbaseNonneg : 0 ≤ reference / D - E := by
    have hfloorRealPos : (0 : ℝ) <
        ((⌊reference / D - E⌋₊ : ℕ) : ℝ) :=
      (show (0 : ℝ) < 5 * T * N by positivity).trans hbaseFloor
    have hfloorPos : 0 < ⌊reference / D - E⌋₊ := by
      exact_mod_cast hfloorRealPos
    exact (Nat.pos_of_floor_pos hfloorPos).le
  have hroundLarge : 4 * sum < ⌊reference / D - E⌋₊ := by
    have hsumFour : ((4 * sum : ℕ) : ℝ) <
        8 * (K * s) * N + 4 * (5 * K + 4) := by
      norm_num [Nat.cast_mul]
      nlinarith only [hsumLt]
    have htoTau : 8 * (K * s) * N + 4 * (5 * K + 4) ≤
        5 * T * N := by simpa [N] using hlargeAbsorb
    have hreal := (hsumFour.trans_le htoTau).trans hbaseFloor
    exact_mod_cast hreal
  have hcap : ∀ q : Fin run.length,
      (uniformStageAt run q).internalNonblueCap ≤ cap := by
    intro q
    simpa [run, cap, s, N, coreSeedNonblueCap] using
      indexedRunTerminalStages_internalNonblueCap_le indexedRun q
  let B : UniformStageOverlapBounds run :=
    UniformStageOverlapBounds.ofFloorCeil cap hbaseNonneg hcap hroundLarge
  have hrunTerminal : run ≠ [] := by
    simpa [run, indexedRunTerminalStages] using hrun
  have Q : UniformStageQuotientCertificate run B :=
    uniformStageQuotientCertificate_of_bounds B hk hrunTerminal
  have hlenRun : run.length ≤ P.stageBound := by
    simpa [run] using hlength
  have hoverlap : (B.overlapError : ℝ) <
      4 * (K * s) * N + 2 * (5 * K + 4) := by
    change ((2 * sum : ℕ) : ℝ) < _
    norm_num [Nat.cast_mul]
    nlinarith only [hsumLt]
  have hbalanceBudget : E + ((run.length * B.overlapError : ℕ) : ℝ) ≤
      eta * T / 10000 * N := by
    have hlenCast : (run.length : ℝ) ≤ (P.stageBound : ℝ) := by
      exact_mod_cast hlenRun
    have hELe : E ≤ K * s * N + K := by
      rw [hE]
      simpa [add_comm] using add_le_add_right
        (mul_le_mul_of_nonneg_right hsmallKs hN.le) K
    have hoverlapLe : (B.overlapError : ℝ) ≤
        4 * (K * s) * N + 2 * (5 * K + 4) := hoverlap.le
    have hmulOverlap : (run.length : ℝ) * (B.overlapError : ℝ) ≤
        (P.stageBound : ℝ) *
          (4 * (K * s) * N + 2 * (5 * K + 4)) := by
      calc
        (run.length : ℝ) * (B.overlapError : ℝ) ≤
            (run.length : ℝ) *
              (4 * (K * s) * N + 2 * (5 * K + 4)) :=
          mul_le_mul_of_nonneg_left hoverlapLe (by positivity)
        _ ≤ (P.stageBound : ℝ) *
              (4 * (K * s) * N + 2 * (5 * K + 4)) :=
          mul_le_mul_of_nonneg_right hlenCast (by positivity)
    have hXPos : 0 < (K * s) * N := mul_pos (mul_pos hK hs) hN
    have hSXNonneg : 0 ≤ (P.stageBound : ℝ) * ((K * s) * N) := by
      positivity
    have hraw : E + ((run.length * B.overlapError : ℕ) : ℝ) <
        5 * R * (K * s) * N +
          (K + 2 * (P.stageBound : ℝ) * (5 * K + 4)) := by
      rw [Nat.cast_mul]
      calc
        E + (run.length : ℝ) * (B.overlapError : ℝ) ≤
            (K * s * N + K) + (P.stageBound : ℝ) *
              (4 * (K * s) * N + 2 * (5 * K + 4)) :=
          add_le_add hELe hmulOverlap
        _ < 5 * R * (K * s) * N +
              (K + 2 * (P.stageBound : ℝ) * (5 * K + 4)) := by
          dsimp [R]
          push_cast
          nlinarith only [hXPos, hSXNonneg]
    exact hraw.le.trans (by simpa [N] using hbalAbsorb)
  have hbalanceFour : eta * T / 10000 * N ≤ 4 * T * N := by
    have hcoef : eta * T / 10000 ≤ 4 * T := by
      have hetaUpper : eta / 10000 ≤ 4 := by
        nlinarith only [heta.2]
      simpa only [div_mul_eq_mul_div] using
        mul_le_mul_of_nonneg_right hetaUpper hT.le
    exact mul_le_mul_of_nonneg_right hcoef hN.le
  have hmixedBudget : 4 * T * N ≤ P.mixedInput * N := by
    rw [P.mixedInput_eq]
    have : (4 : ℝ) ≤ K := by nlinarith only [hmaster, hD]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right this hT.le) hN.le
  have hambientBudget :
      (((run.length * delta k) *
          (B.partLoss + run.length * B.overlapError) : ℕ) : ℝ) ≤
        K * T * N / 100 := by
    have hlenCast : (run.length : ℝ) ≤ (P.stageBound : ℝ) := by
      exact_mod_cast hlenRun
    have hpartB : B.partLoss = part := rfl
    have hoverlapLe : (B.overlapError : ℝ) ≤
        4 * (K * s) * N + 2 * (5 * K + 4) := hoverlap.le
    have hmulOverlap : (run.length : ℝ) * (B.overlapError : ℝ) ≤
        (P.stageBound : ℝ) *
          (4 * (K * s) * N + 2 * (5 * K + 4)) := by
      calc
        (run.length : ℝ) * (B.overlapError : ℝ) ≤
            (run.length : ℝ) *
              (4 * (K * s) * N + 2 * (5 * K + 4)) :=
          mul_le_mul_of_nonneg_left hoverlapLe (by positivity)
        _ ≤ (P.stageBound : ℝ) *
              (4 * (K * s) * N + 2 * (5 * K + 4)) :=
          mul_le_mul_of_nonneg_right hlenCast (by positivity)
    have hinsideLe : (part : ℝ) +
          (run.length : ℝ) * (B.overlapError : ℝ) ≤
        (2 * (K * s) * N + (2 * K + 1)) +
          (P.stageBound : ℝ) *
            (4 * (K * s) * N + 2 * (5 * K + 4)) :=
      add_le_add hpartCoarse.le hmulOverlap
    have hLDLe : (run.length : ℝ) * D ≤ (P.stageBound : ℝ) * D :=
      mul_le_mul_of_nonneg_right hlenCast hD.le
    have hleftLe :
        ((run.length : ℝ) * D) *
            ((part : ℝ) + (run.length : ℝ) * (B.overlapError : ℝ)) ≤
          ((P.stageBound : ℝ) * D) *
            ((2 * (K * s) * N + (2 * K + 1)) +
              (P.stageBound : ℝ) *
                (4 * (K * s) * N + 2 * (5 * K + 4))) := by
      calc
        ((run.length : ℝ) * D) *
            ((part : ℝ) + (run.length : ℝ) * (B.overlapError : ℝ)) ≤
            ((run.length : ℝ) * D) *
              ((2 * (K * s) * N + (2 * K + 1)) +
                (P.stageBound : ℝ) *
                  (4 * (K * s) * N + 2 * (5 * K + 4))) :=
          mul_le_mul_of_nonneg_left hinsideLe (by positivity)
        _ ≤ ((P.stageBound : ℝ) * D) *
              ((2 * (K * s) * N + (2 * K + 1)) +
                (P.stageBound : ℝ) *
                  (4 * (K * s) * N + 2 * (5 * K + 4))) :=
          mul_le_mul_of_nonneg_right hLDLe (by positivity)
    have hcoeff : (P.stageBound : ℝ) *
        (2 + 4 * (P.stageBound : ℝ)) < 6 * R ^ 2 := by
      dsimp [R]
      push_cast
      nlinarith only [sq_nonneg (P.stageBound : ℝ),
        (show (0 : ℝ) ≤ (P.stageBound : ℝ) by positivity)]
    have hXPos : 0 < (K * s) * N := mul_pos (mul_pos hK hs) hN
    have hlead : (P.stageBound : ℝ) * D *
          ((2 + 4 * (P.stageBound : ℝ)) * ((K * s) * N)) <
        6 * D * R ^ 2 * ((K * s) * N) := by
      calc
        (P.stageBound : ℝ) * D *
            ((2 + 4 * (P.stageBound : ℝ)) * ((K * s) * N)) =
            ((P.stageBound : ℝ) *
              (2 + 4 * (P.stageBound : ℝ))) * (D * ((K * s) * N)) := by ring
        _ < (6 * R ^ 2) * (D * ((K * s) * N)) :=
          mul_lt_mul_of_pos_right hcoeff (mul_pos hD hXPos)
        _ = 6 * D * R ^ 2 * ((K * s) * N) := by ring
    have hfinal :
        ((P.stageBound : ℝ) * D) *
            ((2 * (K * s) * N + (2 * K + 1)) +
              (P.stageBound : ℝ) *
                (4 * (K * s) * N + 2 * (5 * K + 4))) <
          6 * D * R ^ 2 * (K * s) * N +
            (P.stageBound : ℝ) * D *
              ((2 * K + 1) +
                2 * (P.stageBound : ℝ) * (5 * K + 4)) := by
      calc
        ((P.stageBound : ℝ) * D) *
            ((2 * (K * s) * N + (2 * K + 1)) +
              (P.stageBound : ℝ) *
                (4 * (K * s) * N + 2 * (5 * K + 4))) =
            (P.stageBound : ℝ) * D *
                ((2 + 4 * (P.stageBound : ℝ)) * ((K * s) * N)) +
              (P.stageBound : ℝ) * D *
                ((2 * K + 1) +
                  2 * (P.stageBound : ℝ) * (5 * K + 4)) := by ring
        _ < 6 * D * R ^ 2 * ((K * s) * N) +
              (P.stageBound : ℝ) * D *
                ((2 * K + 1) +
                  2 * (P.stageBound : ℝ) * (5 * K + 4)) :=
          add_lt_add_left hlead _
        _ = 6 * D * R ^ 2 * (K * s) * N +
              (P.stageBound : ℝ) * D *
                ((2 * K + 1) +
                  2 * (P.stageBound : ℝ) * (5 * K + 4)) := by ring
    have hraw :
        (((run.length * delta k) *
            (B.partLoss + run.length * B.overlapError) : ℕ) : ℝ) <
          6 * D * R ^ 2 * (K * s) * N +
            (P.stageBound : ℝ) * D *
              ((2 * K + 1) + 2 * (P.stageBound : ℝ) * (5 * K + 4)) := by
      simp only [Nat.cast_mul, Nat.cast_add, hpartB]
      have hdeltaCast : ((delta k : ℕ) : ℝ) = D := by rfl
      rw [hdeltaCast]
      exact hleftLe.trans_lt hfinal
    have hAbsorb :
        6 * D * R ^ 2 * (K * s) * N +
            (P.stageBound : ℝ) * D *
              ((2 * K + 1) +
                2 * (P.stageBound : ℝ) * (5 * K + 4)) ≤
          K * T * N / 100 := by
      calc
        6 * D * R ^ 2 * (K * s) * N +
            (P.stageBound : ℝ) * D *
              ((2 * K + 1) +
                2 * (P.stageBound : ℝ) * (5 * K + 4)) ≤
            K * T / 100 * (n : ℝ) := by simpa [N] using hambAbsorb
        _ = K * T * N / 100 := by dsimp [N]; ring
    exact hraw.le.trans hAbsorb
  have hnewClassThreshold :
      uniformStageNewClassThreshold B < ⌈T * N⌉₊ := by
    have htotal : (((2 * sum + part : ℕ) : ℝ)) <
        6 * (K * s) * N + (12 * K + 9) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      nlinarith only [hsumLt, hpartCoarse]
    have hscaled : (((delta k * (2 * sum + part) : ℕ) : ℝ)) <
        6 * D * (K * s) * N + D * (12 * K + 9) := by
      simp only [Nat.cast_mul]
      rw [show ((delta k : ℕ) : ℝ) = D by rfl]
      calc
        D * (((2 * sum + part : ℕ) : ℝ)) <
            D * (6 * (K * s) * N + (12 * K + 9)) :=
          mul_lt_mul_of_pos_left htotal hD
        _ = 6 * D * (K * s) * N + D * (12 * K + 9) := by ring
    have hceil : T * N ≤ ((⌈T * N⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hnewAbsorb' :
        6 * D * (K * s) * N + D * (12 * K + 9) ≤
          T / 1000 * N := by simpa [N] using hnewAbsorb
    have hsmallTau : T / 1000 * N ≤ T * N :=
      mul_le_mul_of_nonneg_right
        (div_le_self hT.le (by norm_num)) hN.le
    have hreal : (((delta k * (2 * sum + part) : ℕ) : ℝ)) <
        ((⌈T * N⌉₊ : ℕ) : ℝ) :=
      hscaled.trans_le (hnewAbsorb'.trans (hsmallTau.trans hceil))
    change delta k * (2 * sum + part) < ⌈T * N⌉₊
    exact_mod_cast hreal
  have hclusterStrong : ∀ q, eta / K * N ≤
      ((uniformStageFinalClusters B q).card : ℝ) := by
    intro q
    have hbal := uniformStageFinalClusters_balanced B q
    have hlower := (abs_le.mp hbal).1
    have hfour : 4 * T ≤ eta / K := by
      rw [le_div_iff₀ hK]
      nlinarith only [hetaTau, hK, hT]
    have htwoD : 2 * D ≤ K := by nlinarith only [hmaster, hD]
    have hdouble : 2 * (eta / K) ≤ eta / D := by
      rw [show 2 * (eta / K) = (2 * eta) / K by ring]
      rw [div_le_div_iff₀ hK hD]
      have hmul := mul_le_mul_of_nonneg_left htwoD heta.1.le
      nlinarith only [hmul]
    have hclusterCoeff : eta / K + 4 * T ≤ eta / D := by
      have hsum := add_le_add_right hfour (eta / K)
      exact hsum.trans (by
        simpa [two_mul] using hdouble)
    have htarget : eta / K * N ≤ reference / D - 4 * T * N := by
      have hmul := mul_le_mul_of_nonneg_right hclusterCoeff hN.le
      nlinarith only [hmul, hrefDiv]
    exact htarget.trans (by
      have := hlower
      dsimp [run] at this ⊢
      nlinarith only [this, hbalanceBudget.trans hbalanceFour])
  refine ⟨B, Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    have hscale : P.clusterScale ≤ eta / K := by
      rw [P.clusterScale_eq]
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * K) hK]
      nlinarith only [heta.1, hK]
    exact (mul_le_mul_of_nonneg_right hscale hN.le).trans (hclusterStrong q)
  · intro q
    simpa [K, N] using hclusterStrong q
  · intro q
    exact (uniformStageFinalClusters_balanced B q).trans hbalanceBudget
  · intro q
    exact (uniformStageFinalClusters_balanced B q).trans
      (hbalanceBudget.trans (hbalanceFour.trans hmixedBudget))
  · have hlenPos : 0 < run.length := List.length_pos_iff.mpr hrunTerminal
    let q0 : Fin run.length := ⟨0, hlenPos⟩
    simpa [run] using delta_le_uniformStageOverlapClassCount B q0
  · simpa [T, N] using hnewClassThreshold
  · have hA := uniformStageAmbient_sdiff_finalUnion_card_le B
    have hcast :
        (((uniformStageAmbientUnion run \ uniformStageFinalUnion B).card : ℕ) : ℝ) ≤
          (((run.length * delta k) *
            (B.partLoss + run.length * B.overlapError) : ℕ) : ℝ) := by
      exact Nat.cast_le.2 hA
    simpa [run, K, T, N] using hcast.trans hambientBudget

/- The cap, terminal-error, internal-red, and restricted-weighted budgets
below are the four eventual scalar estimates consumed by the terminal
quotient-to-final-certificate constructor. -/
set_option maxHeartbeats 800000 in
-- Proving all four floor/ceiling absorption estimates together needs the larger budget.
theorem exists_coreExtractionFinalClusterInputBudgetThreshold
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let cap := coreSeedNonblueCap
        (P.betaSeq (Fin.last P.stageBound)) n
      ((cap : ℝ) + 1 ≤ eta * P.tau / 10 * (n : ℝ)) ∧
      (eta * P.tau / 10000 * (n : ℝ) + ((cap : ℝ) + 1) +
          2 * P.terminalError n ≤ eta * P.tau / 10 * (n : ℝ)) ∧
      ((n : ℝ) * (cap : ℝ) / 2 ≤
          P.tau ^ 2 * (n : ℝ) ^ 2) ∧
      (P.tau * (n : ℝ) + (delta k : ℝ) +
          (P.tau * (n : ℝ) + 1 +
            P.master * P.tau * (n : ℝ) / 100) +
          (delta k : ℝ) * (eta * P.tau / 10 * (n : ℝ)) ≤
        P.mixedInput * (n : ℝ)) := by
  let D : ℝ := delta k
  let K : ℝ := P.master
  let T : ℝ := P.tau
  let b : ℝ := Real.sqrt (P.betaSeq (Fin.last P.stageBound))
  let L : ℝ := (P.stageBound + 1 : ℕ)
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast (show 0 < delta k by unfold delta; omega)
  have hK : 0 < K := by simpa [K] using P.master_pos
  have hKge : (192 : ℝ) ≤ K := by
    simpa [K] using P.one_ninety_two_le_master
  have hKone : 1 ≤ K := by linarith
  have hT : 0 < T := by simpa [T] using P.tau_pos
  have hTone : T < 1 := by simpa [T] using P.tau_lt_one
  have hetaT : 0 < eta * T := mul_pos heta.1 hT
  have hb : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.2 (P.betaSeq_pos _)
  have hL : 0 < L := by positivity
  have hfactor : 1 ≤ L ^ 2 := by
    have : (1 : ℝ) ≤ L := by
      dsimp [L]
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le P.stageBound))
    nlinarith [sq_nonneg (L - 1)]
  have hKb : K * b ≤ K * L ^ 2 * b := by
    calc
      K * b = (K * b) * 1 := by ring
      _ ≤ (K * b) * L ^ 2 :=
        mul_le_mul_of_nonneg_left hfactor (mul_nonneg hK.le hb.le)
      _ = K * L ^ 2 * b := by ring
  have hKbSmall : K * b < eta * T / 100000 := by
    exact hKb.trans_lt (by simpa [K, L, b, T] using P.betaLast_overlap_strong)
  have hbLeKb : b ≤ K * b := by
    simpa using mul_le_mul_of_nonneg_right hKone hb.le
  have hblueCoeff :
      eta * T / 10000 + b + K / 50 * b < eta * T / 10 := by
    have hbSmall : b < eta * T / 100000 := hbLeKb.trans_lt hKbSmall
    have hKfifty : K / 50 * b < eta * T / 5000000 := by
      calc
        K / 50 * b = (K * b) / 50 := by ring
        _ < (eta * T / 100000) / 50 :=
          div_lt_div_of_pos_right hKbSmall (by norm_num)
        _ = eta * T / 5000000 := by ring
    nlinarith only [hetaT, hbSmall, hKfifty]
  obtain ⟨nBlue, hnBlue⟩ := exists_nat_forall_mul_add_le_mul
    hblueCoeff (show 0 ≤ 2 + 2 * K by positivity)
  have hcover : 1 < T * L := by
    have hraw : K / T + 1 < L := by
      have hstage : K / T + 1 < (P.stageBound : ℝ) := by
        simpa [K, T] using P.stageBound_covers
      calc
        K / T + 1 < (P.stageBound : ℝ) := hstage
        _ < (P.stageBound : ℝ) + 1 := lt_add_one _
        _ = L := by simp [L]
    have hratio : 1 / T ≤ K / T := by
      exact (div_le_div_iff_of_pos_right hT).2 hKone
    have hratioLt : 1 / T < K / T + 1 :=
      hratio.trans_lt (lt_add_one (K / T))
    have : 1 / T < L := hratioLt.trans hraw
    have hprod : (1 : ℝ) < L * T := (div_lt_iff₀ hT).mp this
    simpa [mul_comm] using hprod
  have hTLsq : 1 < (T * L) ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hcover)
      (by linarith [mul_pos hT hL] : 0 < T * L + 1)
    nlinarith
  have hLb : L ^ 2 * b ≤ K * L ^ 2 * b := by
    calc
      L ^ 2 * b = 1 * (L ^ 2 * b) := by ring
      _ ≤ K * (L ^ 2 * b) :=
        mul_le_mul_of_nonneg_right hKone (mul_nonneg (sq_nonneg L) hb.le)
      _ = K * L ^ 2 * b := by ring
  have hbeta : K * L ^ 2 * b < T / 2 := by
    simpa [K, L, b, T] using P.betaLast_overlap
  have hbTauSq : b < T ^ 2 := by
    calc
      b = 1 * b := by ring
      _ < (T * L) ^ 2 * b := mul_lt_mul_of_pos_right hTLsq hb
      _ = T ^ 2 * (L ^ 2 * b) := by ring
      _ ≤ T ^ 2 * (K * L ^ 2 * b) :=
        mul_le_mul_of_nonneg_left hLb (sq_nonneg T)
      _ < T ^ 2 * (T / 2) :=
        mul_lt_mul_of_pos_left hbeta (sq_pos_of_pos hT)
      _ < T ^ 2 := by
        have : T / 2 < 1 := by linarith
        simpa using mul_lt_mul_of_pos_left this (sq_pos_of_pos hT)
  obtain ⟨nRed, hnRed⟩ := exists_nat_forall_mul_add_le_mul
    (show b / 2 < T ^ 2 by linarith [hbTauSq])
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
  have hmaster : 10000 * (D + 1) ≤ K := by
    simpa [D, K] using P.ten_thousand_mul_delta_add_one_le_master
  have hDsmall : D ≤ K / 10000 := by nlinarith
  have hDeta : D * eta ≤ D := by
    have := mul_le_mul_of_nonneg_left heta.2.le hD.le
    simpa using this
  have hweightedCoeff :
      2 * T + K * T / 100 + D * (eta * T / 10) < K * T := by
    have hDetaSmall : D * eta ≤ K / 10000 := hDeta.trans hDsmall
    have hmul := mul_le_mul_of_nonneg_right hDetaSmall hT.le
    nlinarith only [hT, hKge, hmul]
  obtain ⟨nWeighted, hnWeighted⟩ := exists_nat_forall_mul_add_le_mul
    hweightedCoeff (show 0 ≤ D + 1 by positivity)
  let n₀ := max 1 (max nBlue (max nRed nWeighted))
  refine ⟨n₀, ?_⟩
  intro n hn
  have hnOne : 1 ≤ n := (le_max_left _ _).trans hn
  have hnPos : 0 < n := by omega
  have hnTail : max nBlue (max nRed nWeighted) ≤ n :=
    (le_max_right 1 _).trans hn
  have hnBlue' : nBlue ≤ n := (le_max_left _ _).trans hnTail
  have hnRed' : nRed ≤ n :=
    (le_max_left _ _).trans ((le_max_right nBlue _).trans hnTail)
  have hnWeighted' : nWeighted ≤ n :=
    (le_max_right nRed nWeighted).trans
      ((le_max_right nBlue _).trans hnTail)
  let N : ℝ := n
  let cap := coreSeedNonblueCap
    (P.betaSeq (Fin.last P.stageBound)) n
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hnPos
  have hcap : (cap : ℝ) < b * N + 1 := by
    simpa [cap, b, N] using coreSeedNonblueCap_lt_add_one
      (P.betaSeq_pos (Fin.last P.stageBound)).le n
  have hterminal : P.terminalError n = K / 100 * b * N + K := by
    simp [CoreExtractionParameters.terminalError,
      CoreExtractionParameters.levelError, K, b, N]
  have hblueAbsorb := hnBlue n hnBlue'
  have hblueBudget :
      eta * T / 10000 * N + ((cap : ℝ) + 1) +
          2 * P.terminalError n ≤ eta * T / 10 * N := by
    rw [hterminal]
    calc
      eta * T / 10000 * N + ((cap : ℝ) + 1) +
          2 * (K / 100 * b * N + K) ≤
          (eta * T / 10000 + b + K / 50 * b) * N + (2 + 2 * K) := by
        nlinarith [hcap]
      _ ≤ eta * T / 10 * N := by simpa [N] using hblueAbsorb
  have hownBudget : (cap : ℝ) + 1 ≤ eta * T / 10 * N := by
    have hnonneg : 0 ≤ eta * T / 10000 * N + 2 * P.terminalError n := by
      have hterminalNonneg : 0 ≤ P.terminalError n :=
        (P.levelError_pos _ n).le
      positivity
    linarith [hblueBudget]
  have hredAbsorb := hnRed n hnRed'
  have hredBudget : N * (cap : ℝ) / 2 ≤ T ^ 2 * N ^ 2 := by
    have hcapLe : (cap : ℝ) ≤ b * N + 1 := hcap.le
    have hmul := mul_le_mul_of_nonneg_left hcapLe hN.le
    calc
      N * (cap : ℝ) / 2 ≤ N * (b * N + 1) / 2 := by linarith
      _ = N * (b / 2 * N + 1 / 2) := by ring
      _ ≤ N * (T ^ 2 * N) :=
        mul_le_mul_of_nonneg_left (by simpa [N] using hredAbsorb) hN.le
      _ = T ^ 2 * N ^ 2 := by ring
  have hweightedAbsorb := hnWeighted n hnWeighted'
  have hweightedBudget :
      T * N + D + (T * N + 1 + K * T * N / 100) +
          D * (eta * T / 10 * N) ≤ K * T * N := by
    calc
      T * N + D + (T * N + 1 + K * T * N / 100) +
          D * (eta * T / 10 * N) =
          (2 * T + K * T / 100 + D * (eta * T / 10)) * N +
            (D + 1) := by ring
      _ ≤ K * T * N := by simpa [N] using hweightedAbsorb
  dsimp only [cap]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [T, N] using hownBudget
  · simpa [T, N] using hblueBudget
  · simpa [T, N] using hredBudget
  · rw [P.mixedInput_eq]
    simpa [D, K, T, N] using hweightedBudget

/- This exact constructor separates the quotient geometry from the eventual
parameter absorption.  Its four scalar budgets are precisely the output of
`exists_coreExtractionFinalClusterInputBudgetThreshold`. -/
set_option maxHeartbeats 800000 in
-- Assembling the dependent quotient certificate and its scalar fields exceeds the default budget.
noncomputable def coreExtractionFinalClusterCertificate_of_terminalQuotient_of_budgets
    {k n nGoal : ℕ} {eta zeta : ℝ}
    (hk : 3 ≤ k) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (P : CoreExtractionParameters k eta zeta)
    {C : ColoredGraph (Fin n)}
    (A : CleanedCoreStart k n C eta P.tailScale)
    (R : CleanedCoreSeedRunCertificate P A)
    (_htwo : 2 ≤ R.run.length)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run))
    (Q : UniformStageQuotientCertificate
      (indexedRunTerminalStages R.run) B)
    (hclusterLower : ∀ q,
      (eta / P.master) * (n : ℝ) ≤
        ((uniformStageFinalClusters B q).card : ℝ))
    (hsizeStrong : ∀ q,
      |((uniformStageFinalClusters B q).card : ℝ) -
          (C.redDegree A.seed : ℝ) / (delta k : ℝ)| ≤
        eta * P.tau / 10000 * (n : ℝ))
    (_hsizeMixed : ∀ q,
      |((uniformStageFinalClusters B q).card : ℝ) -
          (C.redDegree A.seed : ℝ) / (delta k : ℝ)| ≤
        P.mixedInput * (n : ℝ))
    (hclassCount : delta k + 1 ≤ overlapClassCount
      (uniformStageTypical (indexedRunTerminalStages R.run)) B.overlapError)
    (hambientLoss :
      ((uniformStageAmbientUnion (indexedRunTerminalStages R.run) \
          uniformStageFinalUnion B).card : ℝ) ≤
        P.master * P.tau * (n : ℝ) / 100)
    (hnGoal : nGoal ≤ n) (hnPos : 0 < n)
    (hbudgets :
      let cap := coreSeedNonblueCap
        (P.betaSeq (Fin.last P.stageBound)) n
      ((cap : ℝ) + 1 ≤ eta * P.tau / 10 * (n : ℝ)) ∧
      (eta * P.tau / 10000 * (n : ℝ) + ((cap : ℝ) + 1) +
          2 * P.terminalError n ≤ eta * P.tau / 10 * (n : ℝ)) ∧
      ((n : ℝ) * (cap : ℝ) / 2 ≤
          P.tau ^ 2 * (n : ℝ) ^ 2) ∧
      (P.tau * (n : ℝ) + (delta k : ℝ) +
          (P.tau * (n : ℝ) + 1 +
            P.master * P.tau * (n : ℝ) / 100) +
          (delta k : ℝ) * (eta * P.tau / 10 * (n : ℝ)) ≤
        P.mixedInput * (n : ℝ))) :
    CoreExtractionFinalClusterCertificate nGoal k n
      (overlapClassCount
        (uniformStageTypical (indexedRunTerminalStages R.run)) B.overlapError)
      A.cleaned (eta / P.master) P.mixedInput
      (uniformStageFinalClusters B) := by
  classical
  let run := indexedRunTerminalStages R.run
  let t := overlapClassCount (uniformStageTypical run) B.overlapError
  let clusters : Fin t → Finset (Fin n) := uniformStageFinalClusters B
  let N : ℝ := n
  let cap := coreSeedNonblueCap
    (P.betaSeq (Fin.last P.stageBound)) n
  let sizeError := eta * P.tau / 10000 * N
  let weightedError := P.mixedInput * N
  let ownBlueError := eta * P.tau / 10 * N
  let outsideBlueError := eta * P.tau / 10 * N
  let internalRedError := P.tau ^ 2 * N ^ 2
  have hclusterUnion : clusterUnion clusters = uniformStageFinalUnion B := by
    dsimp only [clusters]
    rfl
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hnPos
  have hetaMaster : 0 < eta / P.master :=
    div_pos heta.1 P.master_pos
  have hcapStages : ∀ q : Fin run.length,
      (uniformStageAt run q).internalNonblueCap ≤ cap := by
    intro q
    simpa [run, cap] using
      indexedRunTerminalStages_internalNonblueCap_le R.run q
  have hbudgets' :
      ((cap : ℝ) + 1 ≤ ownBlueError) ∧
      (sizeError + ((cap : ℝ) + 1) + 2 * P.terminalError n ≤
        outsideBlueError) ∧
      (N * (cap : ℝ) / 2 ≤ internalRedError) ∧
      (P.tau * N + (delta k : ℝ) +
          (P.tau * N + 1 + P.master * P.tau * N / 100) +
          (delta k : ℝ) * outsideBlueError ≤ weightedError) := by
    simpa [cap, N, sizeError, ownBlueError, outsideBlueError,
      internalRedError, weightedError] using hbudgets
  rcases hbudgets' with
    ⟨hownBudget, houtsideBudget, hinternalRedBudget, hweightedBudget⟩
  have hclusterNonempty : ∀ i, (clusters i).Nonempty := by
    intro i
    have hpos : 0 < ((clusters i).card : ℝ) :=
      (mul_pos hetaMaster hN).trans_le (by
        simpa [clusters, t, run, N] using hclusterLower i)
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  have hclusterUpper : ∀ i, ((clusters i).card : ℝ) ≤ N := by
    intro i
    have hnat : (clusters i).card ≤ n := by
      calc
        (clusters i).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = n := by simp
    have hreal : ((clusters i).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnat
    simpa [N] using hreal
  have hclusterCount : (t : ℝ) ≤ P.master / eta := by
    have hraw := card_mul_clusterLower_le_card clusters
      ((eta / P.master) * N) (by simpa [clusters, t, run] using Q.pairwiseDisjoint)
      (by
        intro i
        simpa [clusters, t, run, N] using hclusterLower i)
    have hscaled : (t : ℝ) * (eta / P.master) ≤ 1 := by
      have hraw' : ((t : ℝ) * (eta / P.master)) * N ≤ 1 * N := by
        simpa [mul_assoc] using hraw
      by_contra hnot
      have hgt : 1 < (t : ℝ) * (eta / P.master) := lt_of_not_ge hnot
      exact (not_lt_of_ge hraw') (mul_lt_mul_of_pos_right hgt hN)
    have hscaled' : ((t : ℝ) * eta) / P.master ≤ 1 := by
      simpa [div_eq_mul_inv, mul_assoc] using hscaled
    have hetaBound : (t : ℝ) * eta ≤ P.master :=
      by simpa using (div_le_iff₀ P.master_pos).mp hscaled'
    exact (le_div_iff₀ heta.1).mpr hetaBound
  have hreferencePos : 0 < C.redDegree A.seed := by
    have hreal : (0 : ℝ) < (C.redDegree A.seed : ℝ) := by
      exact (mul_pos heta.1 hN).trans_le (by simpa [N] using A.seed_red_lower)
    exact_mod_cast hreal
  have hreferenceUpper : (C.redDegree A.seed : ℝ) ≤ N := by
    have hnat : C.redDegree A.seed ≤ n := by
      change (C.redNeighborFinset A.seed).card ≤ n
      calc
        (C.redNeighborFinset A.seed).card ≤
            (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = n := by simp
    have hreal : (C.redDegree A.seed : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnat
    simpa [N] using hreal
  have hsizeAround : ∀ i,
      |((clusters i).card : ℝ) -
          (C.redDegree A.seed : ℝ) / (delta k : ℝ)| ≤ sizeError := by
    intro i
    simpa [clusters, t, run, sizeError, N] using hsizeStrong i
  have hbalance : ∀ i j,
      |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| ≤
        P.mixedInput * N := by
    intro i j
    have hcoeff : 2 * eta / 10000 ≤ P.master := by
      have hmaster := P.one_ninety_two_le_master
      nlinarith [heta.2]
    calc
      |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| =
          |(((clusters i).card : ℝ) -
              (C.redDegree A.seed : ℝ) / (delta k : ℝ)) -
            (((clusters j).card : ℝ) -
              (C.redDegree A.seed : ℝ) / (delta k : ℝ))| := by ring_nf
      _ ≤ |((clusters i).card : ℝ) -
              (C.redDegree A.seed : ℝ) / (delta k : ℝ)| +
            |((clusters j).card : ℝ) -
              (C.redDegree A.seed : ℝ) / (delta k : ℝ)| := abs_sub _ _
      _ ≤ 2 * sizeError := by
        have hi := hsizeAround i
        have hj := hsizeAround j
        linarith
      _ = (2 * eta / 10000) * (P.tau * N) := by
        simp only [sizeError]
        ring
      _ ≤ P.master * (P.tau * N) :=
        mul_le_mul_of_nonneg_right hcoeff
          (mul_nonneg P.tau_pos.le hN.le)
      _ = P.mixedInput * N := by rw [P.mixedInput_eq]; ring
  have hdenominator : ∀ i,
      outsideBlueError ≤ P.mixedInput * ((clusters i).card : ℝ) := by
    intro i
    calc
      outsideBlueError ≤ eta * P.tau * N := by
        dsimp [outsideBlueError]
        have hnonneg := mul_nonneg (mul_nonneg heta.1.le P.tau_pos.le) hN.le
        nlinarith
      _ = P.mixedInput * ((eta / P.master) * N) := by
        rw [P.mixedInput_eq]
        field_simp [ne_of_gt P.master_pos]
        <;> ring
      _ ≤ P.mixedInput * ((clusters i).card : ℝ) :=
        mul_le_mul_of_nonneg_left
          (by simpa [clusters, t, run, N] using hclusterLower i)
          P.mixedInput_pos.le
  have hownEstimate : ∀ i v, v ∈ clusters i →
      ((clusters i).card : ℝ) - ownBlueError ≤
        (A.cleaned.blueDegreeIn v (clusters i) : ℝ) := by
    intro i v hv
    have hbase := uniformStageFinalCluster_internalBlueDegree_lower_of_cap
      B cap hcapStages i (by simpa [clusters, t, run] using hv)
    exact (sub_le_sub_left hownBudget ((clusters i).card : ℝ)).trans hbase
  have houtsideEstimate : ∀ i v, v ∈ clusters i →
      (A.cleaned.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
        outsideBlueError := by
    intro i v hv
    have hlower : (C.redDegree A.seed : ℝ) / (delta k : ℝ) - sizeError ≤
        ((uniformStageFinalClusters B i).card : ℝ) := by
      have hi := (abs_le.mp (hsizeAround i)).1
      have hi' : -sizeError ≤
          ((uniformStageFinalClusters B i).card : ℝ) -
            (C.redDegree A.seed : ℝ) / (delta k : ℝ) := by
        simpa only [clusters] using hi
      linarith
    have hbase := uniformStageFinalCluster_outsideBlueDegree_le_of_cap_and_balance
      B cap hcapStages i sizeError hlower (by simpa [clusters, t, run] using hv)
    rw [hclusterUnion]
    simpa only [clusters] using hbase.trans houtsideBudget
  have hblueCompl : ∀ i v, v ∈ clusters i →
      (A.cleaned.blueDegreeIn v (clusterUnion clusters)ᶜ : ℝ) ≤
        outsideBlueError := by
    intro i v hv
    have hlower : (C.redDegree A.seed : ℝ) / (delta k : ℝ) - sizeError ≤
        ((uniformStageFinalClusters B i).card : ℝ) := by
      have hi := (abs_le.mp (hsizeAround i)).1
      have hi' : -sizeError ≤
          ((uniformStageFinalClusters B i).card : ℝ) -
            (C.redDegree A.seed : ℝ) / (delta k : ℝ) := by
        simpa only [clusters] using hi
      linarith
    have hbase := uniformStageFinalUnion_compl_blueDegree_le_of_cap_and_balance
      B cap hcapStages i sizeError hlower (by simpa [clusters, t, run] using hv)
    rw [hclusterUnion]
    simpa only [clusters] using hbase.trans houtsideBudget
  have hweightedEstimate : ∀ i v, v ∈ clusters i →
      |(weightedDegreeIn k A.cleaned v (clusterUnion clusters) : ℝ)| ≤
        weightedError := by
    intro i v hv
    have hvControl : v ∈ A.goodSet :=
      uniformStageFinalCluster_subset_control B i
        (by simpa [clusters, t, run] using hv)
    have hfull := A.goodSet_cleaned_weightedDegree_le P hvControl
    have hfullTau : |(weightedDegree k A.cleaned v : ℝ)| ≤
        P.tau * N + (delta k : ℝ) := by
      calc
        |(weightedDegree k A.cleaned v : ℝ)| ≤
            P.betaSeq 0 * (n : ℝ) + (delta k : ℝ) := hfull
        _ ≤ P.tau * N + (delta k : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_right
            (P.betaSeq_lt_tau 0).le hN.le
          simpa [N] using add_le_add_right hmul (delta k : ℝ)
    have hredCompl := R.terminalFinalUnion_compl_redDegree_le B i
      (by simpa [clusters, t, run] using hv)
    have hredCompl' :
        (A.cleaned.redDegreeIn v (clusterUnion clusters)ᶜ : ℝ) ≤
          P.tau * N + 1 + P.master * P.tau * N / 100 := by
      have hredFinal :
          (A.cleaned.redDegreeIn v (uniformStageFinalUnion B)ᶜ : ℝ) ≤
            P.tau * (n : ℝ) + 1 +
              P.master * P.tau * (n : ℝ) / 100 := by
        calc
          (A.cleaned.redDegreeIn v (uniformStageFinalUnion B)ᶜ : ℝ) ≤
              P.tau * (n : ℝ) + 1 +
                ((uniformStageAmbientUnion (indexedRunTerminalStages R.run) \
                  uniformStageFinalUnion B).card : ℝ) := hredCompl
          _ ≤ P.tau * (n : ℝ) + 1 +
              P.master * P.tau * (n : ℝ) / 100 := by
            linarith [hambientLoss]
      rw [hclusterUnion]
      simpa [N] using hredFinal
    have hrestrict :=
      abs_weightedDegreeIn_le_abs_weightedDegree_add_complDegrees
        k A.cleaned v (clusterUnion clusters)
    calc
      |(weightedDegreeIn k A.cleaned v (clusterUnion clusters) : ℝ)| ≤
          |(weightedDegree k A.cleaned v : ℝ)| +
            ((A.cleaned.redDegreeIn v (clusterUnion clusters)ᶜ : ℝ) +
              (delta k : ℝ) *
                (A.cleaned.blueDegreeIn v (clusterUnion clusters)ᶜ : ℝ)) :=
        hrestrict
      _ ≤ (P.tau * N + (delta k : ℝ)) +
          ((P.tau * N + 1 + P.master * P.tau * N / 100) +
            (delta k : ℝ) * outsideBlueError) := by
        exact add_le_add hfullTau (add_le_add hredCompl'
          (mul_le_mul_of_nonneg_left (hblueCompl i v hv)
            (Nat.cast_nonneg (delta k))))
      _ ≤ weightedError := by simpa [add_assoc] using hweightedBudget
  have hinternalRedEstimate : ∀ i,
      (A.cleaned.redEdgeCountIn (clusters i) : ℝ) ≤ internalRedError := by
    intro i
    have hnonblue : ∀ v ∈ clusters i,
        A.cleaned.redDegreeIn v (clusters i) +
          A.cleaned.greenDegreeIn v (clusters i) ≤ cap := by
      intro v hv
      exact uniformStageFinalCluster_internalNonblue_le_of_cap
        B cap hcapStages i (by simpa [clusters, t, run] using hv)
    calc
      (A.cleaned.redEdgeCountIn (clusters i) : ℝ) ≤
          ((clusters i).card : ℝ) * (cap : ℝ) / 2 :=
        redEdgeCountIn_le_card_mul_internalNonblueCap_div_two
          A.cleaned (clusters i) cap hnonblue
      _ ≤ N * (cap : ℝ) / 2 := by
        gcongr
        exact hclusterUpper i
      _ ≤ internalRedError := hinternalRedBudget
  have hsizeErrorNonneg : 0 ≤ sizeError := by
    dsimp [sizeError]
    exact mul_nonneg
      (div_nonneg (mul_nonneg heta.1.le P.tau_pos.le) (by norm_num)) hN.le
  have hweightedErrorNonneg : 0 ≤ weightedError := by
    exact mul_nonneg P.mixedInput_pos.le hN.le
  have hownBlueErrorNonneg : 0 ≤ ownBlueError := by
    dsimp [ownBlueError]
    exact mul_nonneg
      (div_nonneg (mul_nonneg heta.1.le P.tau_pos.le) (by norm_num)) hN.le
  have houtsideBlueErrorNonneg : 0 ≤ outsideBlueError := by
    dsimp [outsideBlueError]
    exact mul_nonneg
      (div_nonneg (mul_nonneg heta.1.le P.tau_pos.le) (by norm_num)) hN.le
  have hinternalRedErrorNonneg : 0 ≤ internalRedError := by
    exact mul_nonneg (sq_nonneg P.tau) (sq_nonneg N)
  have hsizeCoarse : sizeError ≤ eta * P.tau / 10 * N := by
    dsimp [sizeError]
    have hnonneg := mul_nonneg (mul_nonneg heta.1.le P.tau_pos.le) hN.le
    nlinarith
  have houtsideAmbient : outsideBlueError ≤ P.mixedInput * N := by
    calc
      outsideBlueError ≤ eta * P.tau * N := by
        dsimp [outsideBlueError]
        have hnonneg := mul_nonneg (mul_nonneg heta.1.le P.tau_pos.le) hN.le
        nlinarith
      _ = eta * (P.tau * N) := by ring
      _ ≤ P.master * (P.tau * N) := by
        have hmaster := P.one_ninety_two_le_master
        have hnonneg := mul_nonneg P.tau_pos.le hN.le
        exact mul_le_mul_of_nonneg_right (by linarith [heta.2]) hnonneg
      _ = P.master * P.tau * N := by ring
      _ = P.mixedInput * N := by rw [P.mixedInput_eq]
  refine {
    ambientLarge := hnGoal
    coloring_mem_Ck := A.cleaned_mem_Ck
    clusterCount_ge := ?_
    clusters_pairwiseDisjoint := by simpa [clusters, t, run] using Q.pairwiseDisjoint
    clusterLowerBound := by simpa [clusters, t, run, N] using hclusterLower
    clusterBalanced := by simpa [clusters, t, run, N] using hbalance
    blueSparseBetween := ?_
    vertexControls := ?_
    referenceDegree := C.redDegree A.seed
    referenceDegree_pos := hreferencePos
    sizeError := sizeError
    weightedError := weightedError
    ownBlueError := ownBlueError
    outsideBlueError := outsideBlueError
    internalRedError := internalRedError
    sizeError_nonneg := hsizeErrorNonneg
    weightedError_nonneg := hweightedErrorNonneg
    ownBlueError_nonneg := hownBlueErrorNonneg
    outsideBlueError_nonneg := houtsideBlueErrorNonneg
    internalRedError_nonneg := hinternalRedErrorNonneg
    sizeAroundReference := hsizeAround
    weightedEstimate := hweightedEstimate
    ownBlueEstimate := hownEstimate
    outsideBlueEstimate := houtsideEstimate
    internalRedEstimate := hinternalRedEstimate
    scalarGap := ?_
  }
  · unfold delta at hclassCount ⊢
    omega
  · intro i j hij
    exact blueColorDensity_le_of_outsideDegree_and_denominator
      A.cleaned clusters (by simpa [clusters, t, run] using Q.pairwiseDisjoint)
      hij (hclusterNonempty i) (hclusterNonempty j)
      outsideBlueError P.mixedInput (houtsideEstimate i) (hdenominator j)
  · intro i v hv
    refine ⟨?_, ?_, ?_⟩
    · calc
        (1 - P.mixedInput) * ((clusters i).card : ℝ) =
            ((clusters i).card : ℝ) -
              P.mixedInput * ((clusters i).card : ℝ) := by ring
        _ ≤ ((clusters i).card : ℝ) - ownBlueError := by
          linarith [hdenominator i]
        _ ≤ (A.cleaned.blueDegreeIn v (clusters i) : ℝ) :=
          hownEstimate i v hv
    · exact (houtsideEstimate i v hv).trans houtsideAmbient
    · exact hweightedEstimate i v hv
  · exact CoreExtractionParameters.finalCluster_scalarGap_of_coarse_bounds
      (clusters := clusters) (sizeError := sizeError)
      (weightedError := weightedError) (ownBlueError := ownBlueError)
      (outsideBlueError := outsideBlueError)
      (internalRedError := internalRedError)
      hk heta P hreferencePos (by simpa [N] using A.seed_red_lower)
      hreferenceUpper hclusterUpper hclusterCount hsizeErrorNonneg
      hweightedErrorNonneg hownBlueErrorNonneg houtsideBlueErrorNonneg
      hinternalRedErrorNonneg le_rfl hsizeCoarse le_rfl le_rfl le_rfl

/- Eventual parameter-level F6--F8 input certificate for a supplied terminal
quotient.  All quotient facts remain explicit hypotheses so the outer run
assembly can instantiate this theorem without unpacking hidden state. -/
theorem exists_coreExtractionFinalClusterCertificate_of_terminalQuotient
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    {zeta : ℝ} (P : CoreExtractionParameters k eta zeta) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n),
      ∀ A : CleanedCoreStart k n C eta P.tailScale,
      ∀ R : CleanedCoreSeedRunCertificate P A,
      2 ≤ R.run.length →
      ∀ B : UniformStageOverlapBounds (indexedRunTerminalStages R.run),
      ∀ Q : UniformStageQuotientCertificate
        (indexedRunTerminalStages R.run) B,
      (∀ q, (eta / P.master) * (n : ℝ) ≤
        ((uniformStageFinalClusters B q).card : ℝ)) →
      (∀ q, |((uniformStageFinalClusters B q).card : ℝ) -
          (C.redDegree A.seed : ℝ) / (delta k : ℝ)| ≤
        eta * P.tau / 10000 * (n : ℝ)) →
      (∀ q, |((uniformStageFinalClusters B q).card : ℝ) -
          (C.redDegree A.seed : ℝ) / (delta k : ℝ)| ≤
        P.mixedInput * (n : ℝ)) →
      delta k + 1 ≤ overlapClassCount
        (uniformStageTypical (indexedRunTerminalStages R.run)) B.overlapError →
      ((uniformStageAmbientUnion (indexedRunTerminalStages R.run) \
          uniformStageFinalUnion B).card : ℝ) ≤
        P.master * P.tau * (n : ℝ) / 100 →
      ∀ nGoal, nGoal ≤ n →
        Nonempty (CoreExtractionFinalClusterCertificate nGoal k n
          (overlapClassCount
            (uniformStageTypical (indexedRunTerminalStages R.run))
            B.overlapError)
          A.cleaned (eta / P.master) P.mixedInput
          (uniformStageFinalClusters B)) := by
  obtain ⟨nBudget, hbudget⟩ :=
    exists_coreExtractionFinalClusterInputBudgetThreshold k hk eta heta P
  refine ⟨max 1 nBudget, ?_⟩
  intro n hn C A R htwo B Q hlower hstrong hmixed hclass hambient nGoal hnGoal
  have hnBudget : nBudget ≤ n := (le_max_right 1 nBudget).trans hn
  have hnPos : 0 < n := by
    have : 1 ≤ n := (le_max_left 1 nBudget).trans hn
    omega
  exact ⟨coreExtractionFinalClusterCertificate_of_terminalQuotient_of_budgets
    hk heta P A R htwo B Q hlower hstrong hmixed hclass hambient hnGoal hnPos
    (hbudget n hnBudget)⟩

/-! ### Terminal certificates to the raw extraction geometry -/

/-- Combine the F6--F8 final-cluster certificate, its dominant-color result,
and the three explicit terminal error slots into the transparent F9--F10
geometry certificate.  This is the final transfer from the cleaned coloring
back to the original coloring before the exact F11 objective decomposition.

The three `zeta / 100` slots retain the raw `3 * zeta` loss explicitly. -/
noncomputable def coreExtractionTerminalGeometryCertificate_of_final
    {k n nGoal : ℕ} (_hk : 3 ≤ k) {eta zeta inputDelta : ℝ}
    (hζone : zeta < 1)
    (P : CoreExtractionParameters k eta zeta)
    {C : ColoredGraph (Fin n)}
    (A : CleanedCoreStart k n C eta P.tailScale)
    (R : CleanedCoreSeedRunCertificate P A)
    (B : UniformStageOverlapBounds (indexedRunTerminalStages R.run))
    (F : CoreExtractionFinalClusterCertificate nGoal k n
      (overlapClassCount
        (uniformStageTypical (indexedRunTerminalStages R.run))
        B.overlapError)
      A.cleaned (eta / P.master) P.mixedInput
      (uniformStageFinalClusters B))
    (G : CoreExtractionFinalClusterResult k n
      (overlapClassCount
        (uniformStageTypical (indexedRunTerminalStages R.run))
        B.overlapError)
      A.cleaned (eta / P.master) P.mixedInput
      (uniformStageFinalClusters B))
    (E : CoreExtractionTerminalBudgetCertificate P A R B)
    (hC : C ∈ Ck k n)
    (hnear : -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ)) :
    CoreExtractionTerminalGeometryCertificate
      k n C eta inputDelta zeta P.clusterScale := by
  classical
  have hζ : 0 < zeta := P.zeta_pos
  have hmix : P.mixedInput < zeta := by
    rw [P.mixedInput_eq]
    exact P.master_mul_tau_lt_zeta.trans (by linarith)
  have hdensityError :
      dominantColorConstant k * Real.sqrt P.mixedInput /
          (eta / P.master) ^ 2 < zeta :=
    P.mixedError_lt.trans (by linarith)
  let clusters := uniformStageFinalClusters B
  let reduced := coreExtractionReducedGraph A.cleaned clusters
  let reducedDec : DecidableRel reduced.Adj := Classical.decRel _
  exact {
    retained := A.retained
    covered := indexedStageRunRedNeighborhoodUnion R.run
    finalUnion := uniformStageFinalUnion B
    clusterCount := overlapClassCount
      (uniformStageTypical (indexedRunTerminalStages R.run)) B.overlapError
    clusterCount_ge := F.clusterCount_ge
    clusters := clusters
    clusters_pairwiseDisjoint := F.clusters_pairwiseDisjoint
    clusterUnion_eq := coreExtractionClusterUnion_uniformStageFinalClusters B
    finalUnion_subset_covered := R.terminalFinalUnion_subset_covered B
    covered_subset_retained := R.covered_subset_retained
    reducedGraph := reduced
    reducedGraphAdjDecidable := reducedDec
    reducedGraph_regular := by
      dsimp only [reduced]
      exact G.reducedGraph_regular reducedDec
    cleanedBlueDegree := by
      intro i v hv
      rw [← A.cleaned_eq]
      have hblue := (F.vertexControls i v hv).1
      have hcard : 0 ≤ ((clusters i).card : ℝ) := by positivity
      calc
        (1 - zeta) * (((clusters i).card : ℝ) - 1) ≤
            (1 - zeta) * ((clusters i).card : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        _ ≤ (1 - P.mixedInput) * ((clusters i).card : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by linarith) hcard
        _ ≤ (A.cleaned.blueDegreeIn v (clusters i) : ℝ) := hblue
    clusterLowerBound := by
      intro i
      have hscale : P.clusterScale ≤ eta / P.master := by
        rw [P.clusterScale_eq]
        have hmaster : 0 < P.master := P.master_pos
        have heta : 0 < eta := by
          have hprod : 0 < P.master * P.tau :=
            mul_pos P.master_pos P.tau_pos
          have : P.master * P.tau < eta / 100 := P.tau_lt_eta
          nlinarith
        calc
          eta / (2 * P.master) = (eta / P.master) / 2 := by
            field_simp [ne_of_gt hmaster]
          _ ≤ eta / P.master := by
            have := div_pos heta hmaster
            linarith
      exact (mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg n)).trans
        (F.clusterLowerBound i)
    clusterBalanced := by
      intro i j
      exact (F.clusterBalanced i j).trans
        (mul_le_mul_of_nonneg_right hmix.le (Nat.cast_nonneg n))
    finalUnionLarge := E.finalUnionLarge
    cleanedRedDenseOnEdges := by
      intro i j hij
      rw [← A.cleaned_eq]
      exact (by linarith [G.redDenseOnEdges i j hij])
    cleanedGreenDenseOnNonedges := by
      intro i j hij hnonadj
      rw [← A.cleaned_eq]
      exact (by
        linarith [
          (G.redSmallGreenDenseOnNonedges i j hij hnonadj).2])
    retainedError := zeta / 100
    uncoveredError := zeta / 100
    boundaryError := zeta / 100
    retainedError_nonneg := by positivity
    uncoveredError_nonneg := by positivity
    boundaryError_nonneg := by positivity
    errorBudget := E.threeErrorSlots_le
    retainedComplementSmall := E.retainedComplementSmall
    uncoveredSmall := E.uncoveredSmall
    cleanedBoundaryPointwise := by
      intro v hv
      rw [← A.cleaned_eq]
      exact E.cleanedBoundaryPointwise v hv
    coloring_mem_Ck := hC
    wholeNearExtremal := by
      have hn : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      nlinarith
    coreMantelAbsorbed := E.coreMantelAbsorbed
  }

/-! ## The raw and paper-facing core-extraction recursion -/

/-- End-to-end constructor for the raw `zeta`-level extraction result at a
fixed parameter package.  One threshold simultaneously covers cleaning, the
nontrivial indexed run, the terminal overlap quotient, the F6--F8
dominant-color certificate, and the F9--F11 error budgets.

The weighted-degree tail theorem is invoked at the package's fixed
`tailScale`, before `inputDelta` is quantified. The conclusion
retains the three accumulated `zeta` losses. -/
theorem exists_coreExtractionRawResult_of_parameters
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (zeta : ℝ) (hzeta : zeta ∈ Set.Ioo (0 : ℝ) (eta / 60))
    (P : CoreExtractionParameters k eta zeta) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) P.finalDelta₀,
      ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
        -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
        (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
        Nonempty (CoreExtractionRawResult
          k n C eta inputDelta zeta P.clusterScale) := by
  have hetaQuotient : eta / P.master ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos heta.1 P.master_pos
    · rw [div_lt_one P.master_pos]
      linarith [heta.2, P.one_ninety_two_le_master]
  have hmixedInput : P.mixedInput ∈
      Set.Ioo (0 : ℝ) (dominantColorBeta₀ k (eta / P.master)) :=
    ⟨P.mixedInput_pos, P.mixedInput_lt_threshold⟩
  obtain ⟨nTail, htail⟩ :=
    exists_cleanedCoreStart_tailThreshold
      k hk eta P.tailScale P.tailScale_mem
  obtain ⟨nRun, hrun⟩ :=
    exists_nontrivial_cleanedCoreSeedRunCertificate k hk eta heta P
  obtain ⟨nQuotient, hquotient⟩ :=
    exists_terminalQuotient_of_indexedRun k hk eta heta P
  obtain ⟨nFinal, hfinal⟩ :=
    exists_coreExtractionFinalClusterCertificate_of_terminalQuotient
      k hk eta heta P
  obtain ⟨nGoal, hgoal⟩ :=
    exists_coreExtractionFinalClusterResultThreshold
      k hk (eta / P.master) hetaQuotient P.mixedInput hmixedInput
  let n₀ := max nTail
    (max nRun
      (max nQuotient
        (max nFinal (max nGoal P.terminalBudgetThreshold))))
  refine ⟨n₀, ?_⟩
  intro n hn inputDelta hinputDelta C hC hnear hred
  dsimp only [n₀] at hn
  have hnRest₁ :
      max nRun
        (max nQuotient
          (max nFinal (max nGoal P.terminalBudgetThreshold))) ≤ n :=
    (le_max_right nTail _).trans hn
  have hnTail : nTail ≤ n := (le_max_left nTail _).trans hn
  have hnRest₂ :
      max nQuotient
        (max nFinal (max nGoal P.terminalBudgetThreshold)) ≤ n :=
    (le_max_right nRun _).trans hnRest₁
  have hnRun : nRun ≤ n := (le_max_left nRun _).trans hnRest₁
  have hnRest₃ : max nFinal (max nGoal P.terminalBudgetThreshold) ≤ n :=
    (le_max_right nQuotient _).trans hnRest₂
  have hnQuotient : nQuotient ≤ n :=
    (le_max_left nQuotient _).trans hnRest₂
  have hnRest₄ : max nGoal P.terminalBudgetThreshold ≤ n :=
    (le_max_right nFinal _).trans hnRest₃
  have hnFinal : nFinal ≤ n := (le_max_left nFinal _).trans hnRest₃
  have hnGoal : nGoal ≤ n := (le_max_left nGoal _).trans hnRest₄
  have hnBudget : P.terminalBudgetThreshold ≤ n :=
    (le_max_right nGoal _).trans hnRest₄
  have hinputTail : inputDelta ∈ Set.Ioc (0 : ℝ) P.tailScale :=
    ⟨hinputDelta.1,
      hinputDelta.2.le.trans P.finalDelta₀_le_tailScale⟩
  obtain ⟨A⟩ :=
    htail n hnTail inputDelta hinputTail C hC hnear hred
  obtain ⟨R, htwo⟩ := hrun n hnRun C A
  have hrunNonempty : R.run ≠ [] := BoundedRunValid.nonempty R.valid
  obtain ⟨B, Q, _hclusterScale, hclusterLower, hstrongBalance,
      hmixedBalance, _hdeltaClasses, hnewClass, hambientLoss⟩ :=
    hquotient n hnQuotient A.cleaned A.goodSet
      (C.redDegree A.seed : ℝ) R.run A.seed_red_lower
      hrunNonempty (R.length_le.trans (Nat.sub_le _ _))
  have hclassCount : delta k + 1 ≤ overlapClassCount
      (uniformStageTypical (indexedRunTerminalStages R.run))
      B.overlapError :=
    R.delta_add_one_le_terminalOverlapClassCount htwo B hnewClass
  obtain ⟨F⟩ := hfinal n hnFinal C A R htwo B Q hclusterLower
    hstrongBalance hmixedBalance hclassCount hambientLoss nGoal hnGoal
  let G : CoreExtractionFinalClusterResult k n
      (overlapClassCount
        (uniformStageTypical (indexedRunTerminalStages R.run))
        B.overlapError)
      A.cleaned (eta / P.master) P.mixedInput
      (uniformStageFinalClusters B) := hgoal F
  let E : CoreExtractionTerminalBudgetCertificate P A R B :=
    coreExtractionTerminalBudgetCertificate_of_large
      hk heta P A R B hnBudget hambientLoss
  have hzetaOne : zeta < 1 := by
    nlinarith [hzeta.2, heta.2]
  let T : CoreExtractionTerminalGeometryCertificate
      k n C eta inputDelta zeta P.clusterScale :=
    coreExtractionTerminalGeometryCertificate_of_final
      hk hzetaOne P A R B F G E hC hnear
  exact ⟨T.toAssemblyCertificate.toRawResult hk⟩

/-- Outer parameter-selection adapter.  The cluster scale `c` is selected
from `k,eta` before the raw error parameter and hence is uniform in `zeta`. -/
theorem kthOrderRecursionRaw_of_parameters
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (construct : ∀ (zeta : ℝ)
        (_hzeta : zeta ∈ Set.Ioo (0 : ℝ) (eta / 60))
        (P : CoreExtractionParameters k eta zeta),
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) P.finalDelta₀,
        ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
          -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
          (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
          Nonempty
            (CoreExtractionRawResult
              k n C eta inputDelta zeta P.clusterScale)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ zeta ∈ Set.Ioo (0 : ℝ) (eta / 60),
        ∃ delta₀ : ℝ, delta₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ n₀ : ℕ,
          ∀ n ≥ n₀, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) delta₀,
            ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
              -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
              (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
              Nonempty
                (CoreExtractionRawResult
                  k n C eta inputDelta zeta c) := by
  obtain ⟨c, hc, hparameters⟩ :=
    exists_coreExtractionParameters k hk eta heta
  refine ⟨c, hc, ?_⟩
  intro zeta hzeta
  obtain ⟨P, hPc⟩ := hparameters zeta hzeta
  obtain ⟨n₀, hconstruct⟩ := construct zeta hzeta P
  refine ⟨P.finalDelta₀, P.finalDelta₀_mem, n₀, ?_⟩
  intro n hn inputDelta hinputDelta C hC hnear hred
  simpa only [hPc] using
    hconstruct n hn inputDelta hinputDelta C hC hnear hred

/-- Raw form of `lemma:kth-order-recursion` with local error `zeta` and the
three accumulated coverage/remainder losses exposed as `3 * zeta`.

The quantifier order already selects `c = c(k,eta)` before `zeta`; the final
paper-facing theorem below changes only the error scale. -/
theorem kthOrderRecursionRaw
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ zeta ∈ Set.Ioo (0 : ℝ) (eta / 60),
        ∃ delta₀ : ℝ, delta₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ n₀ : ℕ,
          ∀ n ≥ n₀, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) delta₀,
            ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
              -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
              (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
              Nonempty
                (CoreExtractionRawResult
                  k n C eta inputDelta zeta c) := by
  apply kthOrderRecursionRaw_of_parameters k hk eta heta
  intro zeta hzeta P
  exact exists_coreExtractionRawResult_of_parameters
    k hk eta heta zeta hzeta P

/-- Quantifier-and-rescaling adapter from the raw three-loss recursion to the
paper-facing statement. -/
theorem kthOrderRecursion_of_raw
    (k : ℕ) (_hk : 3 ≤ k) (eta : ℝ)
    (_heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (hraw : ∃ c : ℝ, 0 < c ∧
      ∀ zeta ∈ Set.Ioo (0 : ℝ) (eta / 60),
        ∃ delta₀ : ℝ, delta₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ n₀ : ℕ,
          ∀ n ≥ n₀, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) delta₀,
            ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
              -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
              (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
              Nonempty
                (CoreExtractionRawResult
                  k n C eta inputDelta zeta c)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ xi ∈ Set.Ioo (0 : ℝ) (eta / 20),
        ∃ delta₀ : ℝ, delta₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ n₀ : ℕ,
          ∀ n ≥ n₀, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) delta₀,
            ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
              -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
              (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
              Nonempty
                (CoreExtractionResult
                  k n C eta inputDelta xi c) := by
  obtain ⟨c, hc, hraw⟩ := hraw
  refine ⟨c, hc, ?_⟩
  intro xi hxi
  have hzeta : xi / 3 ∈ Set.Ioo (0 : ℝ) (eta / 60) := by
    constructor
    · linarith [hxi.1]
    · nlinarith [hxi.2]
  obtain ⟨delta₀, hdelta₀, n₀, hn₀⟩ := hraw (xi / 3) hzeta
  refine ⟨delta₀, hdelta₀, n₀, ?_⟩
  intro n hn inputDelta hinputDelta C hC hnear hred
  obtain ⟨R⟩ := hn₀ n hn inputDelta hinputDelta C hC hnear hred
  exact ⟨R.toCoreExtractionResult
    (CoreExtractionRawResult.third_local hxi.1.le)
    (by simpa using CoreExtractionRawResult.three_mul_third xi)⟩

/-- Paper-facing formalization of `lemma:kth-order-recursion`.

For fixed `k ≥ 3` and `eta ∈ (0,1)`, the positive cluster scale `c` is
chosen before `xi`.  The returned `CoreExtractionResult` exposes all six
paper conclusions: blue-dense balanced clusters of size at least `c*n`, a
`delta k`-regular red reduced graph with green-dense distinct nonedges, a
small exceptional set and red/blue boundary, large covered mass, and the
exact `inputDelta + xi` remainder objective bound.

The proof uses a fixed tail scale, adjacent input/output seed scales,
and an explicit integer gap for the reduced degree. -/
theorem kthOrderRecursion
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ xi ∈ Set.Ioo (0 : ℝ) (eta / 20),
        ∃ delta₀ : ℝ, delta₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ n₀ : ℕ,
          ∀ n ≥ n₀, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) delta₀,
            ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
              -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
              (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
              Nonempty
                (CoreExtractionResult
                  k n C eta inputDelta xi c) := by
  exact kthOrderRecursion_of_raw k hk eta heta
    (kthOrderRecursionRaw k hk eta heta)

end ColoredGraph

end InducedStars
