import InducedStars.Analysis.ScalarOptimization
import InducedStars.Graphon.Densities
import InducedStars.Graphon.Star
import InducedStars.Graphon.StepEstimates
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The explicit block graphons in the fixed-density optimizer family

This file contains the finite regular cores, their equal-cell graphons, and
the countable interval construction used for the paper's finite or infinite
block sequences.  The analytic functionals and the final optimizer family are
kept in later files.
-/

noncomputable section

open Filter MeasureTheory Set SimpleGraph
open scoped BigOperators ENNReal unitInterval

namespace InducedStars

/-- A fixed classical adjacency decision for every finite core.  Keeping this
instance in one place makes Mathlib's locally-finite degree API definitionally
stable throughout the bundled core interface. -/
local instance finiteCoreAdjDecidable {n : ℕ} (G : SimpleGraph (Fin n)) :
    DecidableRel G.Adj :=
  Classical.decRel _

/-! ## Connected regular finite cores -/

/-- A connected `(k - 2)`-regular graph used inside one candidate block. -/
structure RegularBlockCore (k : ℕ) where
  order : ℕ
  order_pos : 0 < order
  graph : SimpleGraph (Fin order)
  connected : graph.Connected
  regular : graph.IsRegularOfDegree (k - 2)

namespace RegularBlockCore

theorem degree_eq {k : ℕ} (C : RegularBlockCore k) (v : Fin C.order) :
    C.graph.degree v = k - 2 := by
  classical
  exact C.regular.degree_eq v

/-- Degree summation in a regular core, in the ordered-edge normalization. -/
theorem sum_degrees {k : ℕ} (C : RegularBlockCore k) :
    ∑ v : Fin C.order, C.graph.degree v = C.order * (k - 2) := by
  classical
  simp [C.degree_eq]

/-- The handshaking identity for a regular core. -/
theorem twice_card_edges {k : ℕ} (C : RegularBlockCore k) :
    2 * C.graph.edgeFinset.card = C.order * (k - 2) := by
  classical
  rw [← C.graph.sum_degrees_eq_twice_card_edges, C.sum_degrees]

/-- The paper's divided-by-two form of the regular-core edge count. -/
theorem card_edges {k : ℕ} (C : RegularBlockCore k) :
    C.graph.edgeFinset.card = C.order * (k - 2) / 2 := by
  rw [← C.twice_card_edges]
  omega

/-- A simple `(k-2)`-regular core has at least `k-1` vertices. -/
theorem k_sub_one_le_order {k : ℕ} (hk : 3 ≤ k) (C : RegularBlockCore k) :
    k - 1 ≤ C.order := by
  classical
  let v : Fin C.order := ⟨0, C.order_pos⟩
  have hdeg_lt : C.graph.degree v < C.order := by
    simpa using C.graph.degree_lt_card_verts v
  rw [C.degree_eq] at hdeg_lt
  omega

/-- The complete graph on `k-1` vertices, packaged as a regular block core. -/
def complete (k : ℕ) (hk : 3 ≤ k) : RegularBlockCore k where
  order := k - 1
  order_pos := by omega
  graph := ⊤
  connected := by
    let _ : Nonempty (Fin (k - 1)) := Fin.pos_iff_nonempty.mp (by omega)
    exact SimpleGraph.connected_top
  regular := by
    intro v
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.top_adj, Finset.filter_ne]
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    simp only [Fintype.card_fin]
    omega

@[simp] theorem complete_order (k : ℕ) (hk : 3 ≤ k) :
    (complete k hk).order = k - 1 :=
  rfl

end RegularBlockCore

/-! ## Arbitrary-profile finite-core matrices -/

section

/-- A stable classical adjacency decision for finite cores in this module. -/
local instance profileFiniteCoreAdjDecidable {n : ℕ}
    (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

/-- The profile-valued core matrix: one on the diagonal, `p` on core edges,
and zero on core nonedges. -/
def profileXiMatrix {k : ℕ} (p : ℝ) (C : RegularBlockCore k) :
    Matrix (Fin C.order) (Fin C.order) ℝ := by
  classical
  exact fun i j ↦ if i = j then 1 else if C.graph.Adj i j then p else 0

@[simp] theorem profileXiMatrix_apply_eq {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (i : Fin C.order) :
    profileXiMatrix p C i i = 1 := by
  simp [profileXiMatrix]

theorem profileXiMatrix_apply_of_adj {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) {i j : Fin C.order} (hij : C.graph.Adj i j) :
    profileXiMatrix p C i j = p := by
  simp [profileXiMatrix, C.graph.ne_of_adj hij, hij]

theorem profileXiMatrix_apply_of_ne_of_not_adj {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) {i j : Fin C.order} (hne : i ≠ j)
    (hij : ¬ C.graph.Adj i j) :
    profileXiMatrix p C i j = 0 := by
  simp [profileXiMatrix, hne, hij]

theorem profileXiMatrix_isSymm {k : ℕ} (p : ℝ) (C : RegularBlockCore k) :
    (profileXiMatrix p C).IsSymm := by
  classical
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp only [profileXiMatrix, hij, hji, ite_false]
    simp [C.graph.adj_comm]

theorem profileXiMatrix_nonneg {k : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (C : RegularBlockCore k) (i j : Fin C.order) :
    0 ≤ profileXiMatrix p C i j := by
  simp only [profileXiMatrix]
  split_ifs <;> simp_all

theorem profileXiMatrix_le_one {k : ℕ} {p : ℝ} (hp : p ≤ 1)
    (C : RegularBlockCore k) (i j : Fin C.order) :
    profileXiMatrix p C i j ≤ 1 := by
  simp only [profileXiMatrix]
  split_ifs <;> simp_all

theorem sum_profileXiMatrix_row {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (i : Fin C.order) :
    ∑ j : Fin C.order, profileXiMatrix p C i j =
      1 + (C.graph.degree i : ℝ) * p := by
  classical
  calc
    ∑ j : Fin C.order, profileXiMatrix p C i j =
        (∑ j : Fin C.order, if j = i then (1 : ℝ) else 0) +
          ∑ j : Fin C.order, if C.graph.Adj i j then p else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp [profileXiMatrix]
      · have hij : i ≠ j := Ne.symm hji
        simp [profileXiMatrix, hji, hij]
    _ = 1 + ∑ j : Fin C.order,
          if C.graph.Adj i j then p else 0 := by simp
    _ = 1 + (C.graph.degree i : ℝ) * p := by
      congr 1
      rw [← Finset.sum_filter]
      simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]

theorem sum_profileXiMatrix {k : ℕ} (p : ℝ) (C : RegularBlockCore k) :
    ∑ i : Fin C.order, ∑ j : Fin C.order, profileXiMatrix p C i j =
      (C.order : ℝ) * (1 + ((k - 2 : ℕ) : ℝ) * p) := by
  classical
  simp_rw [sum_profileXiMatrix_row, C.degree_eq]
  simp
  ring

theorem sum_binaryEntropy_profileXiMatrix_row {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (i : Fin C.order) :
    ∑ j : Fin C.order, binaryEntropy (profileXiMatrix p C i j) =
      (C.graph.degree i : ℝ) * binaryEntropy p := by
  classical
  calc
    ∑ j : Fin C.order, binaryEntropy (profileXiMatrix p C i j) =
        ∑ j : Fin C.order,
          if C.graph.Adj i j then binaryEntropy p else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp [profileXiMatrix]
      · by_cases hadj : C.graph.Adj i j <;>
          simp [profileXiMatrix, hij, hadj]
    _ = (C.graph.degree i : ℝ) * binaryEntropy p := by
      rw [← Finset.sum_filter]
      simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]

theorem sum_binaryEntropy_profileXiMatrix {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) :
    ∑ i : Fin C.order, ∑ j : Fin C.order,
        binaryEntropy (profileXiMatrix p C i j) =
      (C.order : ℝ) * ((k - 2 : ℕ) : ℝ) * binaryEntropy p := by
  classical
  simp_rw [sum_binaryEntropy_profileXiMatrix_row, C.degree_eq]
  simp
  ring

end

/-! ## The finite building block `xi_G` -/

/-- The matrix of the paper's graphon `xi_G`: one on the diagonal, `p_k` on
core edges, and zero on core nonedges. -/
def xiMatrix {k : ℕ} (C : RegularBlockCore k) :
    Matrix (Fin C.order) (Fin C.order) ℝ := by
  classical
  exact fun i j ↦ if i = j then 1 else if C.graph.Adj i j then pK k else 0

theorem xiMatrix_apply_eq {k : ℕ} (C : RegularBlockCore k) (i : Fin C.order) :
    xiMatrix C i i = 1 :=
  profileXiMatrix_apply_eq (pK k) C i

theorem xiMatrix_apply_of_adj {k : ℕ} (C : RegularBlockCore k)
    {i j : Fin C.order} (hij : C.graph.Adj i j) :
    xiMatrix C i j = pK k :=
  profileXiMatrix_apply_of_adj (pK k) C hij

theorem xiMatrix_apply_of_ne_of_not_adj {k : ℕ} (C : RegularBlockCore k)
    {i j : Fin C.order} (hne : i ≠ j) (hij : ¬ C.graph.Adj i j) :
    xiMatrix C i j = 0 :=
  profileXiMatrix_apply_of_ne_of_not_adj (pK k) C hne hij

theorem xiMatrix_isSymm {k : ℕ} (C : RegularBlockCore k) :
    (xiMatrix C).IsSymm :=
  profileXiMatrix_isSymm (pK k) C

theorem xiMatrix_nonneg {k : ℕ} (hk : 3 ≤ k) (C : RegularBlockCore k)
    (i j : Fin C.order) : 0 ≤ xiMatrix C i j :=
  profileXiMatrix_nonneg (pK_pos (by omega : 2 ≤ k)).le C i j

theorem xiMatrix_le_one {k : ℕ} (hk : 3 ≤ k) (C : RegularBlockCore k)
    (i j : Fin C.order) : xiMatrix C i j ≤ 1 :=
  profileXiMatrix_le_one (pK_lt_one (by omega : 2 ≤ k)).le C i j

/-- A finite-core matrix entry is nonzero exactly on the closed
neighborhood relation. -/
theorem xiMatrix_ne_zero_iff {k : ℕ} (hk : 3 ≤ k)
    (C : RegularBlockCore k) (i j : Fin C.order) :
    xiMatrix C i j ≠ 0 ↔ i = j ∨ C.graph.Adj i j := by
  constructor
  · intro h
    by_cases hij : i = j
    · exact Or.inl hij
    · by_cases hadj : C.graph.Adj i j
      · exact Or.inr hadj
      · exact (h (xiMatrix_apply_of_ne_of_not_adj C hij hadj)).elim
  · rintro (rfl | hij)
    · rw [xiMatrix_apply_eq]
      norm_num
    · rw [xiMatrix_apply_of_adj C hij]
      exact (pK_pos (by omega : 2 ≤ k)).ne'

/-- The paper's equal-cell graphon `xi_G`. -/
def xiGraphon {k : ℕ} (hk : 3 ≤ k) (C : RegularBlockCore k) : Graphon :=
  matrixGraphon (xiMatrix C) (xiMatrix_isSymm C)
    (xiMatrix_nonneg hk C) (xiMatrix_le_one hk C)

/-! ### Exact finite-block formulas -/

theorem sum_xiMatrix_row {k : ℕ} (C : RegularBlockCore k) (i : Fin C.order) :
    ∑ j : Fin C.order, xiMatrix C i j =
      1 + (C.graph.degree i : ℝ) * pK k :=
  sum_profileXiMatrix_row (pK k) C i

theorem sum_xiMatrix {k : ℕ} (C : RegularBlockCore k) :
    ∑ i : Fin C.order, ∑ j : Fin C.order, xiMatrix C i j =
      (C.order : ℝ) * (1 + ((k - 2 : ℕ) : ℝ) * pK k) :=
  sum_profileXiMatrix (pK k) C

theorem sum_binaryEntropy_xiMatrix_row {k : ℕ} (C : RegularBlockCore k)
    (i : Fin C.order) :
    ∑ j : Fin C.order, binaryEntropy (xiMatrix C i j) =
      (C.graph.degree i : ℝ) * binaryEntropy (pK k) :=
  sum_binaryEntropy_profileXiMatrix_row (pK k) C i

theorem sum_binaryEntropy_xiMatrix {k : ℕ} (C : RegularBlockCore k) :
    ∑ i : Fin C.order, ∑ j : Fin C.order, binaryEntropy (xiMatrix C i j) =
      (C.order : ℝ) * ((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k) :=
  sum_binaryEntropy_profileXiMatrix (pK k) C

/-- Edge density of the paper's finite building block `xi_G`. -/
theorem xiGraphon_edgeDensity {k : ℕ} (hk : 3 ≤ k) (C : RegularBlockCore k) :
    graphonEdgeDensity (xiGraphon hk C) =
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) / C.order := by
  rw [xiGraphon, graphonEdgeDensity_matrixGraphon C.order_pos,
    sum_xiMatrix]
  have horder : (C.order : ℝ) ≠ 0 := by exact_mod_cast C.order_pos.ne'
  field_simp

/-- Entropy of the paper's finite building block `xi_G`. -/
theorem xiGraphon_entropy {k : ℕ} (hk : 3 ≤ k) (C : RegularBlockCore k) :
    graphonEntropy (xiGraphon hk C) =
      ((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k) / C.order := by
  rw [xiGraphon, graphonEntropy_matrixGraphon C.order_pos,
    sum_binaryEntropy_xiMatrix]
  have horder : (C.order : ℝ) ≠ 0 := by exact_mod_cast C.order_pos.ne'
  field_simp

/-- Integrate a finite matrix of constant rectangle indicators. No disjointness
or positivity is needed; all summands are integrable on the unit square. -/
theorem integral_doubleSum_cellIndicators {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : ι → Set UnitInterval) (T : κ → Set UnitInterval)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (M : ι → κ → ℝ) :
    (∫ z : UnitSquare, ∑ i, ∑ j,
      (S i ×ˢ T j).indicator (fun _ ↦ M i j) z ∂unitSquareMeasure) =
      ∑ i, ∑ j, unitSquareMeasure.real (S i ×ˢ T j) * M i j := by
  have hi i j : Integrable
      ((S i ×ˢ T j).indicator (fun _ : UnitSquare ↦ M i j))
        unitSquareMeasure :=
    (integrable_const _).indicator ((hS i).prod (hT j))
  rw [integral_finsetSum _ (fun i _ ↦
    integrable_finsetSum _ (fun j _ ↦ hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ ↦ hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator_const _ ((hS i).prod (hT j)), smul_eq_mul]

/-! ### Induced-star freeness of a finite block -/

theorem xiMatrix_inducedStar_weight_zero {k : ℕ} (hk : 3 ≤ k)
    (C : RegularBlockCore k) (φ : Fin (k + 1) → Fin C.order) :
    matrixInducedMapWeight (inducedStar k) (xiMatrix C)
      (xiMatrix_isSymm C) φ = 0 := by
  classical
  by_cases hbad : ∃ a : Fin k, xiMatrix C (φ 0) (φ a.succ) = 0
  · obtain ⟨a, ha⟩ := hbad
    have hEdge : s(0, a.succ) ∈ finiteGraphEdges (inducedStar k) := by
      simpa using inducedStar_center_adj_leaf a
    have hEdgeProd :
        (∏ e ∈ finiteGraphEdges (inducedStar k),
          matrixMapPairValue (xiMatrix C) (xiMatrix_isSymm C) φ e) = 0 := by
      rw [Finset.prod_eq_zero_iff]
      exact ⟨s(0, a.succ), hEdge, by simpa using ha⟩
    unfold matrixInducedMapWeight
    rw [hEdgeProd, zero_mul]
  · have hcenter (a : Fin k) :
        xiMatrix C (φ 0) (φ a.succ) ≠ 0 := by
      intro ha
      exact hbad ⟨a, ha⟩
    let closed : Finset (Fin C.order) :=
      insert (φ 0) (C.graph.neighborFinset (φ 0))
    have hmem (a : Fin k) : φ a.succ ∈ closed := by
      rw [show closed = insert (φ 0) (C.graph.neighborFinset (φ 0)) from rfl,
        Finset.mem_insert, C.graph.mem_neighborFinset]
      rcases (xiMatrix_ne_zero_iff hk C _ _).mp (hcenter a) with heq | hadj
      · exact Or.inl heq.symm
      · exact Or.inr hadj
    let ψ : Fin k → {x // x ∈ closed} := fun a ↦ ⟨φ a.succ, hmem a⟩
    by_cases hinj : Function.Injective ψ
    · have hcardle : Fintype.card (Fin k) ≤ Fintype.card {x // x ∈ closed} :=
        Fintype.card_le_of_injective ψ hinj
      have hcard : closed.card = k - 1 := by
        rw [show closed = insert (φ 0) (C.graph.neighborFinset (φ 0)) from rfl,
          Finset.card_insert_of_notMem (C.graph.notMem_neighborFinset_self (φ 0)),
          C.graph.card_neighborFinset_eq_degree, C.degree_eq]
        omega
      have : k ≤ k - 1 := by
        simpa [hcard] using hcardle
      omega
    · simp only [Function.Injective] at hinj
      push Not at hinj
      obtain ⟨a, b, hab, hne⟩ := hinj
      have hlabels : φ a.succ = φ b.succ := congrArg Subtype.val hab
      have hNonedge : s(a.succ, b.succ) ∈
          finiteGraphEdges (inducedStar k)ᶜ := by
        have hsucc : a.succ ≠ b.succ := by simpa using hne
        simp [hsucc]
      have hNonedgeProd :
          (∏ e ∈ finiteGraphEdges (inducedStar k)ᶜ,
            (1 - matrixMapPairValue (xiMatrix C) (xiMatrix_isSymm C) φ e)) = 0 := by
        rw [Finset.prod_eq_zero_iff]
        refine ⟨s(a.succ, b.succ), hNonedge, ?_⟩
        rw [matrixMapPairValue_mk, hlabels, xiMatrix_apply_eq]
        ring
      unfold matrixInducedMapWeight
      rw [hNonedgeProd, mul_zero]

/-- Every finite building block is induced-`K_{1,k}`-free. -/
theorem xiGraphon_inducedStar_free {k : ℕ} (hk : 3 ≤ k)
    (C : RegularBlockCore k) :
    graphonInducedDensity (inducedStar k) (xiGraphon hk C) = 0 := by
  unfold xiGraphon
  apply graphonInducedDensity_matrixGraphon_eq_zero_of_weights C.order_pos
  exact xiMatrix_inducedStar_weight_zero hk C

/-! ## Finite or infinite admissible block sequences -/

/-- Active indices for an optional finite length. `none` means that every
natural-number index is active. -/
def blockIndexActive (count : Option ℕ) (i : ℕ) : Prop :=
  match count with
  | none => True
  | some n => i < n

instance (count : Option ℕ) (i : ℕ) : Decidable (blockIndexActive count i) :=
  Classical.propDecidable _

/-- A finite or infinite sequence of positive, nonincreasing block lengths
and connected regular cores. In the finite case inactive lengths are exactly
zero. The total length is at most one, leaving a possible zero-valued tail. -/
structure AdmissibleBlockSequence (k : ℕ) where
  count : Option ℕ
  count_pos : ∀ n, count = some n → 0 < n
  alpha : ℕ → ℝ
  core : ℕ → RegularBlockCore k
  alpha_pos_of_active : ∀ i, blockIndexActive count i → 0 < alpha i
  alpha_eq_zero_of_inactive : ∀ i, ¬ blockIndexActive count i → alpha i = 0
  alpha_antitone : Antitone alpha
  summable_alpha : Summable alpha
  tsum_alpha_le_one : ∑' i, alpha i ≤ 1

namespace AdmissibleBlockSequence

variable {k : ℕ} (L : AdmissibleBlockSequence k)

theorem alpha_nonneg (i : ℕ) : 0 ≤ L.alpha i := by
  by_cases hi : blockIndexActive L.count i
  · exact (L.alpha_pos_of_active i hi).le
  · rw [L.alpha_eq_zero_of_inactive i hi]

theorem alpha_le_one (i : ℕ) : L.alpha i ≤ 1 := by
  calc
    L.alpha i ≤ ∑' j, L.alpha j :=
      L.summable_alpha.le_tsum i (fun j _ ↦ L.alpha_nonneg j)
    _ ≤ 1 := L.tsum_alpha_le_one

/-- The left endpoint of block `i`, i.e. the sum of preceding lengths. -/
def blockStart (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, L.alpha j

/-- The right endpoint of block `i`. -/
def blockEnd (i : ℕ) : ℝ :=
  L.blockStart i + L.alpha i

@[simp] theorem blockStart_zero : L.blockStart 0 = 0 := by
  simp [blockStart]

theorem blockStart_succ (i : ℕ) : L.blockStart (i + 1) = L.blockEnd i := by
  simp [blockStart, blockEnd, Finset.sum_range_succ]

theorem blockStart_nonneg (i : ℕ) : 0 ≤ L.blockStart i := by
  exact Finset.sum_nonneg fun j _ ↦ L.alpha_nonneg j

theorem blockStart_le_tsum (i : ℕ) : L.blockStart i ≤ ∑' j, L.alpha j := by
  exact L.summable_alpha.sum_le_tsum (Finset.range i) fun j _ ↦ L.alpha_nonneg j

theorem blockStart_le_one (i : ℕ) : L.blockStart i ≤ 1 :=
  (L.blockStart_le_tsum i).trans L.tsum_alpha_le_one

theorem blockStart_mono : Monotone L.blockStart := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hij
  · intro n _ _
    exact L.alpha_nonneg n

theorem blockEnd_nonneg (i : ℕ) : 0 ≤ L.blockEnd i := by
  exact add_nonneg (L.blockStart_nonneg i) (L.alpha_nonneg i)

theorem blockEnd_le_one (i : ℕ) : L.blockEnd i ≤ 1 := by
  rw [← L.blockStart_succ]
  exact L.blockStart_le_one (i + 1)

theorem blockStart_lt_blockEnd_of_active (i : ℕ)
    (hi : blockIndexActive L.count i) : L.blockStart i < L.blockEnd i := by
  simp only [blockEnd]
  linarith [L.alpha_pos_of_active i hi]

/-- Paper endpoint `lambda_i` in zero-based indexing. -/
def endpoint (i : ℕ) : ℝ := L.blockEnd i

theorem endpoint_mem_Icc (i : ℕ) : L.endpoint i ∈ Icc (0 : ℝ) 1 :=
  ⟨L.blockEnd_nonneg i, L.blockEnd_le_one i⟩

@[simp] theorem endpoint_zero : L.endpoint 0 = L.alpha 0 := by
  simp [endpoint, blockEnd, blockStart]

/-- Consecutive paper endpoints differ by the next block length. -/
theorem endpoint_succ_sub (i : ℕ) :
    L.endpoint (i + 1) - L.endpoint i = L.alpha (i + 1) := by
  calc
    L.endpoint (i + 1) - L.endpoint i =
        (L.blockEnd i + L.alpha (i + 1)) - L.blockEnd i := by
      rw [endpoint, endpoint, blockEnd, L.blockStart_succ]
    _ = L.alpha (i + 1) := by ring

/-- Every index is active in the infinite-sequence case. -/
theorem active_of_count_eq_none (hcount : L.count = none) (i : ℕ) :
    blockIndexActive L.count i := by
  simp [blockIndexActive, hcount]

/-- In a finite sequence, precisely the indices below its length are active. -/
theorem active_iff_of_count_eq_some {n i : ℕ} (hcount : L.count = some n) :
    blockIndexActive L.count i ↔ i < n := by
  simp [blockIndexActive, hcount]

/-- All entries after the declared finite length vanish exactly. -/
theorem alpha_eq_zero_of_count_eq_some {n i : ℕ} (hcount : L.count = some n)
    (hi : n ≤ i) : L.alpha i = 0 := by
  apply L.alpha_eq_zero_of_inactive
  simpa [L.active_iff_of_count_eq_some hcount] using hi

theorem endpoint_strictMonoOn_active {i j : ℕ} (hij : i < j)
    (hj : blockIndexActive L.count j) : L.endpoint i < L.endpoint j := by
  calc
    L.endpoint i = L.blockStart (i + 1) := (L.blockStart_succ i).symm
    _ ≤ L.blockStart j := L.blockStart_mono (by omega)
    _ < L.blockEnd j := by
      simp only [blockEnd]
      linarith [L.alpha_pos_of_active j hj]
    _ = L.endpoint j := rfl

/-! ### The scalar mass of a block sequence -/

/-- The normalized quadratic mass contributed by block `i`. -/
def massTerm (i : ℕ) : ℝ :=
  L.alpha i ^ 2 / (L.core i).order

theorem massTerm_nonneg (i : ℕ) : 0 ≤ L.massTerm i := by
  exact div_nonneg (sq_nonneg _) (by positivity)

theorem massTerm_le_alpha (i : ℕ) : L.massTerm i ≤ L.alpha i := by
  have ha0 := L.alpha_nonneg i
  have ha1 := L.alpha_le_one i
  have hsquare : L.alpha i ^ 2 ≤ L.alpha i := by nlinarith [sq_nonneg (L.alpha i)]
  calc
    L.massTerm i ≤ L.alpha i ^ 2 := by
      exact div_le_self (sq_nonneg _) (by exact_mod_cast (L.core i).order_pos)
    _ ≤ L.alpha i := hsquare

/-- The unnormalized quadratic block-length series is summable. -/
theorem summable_alpha_sq : Summable (fun i ↦ L.alpha i ^ 2) := by
  apply Summable.of_nonneg_of_le (fun i ↦ sq_nonneg (L.alpha i)) _ L.summable_alpha
  intro i
  nlinarith [L.alpha_nonneg i, L.alpha_le_one i]

theorem summable_massTerm : Summable L.massTerm :=
  Summable.of_nonneg_of_le L.massTerm_nonneg L.massTerm_le_alpha L.summable_alpha

/-- The exact `tsum` appearing in the paper's block edge/entropy formulas. -/
def mass : ℝ := ∑' i, L.massTerm i

theorem mass_nonneg : 0 ≤ L.mass :=
  tsum_nonneg L.massTerm_nonneg

/-- Unit-interval version of a block's left endpoint. -/
def blockStartUI (i : ℕ) : UnitInterval :=
  ⟨L.blockStart i, L.blockStart_nonneg i, L.blockStart_le_one i⟩

/-- Unit-interval version of a block's right endpoint. -/
def blockEndUI (i : ℕ) : UnitInterval :=
  ⟨L.blockEnd i, L.blockEnd_nonneg i, L.blockEnd_le_one i⟩

/-- The half-open interval occupied by block `i`. -/
def blockInterval (i : ℕ) : Set UnitInterval :=
  Ico (L.blockStartUI i) (L.blockEndUI i)

@[measurability] theorem measurableSet_blockInterval (i : ℕ) :
    MeasurableSet (L.blockInterval i) :=
  measurableSet_Ico

theorem volume_blockInterval (i : ℕ) :
    volume (L.blockInterval i) = ENNReal.ofReal (L.alpha i) := by
  rw [blockInterval, unitInterval.volume_Ico]
  congr 1
  simp [blockStartUI, blockEndUI, blockEnd]

theorem pairwise_disjoint_blockInterval :
    Pairwise fun i j : ℕ ↦ Disjoint (L.blockInterval i) (L.blockInterval j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [Set.disjoint_left]
    intro x hxi hxj
    have hstart : L.blockEnd i ≤ L.blockStart j := by
      rw [← L.blockStart_succ]
      exact L.blockStart_mono (by omega)
    exact (not_lt_of_ge (hstart.trans hxj.1)) hxi.2
  · rw [Set.disjoint_left]
    intro x hxi hxj
    have hstart : L.blockEnd j ≤ L.blockStart i := by
      rw [← L.blockStart_succ]
      exact L.blockStart_mono (by omega)
    exact (not_lt_of_ge (hstart.trans hxi.1)) hxj.2

/-- The square supporting block `i`. -/
def blockSquare (i : ℕ) : Set UnitSquare :=
  L.blockInterval i ×ˢ L.blockInterval i

@[measurability] theorem measurableSet_blockSquare (i : ℕ) :
    MeasurableSet (L.blockSquare i) :=
  (L.measurableSet_blockInterval i).prod (L.measurableSet_blockInterval i)

theorem pairwise_disjoint_blockSquare :
    Pairwise fun i j : ℕ ↦ Disjoint (L.blockSquare i) (L.blockSquare j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  exact Set.disjoint_left.1 (L.pairwise_disjoint_blockInterval hij) hzi.1 hzj.1

/-! ### Equal subcells inside every block -/

/-- Left endpoint of vertex-cell `v` inside block `i`. -/
def cellLeft (i : ℕ) (v : Fin (L.core i).order) : ℝ :=
  L.blockStart i + L.alpha i * ((v : ℝ) / (L.core i).order)

/-- Right endpoint of vertex-cell `v` inside block `i`. -/
def cellRight (i : ℕ) (v : Fin (L.core i).order) : ℝ :=
  L.blockStart i + L.alpha i * (((v : ℕ) + 1 : ℝ) / (L.core i).order)

theorem cellLeft_mem_Icc (i : ℕ) (v : Fin (L.core i).order) :
    L.cellLeft i v ∈ Icc (0 : ℝ) 1 := by
  have ha := L.alpha_nonneg i
  have hratio0 : 0 ≤ (v : ℝ) / (L.core i).order := by positivity
  have hratio1 : (v : ℝ) / (L.core i).order ≤ 1 := by
    rw [div_le_one (by exact_mod_cast (L.core i).order_pos)]
    exact_mod_cast v.isLt.le
  constructor
  · exact add_nonneg (L.blockStart_nonneg i) (mul_nonneg ha hratio0)
  · calc
      L.cellLeft i v ≤ L.blockStart i + L.alpha i * 1 := by
        have hmul := mul_le_mul_of_nonneg_left hratio1 ha
        simp only [cellLeft]
        linarith
      _ = L.blockEnd i := by simp [blockEnd]
      _ ≤ 1 := L.blockEnd_le_one i

theorem cellRight_mem_Icc (i : ℕ) (v : Fin (L.core i).order) :
    L.cellRight i v ∈ Icc (0 : ℝ) 1 := by
  have ha := L.alpha_nonneg i
  have hratio0 : 0 ≤ (((v : ℕ) + 1 : ℝ) / (L.core i).order) := by positivity
  have hratio1 : (((v : ℕ) + 1 : ℝ) / (L.core i).order) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast (L.core i).order_pos)]
    exact_mod_cast v.isLt
  constructor
  · exact add_nonneg (L.blockStart_nonneg i) (mul_nonneg ha hratio0)
  · calc
      L.cellRight i v ≤ L.blockStart i + L.alpha i * 1 := by
        have hmul := mul_le_mul_of_nonneg_left hratio1 ha
        simp only [cellRight]
        linarith
      _ = L.blockEnd i := by simp [blockEnd]
      _ ≤ 1 := L.blockEnd_le_one i

def cellLeftUI (i : ℕ) (v : Fin (L.core i).order) : UnitInterval :=
  ⟨L.cellLeft i v, (L.cellLeft_mem_Icc i v).1, (L.cellLeft_mem_Icc i v).2⟩

def cellRightUI (i : ℕ) (v : Fin (L.core i).order) : UnitInterval :=
  ⟨L.cellRight i v, (L.cellRight_mem_Icc i v).1, (L.cellRight_mem_Icc i v).2⟩

/-- Vertex-cell `v` in block `i`. -/
def blockCell (i : ℕ) (v : Fin (L.core i).order) : Set UnitInterval :=
  Ico (L.cellLeftUI i v) (L.cellRightUI i v)

@[measurability] theorem measurableSet_blockCell (i : ℕ)
    (v : Fin (L.core i).order) : MeasurableSet (L.blockCell i v) :=
  measurableSet_Ico

theorem volume_blockCell (i : ℕ) (v : Fin (L.core i).order) :
    volume (L.blockCell i v) =
      ENNReal.ofReal (L.alpha i / (L.core i).order) := by
  rw [blockCell, unitInterval.volume_Ico]
  congr 1
  simp only [cellLeftUI, cellRightUI, cellLeft, cellRight]
  have hr : (((L.core i).order : ℝ)) ≠ 0 := by
    exact_mod_cast (L.core i).order_pos.ne'
  field_simp [hr]
  ring

/-- Product-volume of a pair of equal subcells inside block `i`. -/
theorem volume_blockCell_prod (i : ℕ) (v w : Fin (L.core i).order) :
    unitSquareMeasure (L.blockCell i v ×ˢ L.blockCell i w) =
      ENNReal.ofReal (L.alpha i / (L.core i).order) ^ 2 := by
  change ((volume : Measure UnitInterval).prod (volume : Measure UnitInterval))
      (L.blockCell i v ×ˢ L.blockCell i w) = _
  rw [Measure.prod_prod, L.volume_blockCell, L.volume_blockCell]
  rw [pow_two]

/-- Real-valued product-volume of a pair of equal subcells. -/
theorem measureReal_blockCell_prod (i : ℕ) (v w : Fin (L.core i).order) :
    unitSquareMeasure.real (L.blockCell i v ×ˢ L.blockCell i w) =
      (L.alpha i / (L.core i).order) ^ 2 := by
  rw [Measure.real, L.volume_blockCell_prod, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal]
  exact div_nonneg (L.alpha_nonneg i) (by positivity)

theorem blockCell_subset_interval (i : ℕ) (v : Fin (L.core i).order) :
    L.blockCell i v ⊆ L.blockInterval i := by
  intro x hx
  constructor
  · exact hx.1.trans' (by
      change L.blockStart i ≤ L.cellLeft i v
      exact le_add_of_nonneg_right (mul_nonneg (L.alpha_nonneg i) (by positivity)))
  · exact hx.2.trans_le (by
      change L.cellRight i v ≤ L.blockEnd i
      have hratio : (((v : ℕ) + 1 : ℝ) / (L.core i).order) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (L.core i).order_pos)]
        exact_mod_cast v.isLt
      simp only [cellRight, blockEnd]
      have hmul := mul_le_mul_of_nonneg_left hratio (L.alpha_nonneg i)
      linarith)

theorem blockCell_eq_of_mem {i j : ℕ} {v : Fin (L.core i).order}
    {w : Fin (L.core j).order} {x : UnitInterval}
    (hxv : x ∈ L.blockCell i v) (hxw : x ∈ L.blockCell j w) :
    i = j := by
  by_contra hij
  exact Set.disjoint_left.1 (L.pairwise_disjoint_blockInterval hij)
    (L.blockCell_subset_interval i v hxv) (L.blockCell_subset_interval j w hxw)

theorem blockCell_vertex_eq_of_mem {i : ℕ} {v w : Fin (L.core i).order}
    {x : UnitInterval} (hxv : x ∈ L.blockCell i v) (hxw : x ∈ L.blockCell i w) :
    v = w := by
  apply Fin.ext
  by_contra hvw
  rcases lt_or_gt_of_ne hvw with hvw | hwv
  · have hsep : L.cellRight i v ≤ L.cellLeft i w := by
      simp only [cellRight, cellLeft]
      have hratio : (((v : ℕ) + 1 : ℝ) / (L.core i).order) ≤
          (w : ℝ) / (L.core i).order := by
        rw [div_le_div_iff_of_pos_right (by exact_mod_cast (L.core i).order_pos)]
        exact_mod_cast (Nat.succ_le_iff.mpr hvw)
      have hmul := mul_le_mul_of_nonneg_left hratio (L.alpha_nonneg i)
      linarith
    exact (not_lt_of_ge hsep) (hxw.1.trans_lt hxv.2)
  · have hsep : L.cellRight i w ≤ L.cellLeft i v := by
      simp only [cellRight, cellLeft]
      have hratio : (((w : ℕ) + 1 : ℝ) / (L.core i).order) ≤
          (v : ℝ) / (L.core i).order := by
        rw [div_le_div_iff_of_pos_right (by exact_mod_cast (L.core i).order_pos)]
        exact_mod_cast (Nat.succ_le_iff.mpr hwv)
      have hmul := mul_le_mul_of_nonneg_left hratio (L.alpha_nonneg i)
      linarith
    exact (not_lt_of_ge hsep) (hxv.1.trans_lt hxw.2)

/-! ### The raw countable block kernel -/

/-- One rescaled copy of `xi_G`, supported on the square of block `i`. -/
def blockKernel (i : ℕ) (z : UnitSquare) : ℝ :=
  ∑ v : Fin (L.core i).order, ∑ w : Fin (L.core i).order,
    (L.blockCell i v ×ˢ L.blockCell i w).indicator
      (fun _ ↦ xiMatrix (L.core i) v w) z

@[fun_prop] theorem measurable_blockKernel (i : ℕ) : Measurable (L.blockKernel i) := by
  unfold blockKernel
  refine Finset.measurable_sum Finset.univ ?_
  intro v _
  refine Finset.measurable_sum Finset.univ ?_
  intro w _
  exact measurable_const.indicator
    ((L.measurableSet_blockCell i v).prod (L.measurableSet_blockCell i w))

theorem integrable_blockKernel (i : ℕ) :
    Integrable (L.blockKernel i) unitSquareMeasure := by
  unfold blockKernel
  apply integrable_finsetSum
  intro v _
  apply integrable_finsetSum
  intro w _
  exact (integrable_const _).indicator
    ((L.measurableSet_blockCell i v).prod (L.measurableSet_blockCell i w))

/-- Integral of one rescaled finite-core block before using regularity. -/
theorem integral_blockKernel (i : ℕ) :
    ∫ z : UnitSquare, L.blockKernel i z ∂unitSquareMeasure =
      (L.alpha i / (L.core i).order) ^ 2 *
        ∑ v : Fin (L.core i).order, ∑ w : Fin (L.core i).order,
          xiMatrix (L.core i) v w := by
  simpa only [blockKernel, L.measureReal_blockCell_prod, Finset.mul_sum] using
    integral_doubleSum_cellIndicators (L.blockCell i) (L.blockCell i)
      (L.measurableSet_blockCell i) (L.measurableSet_blockCell i)
      (xiMatrix (L.core i))

/-- Exact contribution of block `i` to edge density. -/
theorem integral_blockKernel_eq_massTerm_mul (i : ℕ) :
    ∫ z : UnitSquare, L.blockKernel i z ∂unitSquareMeasure =
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) * L.massTerm i := by
  rw [L.integral_blockKernel, sum_xiMatrix]
  unfold massTerm
  have horder : (((L.core i).order : ℝ)) ≠ 0 := by
    exact_mod_cast (L.core i).order_pos.ne'
  field_simp

theorem blockKernel_of_mem (i : ℕ) (v w : Fin (L.core i).order) (z : UnitSquare)
    (hzv : z.1 ∈ L.blockCell i v) (hzw : z.2 ∈ L.blockCell i w) :
    L.blockKernel i z = xiMatrix (L.core i) v w := by
  classical
  unfold blockKernel
  rw [Finset.sum_eq_single v]
  · rw [Finset.sum_eq_single w]
    · simp [hzv, hzw]
    · intro b _ hbw
      simp only [Set.indicator_apply]
      split_ifs with hb
      · exact (hbw (L.blockCell_vertex_eq_of_mem hb.2 hzw)).elim
      · rfl
    · simp
  · intro a _ hav
    apply Finset.sum_eq_zero
    intro b _
    simp only [Set.indicator_apply]
    split_ifs with hab
    · exact (hav (L.blockCell_vertex_eq_of_mem hab.1 hzv)).elim
    · rfl
  · simp

theorem blockKernel_eq_zero_of_not_mem (i : ℕ) (z : UnitSquare)
    (hz : z.1 ∉ L.blockInterval i ∨ z.2 ∉ L.blockInterval i) :
    L.blockKernel i z = 0 := by
  classical
  unfold blockKernel
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro w _
  apply Set.indicator_of_notMem
  intro h
  exact hz.elim
    (fun hnot ↦ hnot (L.blockCell_subset_interval i v h.1))
    (fun hnot ↦ hnot (L.blockCell_subset_interval i w h.2))

theorem blockKernel_eq_zero_of_no_leftCell (i : ℕ) (z : UnitSquare)
    (hz : ∀ v : Fin (L.core i).order, z.1 ∉ L.blockCell i v) :
    L.blockKernel i z = 0 := by
  classical
  unfold blockKernel
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro w _
  apply Set.indicator_of_notMem
  intro h
  exact hz v h.1

theorem blockKernel_eq_zero_of_no_rightCell (i : ℕ) (z : UnitSquare)
    (hz : ∀ w : Fin (L.core i).order, z.2 ∉ L.blockCell i w) :
    L.blockKernel i z = 0 := by
  classical
  unfold blockKernel
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro w _
  apply Set.indicator_of_notMem
  intro h
  exact hz w h.2

/-! The scalar-entropy analogue of a single block kernel. -/

/-- Finite cell sum obtained by applying binary entropy to the entries of one
core matrix. -/
def blockEntropyKernel (i : ℕ) (z : UnitSquare) : ℝ :=
  ∑ v : Fin (L.core i).order, ∑ w : Fin (L.core i).order,
    (L.blockCell i v ×ˢ L.blockCell i w).indicator
      (fun _ ↦ binaryEntropy (xiMatrix (L.core i) v w)) z

@[fun_prop] theorem measurable_blockEntropyKernel (i : ℕ) :
    Measurable (L.blockEntropyKernel i) := by
  unfold blockEntropyKernel
  refine Finset.measurable_sum Finset.univ ?_
  intro v _
  refine Finset.measurable_sum Finset.univ ?_
  intro w _
  exact measurable_const.indicator
    ((L.measurableSet_blockCell i v).prod (L.measurableSet_blockCell i w))

theorem integrable_blockEntropyKernel (i : ℕ) :
    Integrable (L.blockEntropyKernel i) unitSquareMeasure := by
  unfold blockEntropyKernel
  apply integrable_finsetSum
  intro v _
  apply integrable_finsetSum
  intro w _
  exact (integrable_const _).indicator
    ((L.measurableSet_blockCell i v).prod (L.measurableSet_blockCell i w))

theorem blockEntropyKernel_of_mem (i : ℕ) (v w : Fin (L.core i).order)
    (z : UnitSquare) (hzv : z.1 ∈ L.blockCell i v)
    (hzw : z.2 ∈ L.blockCell i w) :
    L.blockEntropyKernel i z = binaryEntropy (xiMatrix (L.core i) v w) := by
  classical
  unfold blockEntropyKernel
  rw [Finset.sum_eq_single v]
  · rw [Finset.sum_eq_single w]
    · simp [hzv, hzw]
    · intro b _ hbw
      simp only [Set.indicator_apply]
      split_ifs with hb
      · exact (hbw (L.blockCell_vertex_eq_of_mem hb.2 hzw)).elim
      · rfl
    · simp
  · intro a _ hav
    apply Finset.sum_eq_zero
    intro b _
    simp only [Set.indicator_apply]
    split_ifs with hab
    · exact (hav (L.blockCell_vertex_eq_of_mem hab.1 hzv)).elim
    · rfl
  · simp

theorem blockEntropyKernel_eq_zero_of_not_mem (i : ℕ) (z : UnitSquare)
    (hz : z.1 ∉ L.blockInterval i ∨ z.2 ∉ L.blockInterval i) :
    L.blockEntropyKernel i z = 0 := by
  classical
  unfold blockEntropyKernel
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro w _
  apply Set.indicator_of_notMem
  intro h
  exact hz.elim
    (fun hnot ↦ hnot (L.blockCell_subset_interval i v h.1))
    (fun hnot ↦ hnot (L.blockCell_subset_interval i w h.2))

/-- Applying binary entropy to a block kernel is exactly the corresponding
finite entropy-cell sum, including off-cell boundary points. -/
theorem binaryEntropy_blockKernel (i : ℕ) (z : UnitSquare) :
    binaryEntropy (L.blockKernel i z) = L.blockEntropyKernel i z := by
  classical
  by_cases hx : ∃ v : Fin (L.core i).order, z.1 ∈ L.blockCell i v
  · obtain ⟨v, hv⟩ := hx
    by_cases hy : ∃ w : Fin (L.core i).order, z.2 ∈ L.blockCell i w
    · obtain ⟨w, hw⟩ := hy
      rw [L.blockKernel_of_mem i v w z hv hw,
        L.blockEntropyKernel_of_mem i v w z hv hw]
    · have hzero : L.blockKernel i z = 0 := by
        unfold blockKernel
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro b _
        apply Set.indicator_of_notMem
        intro hab
        exact hy ⟨b, hab.2⟩
      have hEntropyZero : L.blockEntropyKernel i z = 0 := by
        unfold blockEntropyKernel
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro b _
        apply Set.indicator_of_notMem
        intro hab
        exact hy ⟨b, hab.2⟩
      simp [hzero, hEntropyZero]
  · have hzero : L.blockKernel i z = 0 := by
      unfold blockKernel
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      apply Set.indicator_of_notMem
      intro hab
      exact hx ⟨a, hab.1⟩
    have hEntropyZero : L.blockEntropyKernel i z = 0 := by
      unfold blockEntropyKernel
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      apply Set.indicator_of_notMem
      intro hab
      exact hx ⟨a, hab.1⟩
    simp [hzero, hEntropyZero]

/-- Integral of the entropy-cell sum for one block. -/
theorem integral_blockEntropyKernel (i : ℕ) :
    ∫ z : UnitSquare, L.blockEntropyKernel i z ∂unitSquareMeasure =
      (L.alpha i / (L.core i).order) ^ 2 *
        ∑ v : Fin (L.core i).order, ∑ w : Fin (L.core i).order,
          binaryEntropy (xiMatrix (L.core i) v w) := by
  simpa only [blockEntropyKernel, L.measureReal_blockCell_prod, Finset.mul_sum] using
    integral_doubleSum_cellIndicators (L.blockCell i) (L.blockCell i)
      (L.measurableSet_blockCell i) (L.measurableSet_blockCell i)
      (fun v w ↦ binaryEntropy (xiMatrix (L.core i) v w))

/-- Exact contribution of block `i` to graphon entropy. -/
theorem integral_blockEntropyKernel_eq_massTerm_mul (i : ℕ) :
    ∫ z : UnitSquare, L.blockEntropyKernel i z ∂unitSquareMeasure =
      (((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k)) * L.massTerm i := by
  rw [L.integral_blockEntropyKernel, sum_binaryEntropy_xiMatrix]
  unfold massTerm
  have horder : (((L.core i).order : ℝ)) ≠ 0 := by
    exact_mod_cast (L.core i).order_pos.ne'
  field_simp

theorem blockKernel_mem_Icc (hk : 3 ≤ k) (i : ℕ) (z : UnitSquare) :
    L.blockKernel i z ∈ Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : ∃ v : Fin (L.core i).order, z.1 ∈ L.blockCell i v
  · obtain ⟨v, hv⟩ := hx
    by_cases hy : ∃ w : Fin (L.core i).order, z.2 ∈ L.blockCell i w
    · obtain ⟨w, hw⟩ := hy
      rw [L.blockKernel_of_mem i v w z hv hw]
      exact ⟨xiMatrix_nonneg hk _ _ _, xiMatrix_le_one hk _ _ _⟩
    · have hz : z.2 ∉ L.blockInterval i ∨
          ∀ w : Fin (L.core i).order, z.2 ∉ L.blockCell i w := by
        exact Or.inr (by simpa only [not_exists] using hy)
      have hzero : L.blockKernel i z = 0 := by
        unfold blockKernel
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro b _
        apply Set.indicator_of_notMem
        intro hab
        exact hy ⟨b, hab.2⟩
      simp [hzero]
  · have hzero : L.blockKernel i z = 0 := by
      unfold blockKernel
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      apply Set.indicator_of_notMem
      intro hab
      exact hx ⟨a, hab.1⟩
    simp [hzero]

theorem blockKernel_symm (i : ℕ) (z : UnitSquare) :
    L.blockKernel i (z.2, z.1) = L.blockKernel i z := by
  classical
  simp only [blockKernel, Set.indicator_apply, Set.mem_prod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [(xiMatrix_isSymm (L.core i)).apply]
  simp [and_comm]

/-- Raw kernel of the countable disjoint union of all active blocks. -/
def kernel (z : UnitSquare) : ℝ :=
  ∑' i : ℕ, L.blockKernel i z

theorem blockKernel_eq_zero_of_ne {i j : ℕ} (hij : i ≠ j) (z : UnitSquare)
    (hi : z.1 ∈ L.blockInterval i) : L.blockKernel j z = 0 := by
  apply L.blockKernel_eq_zero_of_not_mem
  left
  intro hj
  exact Set.disjoint_left.1 (L.pairwise_disjoint_blockInterval hij) hi hj

theorem kernel_eq_blockKernel_of_mem (i : ℕ) (z : UnitSquare)
    (hi : z.1 ∈ L.blockInterval i) : L.kernel z = L.blockKernel i z := by
  classical
  rw [kernel, tsum_eq_single i]
  · intro j hji
    exact L.blockKernel_eq_zero_of_ne (i := i) (j := j) hji.symm z hi

theorem kernel_eq_zero_of_no_block (z : UnitSquare)
    (hz : ∀ i, z.1 ∉ L.blockInterval i) : L.kernel z = 0 := by
  simp [kernel, L.blockKernel_eq_zero_of_not_mem, hz]

/-- The countable kernel vanishes off the union of its block squares. -/
theorem kernel_eq_zero_of_not_mem_iUnion_blockSquare (z : UnitSquare)
    (hz : z ∉ ⋃ i, L.blockSquare i) : L.kernel z = 0 := by
  classical
  by_cases hx : ∃ i, z.1 ∈ L.blockInterval i
  · obtain ⟨i, hi⟩ := hx
    rw [L.kernel_eq_blockKernel_of_mem i z hi]
    apply L.blockKernel_eq_zero_of_not_mem
    right
    intro hy
    apply hz
    exact Set.mem_iUnion.2 ⟨i, hi, hy⟩
  · apply L.kernel_eq_zero_of_no_block
    simpa only [not_exists] using hx

theorem setIntegral_kernel_blockSquare (i : ℕ) :
    ∫ z in L.blockSquare i, L.kernel z ∂unitSquareMeasure =
      ∫ z in L.blockSquare i, L.blockKernel i z ∂unitSquareMeasure := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (L.measurableSet_blockSquare i)] with z hz
  exact L.kernel_eq_blockKernel_of_mem i z hz.1

theorem setIntegral_blockKernel_blockSquare (i : ℕ) :
    ∫ z in L.blockSquare i, L.blockKernel i z ∂unitSquareMeasure =
      ∫ z : UnitSquare, L.blockKernel i z ∂unitSquareMeasure := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  apply L.blockKernel_eq_zero_of_not_mem
  simpa [blockSquare] using not_and_or.mp hz

theorem kernel_mem_Icc (hk : 3 ≤ k) (z : UnitSquare) :
    L.kernel z ∈ Icc (0 : ℝ) 1 := by
  classical
  by_cases h : ∃ i, z.1 ∈ L.blockInterval i
  · obtain ⟨i, hi⟩ := h
    rw [L.kernel_eq_blockKernel_of_mem i z hi]
    exact L.blockKernel_mem_Icc hk i z
  · rw [L.kernel_eq_zero_of_no_block z (by simpa only [not_exists] using h)]
    exact ⟨le_rfl, zero_le_one⟩

@[fun_prop] theorem measurable_kernel : Measurable L.kernel := by
  unfold kernel
  fun_prop

theorem kernel_symm (z : UnitSquare) : L.kernel (z.2, z.1) = L.kernel z := by
  classical
  simp only [kernel, L.blockKernel_symm]

theorem kernel_eq_zero_of_no_leftCell (z : UnitSquare)
    (hz : ∀ i, ∀ v : Fin (L.core i).order, z.1 ∉ L.blockCell i v) :
    L.kernel z = 0 := by
  rw [kernel]
  have hzero : (fun i ↦ L.blockKernel i z) = fun _ ↦ 0 := by
    funext i
    exact L.blockKernel_eq_zero_of_no_leftCell i z (hz i)
  rw [hzero, tsum_zero]

/-! ### Raw induced-density factors -/

/-- Evaluate the raw countable kernel on an unordered coordinate pair. -/
def kernelPairValue {f : ℕ} (x : Fin f → UnitInterval) : Sym2 (Fin f) → ℝ :=
  Sym2.lift ⟨fun i j ↦ L.kernel (x i, x j), fun i j ↦ by
    simpa using (L.kernel_symm (x i, x j)).symm⟩

@[simp] theorem kernelPairValue_mk {f : ℕ} (x : Fin f → UnitInterval)
    (i j : Fin f) :
    L.kernelPairValue x s(i, j) = L.kernel (x i, x j) :=
  rfl

/-- The induced-density integrand formed from the raw countable kernel. -/
def kernelInducedIntegrand {f : ℕ} (F : SimpleGraph (Fin f))
    (x : Fin f → UnitInterval) : ℝ :=
  (∏ e ∈ finiteGraphEdges F, L.kernelPairValue x e) *
    ∏ e ∈ finiteGraphEdges Fᶜ, (1 - L.kernelPairValue x e)

theorem kernelInducedStarIntegrand_eq_zero_of_centerLeaf {k : ℕ}
    (x : Fin (k + 1) → UnitInterval) (a : Fin k)
    (hzero : L.kernel (x 0, x a.succ) = 0) :
    L.kernelInducedIntegrand (inducedStar k) x = 0 := by
  classical
  have hEdge : s(0, a.succ) ∈ finiteGraphEdges (inducedStar k) := by
    simpa using inducedStar_center_adj_leaf a
  unfold kernelInducedIntegrand
  rw [show (∏ e ∈ finiteGraphEdges (inducedStar k),
      L.kernelPairValue x e) = 0 by
    apply Finset.prod_eq_zero hEdge
    simpa using hzero]
  simp

/-- Pointwise induced-star obstruction for the raw countable block kernel. -/
theorem kernelInducedStarIntegrand_zero (hk : 3 ≤ k)
    (x : Fin (k + 1) → UnitInterval) :
    L.kernelInducedIntegrand (inducedStar k) x = 0 := by
  classical
  by_cases hcenter : ∃ i, ∃ v : Fin (L.core i).order,
      x 0 ∈ L.blockCell i v
  · obtain ⟨i, v, hv⟩ := hcenter
    by_cases hall : ∀ a : Fin k, ∃ w : Fin (L.core i).order,
        x a.succ ∈ L.blockCell i w
    · choose w hw using hall
      let φ : Fin (k + 1) → Fin (L.core i).order := Fin.cases v w
      have hcell (a : Fin (k + 1)) : x a ∈ L.blockCell i (φ a) := by
        refine Fin.cases ?_ (fun b ↦ ?_) a
        · simpa [φ] using hv
        · simpa [φ] using hw b
      have hpair (a b : Fin (k + 1)) :
          L.kernel (x a, x b) = xiMatrix (L.core i) (φ a) (φ b) := by
        rw [L.kernel_eq_blockKernel_of_mem i (x a, x b)
          (L.blockCell_subset_interval i (φ a) (hcell a))]
        exact L.blockKernel_of_mem i (φ a) (φ b) (x a, x b)
          (hcell a) (hcell b)
      calc
        L.kernelInducedIntegrand (inducedStar k) x =
            matrixInducedMapWeight (inducedStar k) (xiMatrix (L.core i))
              (xiMatrix_isSymm (L.core i)) φ := by
          unfold kernelInducedIntegrand matrixInducedMapWeight
          congr 1
          · apply Finset.prod_congr rfl
            intro e _
            induction e using Sym2.inductionOn with
            | _ a b => simpa using hpair a b
          · apply Finset.prod_congr rfl
            intro e _
            induction e using Sym2.inductionOn with
            | _ a b => rw [L.kernelPairValue_mk, matrixMapPairValue_mk,
                hpair a b]
        _ = 0 := xiMatrix_inducedStar_weight_zero hk (L.core i) φ
    · push Not at hall
      obtain ⟨a, ha⟩ := hall
      apply L.kernelInducedStarIntegrand_eq_zero_of_centerLeaf x a
      rw [L.kernel_eq_blockKernel_of_mem i (x 0, x a.succ)
        (L.blockCell_subset_interval i v hv)]
      exact L.blockKernel_eq_zero_of_no_rightCell i (x 0, x a.succ) ha
  · let a : Fin k := ⟨0, by omega⟩
    apply L.kernelInducedStarIntegrand_eq_zero_of_centerLeaf x a
    apply L.kernel_eq_zero_of_no_leftCell
    intro i v hiv
    exact hcenter ⟨i, v, hiv⟩

theorem integrable_kernel (hk : 3 ≤ k) : Integrable L.kernel unitSquareMeasure := by
  apply Integrable.of_bound L.measurable_kernel.aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (L.kernel_mem_Icc hk z).1]
  exact (L.kernel_mem_Icc hk z).2

/-- Exact integral of the raw countable kernel. -/
theorem integral_kernel (hk : 3 ≤ k) :
    ∫ z : UnitSquare, L.kernel z ∂unitSquareMeasure =
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) * L.mass := by
  calc
    ∫ z : UnitSquare, L.kernel z ∂unitSquareMeasure =
        ∫ z in ⋃ i, L.blockSquare i, L.kernel z ∂unitSquareMeasure := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      exact L.kernel_eq_zero_of_not_mem_iUnion_blockSquare
    _ = ∑' i, ∫ z in L.blockSquare i, L.kernel z ∂unitSquareMeasure := by
      apply integral_iUnion
      · exact L.measurableSet_blockSquare
      · exact L.pairwise_disjoint_blockSquare
      · exact (L.integrable_kernel hk).integrableOn
    _ = ∑' i, ∫ z : UnitSquare, L.blockKernel i z ∂unitSquareMeasure := by
      apply tsum_congr
      intro i
      rw [L.setIntegral_kernel_blockSquare,
        L.setIntegral_blockKernel_blockSquare]
    _ = (1 + ((k - 2 : ℕ) : ℝ) * pK k) * L.mass := by
      simp_rw [L.integral_blockKernel_eq_massTerm_mul]
      exact L.summable_massTerm.tsum_mul_left _

theorem integrable_binaryEntropy_kernel (hk : 3 ≤ k) :
    Integrable (fun z : UnitSquare ↦ binaryEntropy (L.kernel z))
      unitSquareMeasure := by
  apply Integrable.of_bound
    (binaryEntropy_continuous.measurable.comp
      L.measurable_kernel).aestronglyMeasurable 1
  filter_upwards [] with z
  change |binaryEntropy (L.kernel z)| ≤ 1
  rw [abs_of_nonneg
    (binaryEntropy_nonneg (L.kernel_mem_Icc hk z).1 (L.kernel_mem_Icc hk z).2)]
  exact binaryEntropy_le_one _

theorem setIntegral_binaryEntropy_kernel_blockSquare (i : ℕ) :
    ∫ z in L.blockSquare i, binaryEntropy (L.kernel z) ∂unitSquareMeasure =
      ∫ z in L.blockSquare i, L.blockEntropyKernel i z ∂unitSquareMeasure := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (L.measurableSet_blockSquare i)] with z hz
  rw [L.kernel_eq_blockKernel_of_mem i z hz.1,
    L.binaryEntropy_blockKernel]

theorem setIntegral_blockEntropyKernel_blockSquare (i : ℕ) :
    ∫ z in L.blockSquare i, L.blockEntropyKernel i z ∂unitSquareMeasure =
      ∫ z : UnitSquare, L.blockEntropyKernel i z ∂unitSquareMeasure := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  apply L.blockEntropyKernel_eq_zero_of_not_mem
  simpa [blockSquare] using not_and_or.mp hz

/-- Exact integral of binary entropy applied to the raw countable kernel. -/
theorem integral_binaryEntropy_kernel (hk : 3 ≤ k) :
    ∫ z : UnitSquare, binaryEntropy (L.kernel z) ∂unitSquareMeasure =
      (((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k)) * L.mass := by
  calc
    ∫ z : UnitSquare, binaryEntropy (L.kernel z) ∂unitSquareMeasure =
        ∫ z in ⋃ i, L.blockSquare i,
          binaryEntropy (L.kernel z) ∂unitSquareMeasure := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [L.kernel_eq_zero_of_not_mem_iUnion_blockSquare z hz]
      simp
    _ = ∑' i, ∫ z in L.blockSquare i,
        binaryEntropy (L.kernel z) ∂unitSquareMeasure := by
      apply integral_iUnion
      · exact L.measurableSet_blockSquare
      · exact L.pairwise_disjoint_blockSquare
      · exact (L.integrable_binaryEntropy_kernel hk).integrableOn
    _ = ∑' i, ∫ z : UnitSquare,
        L.blockEntropyKernel i z ∂unitSquareMeasure := by
      apply tsum_congr
      intro i
      rw [L.setIntegral_binaryEntropy_kernel_blockSquare,
        L.setIntegral_blockEntropyKernel_blockSquare]
    _ = (((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k)) * L.mass := by
      simp_rw [L.integral_blockEntropyKernel_eq_massTerm_mul]
      exact L.summable_massTerm.tsum_mul_left _

/-- The genuine measurable graphon associated with a finite or infinite
admissible block sequence. -/
def graphon (hk : 3 ≤ k) : Graphon :=
  Graphon.ofFun L.kernel (L.integrable_kernel hk)
    (ae_of_all _ fun z ↦ (L.kernel_mem_Icc hk z).1)
    (ae_of_all _ fun z ↦ (L.kernel_mem_Icc hk z).2)
    L.kernel_symm

theorem graphon_ae_eq_kernel (hk : 3 ≤ k) :
    ∀ᵐ z ∂unitSquareMeasure, L.graphon hk z = L.kernel z :=
  Graphon.coe_ofFun _ _ _ _ _

/-- Every distinct-coordinate pair factor of the canonical graphon
representative agrees almost everywhere with the raw countable kernel. -/
theorem graphonPairValue_ae_eq_kernelPairValue {f : ℕ} (hk : 3 ≤ k)
    {i j : Fin f} (hij : i ≠ j) :
    (fun x : Fin f → UnitInterval ↦
      graphonPairValue (L.graphon hk) x s(i, j)) =ᵐ[volume]
        fun x ↦ L.kernelPairValue x s(i, j) := by
  have h₁ := graphonPairValue_ae_eq_of_ne (L.graphon hk) hij
  have h₂ := (measurePreserving_pairProjection hij).quasiMeasurePreserving.ae_eq_comp
    (L.graphon_ae_eq_kernel hk)
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  exact hx₁.trans (by simpa using hx₂)

/-- The canonical graphon induced-density integrand agrees almost everywhere
with the raw-kernel induced-density integrand. -/
theorem graphonInducedIntegrand_ae_eq_kernelInducedIntegrand {f : ℕ}
    (hk : 3 ≤ k) (F : SimpleGraph (Fin f)) :
    graphonInducedIntegrand F (L.graphon hk) =ᵐ[volume]
      L.kernelInducedIntegrand F := by
  classical
  have hedge (e : Sym2 (Fin f)) : e ∈ finiteGraphEdges F →
      ∀ᵐ x : Fin f → UnitInterval ∂volume,
        graphonPairValue (L.graphon hk) x e = L.kernelPairValue x e := by
    refine Sym2.inductionOn e ?_
    intro i j he
    have hF : F.Adj i j := by simpa using he
    exact L.graphonPairValue_ae_eq_kernelPairValue hk (F.ne_of_adj hF)
  have hnonedge (e : Sym2 (Fin f)) : e ∈ finiteGraphEdges Fᶜ →
      ∀ᵐ x : Fin f → UnitInterval ∂volume,
        graphonPairValue (L.graphon hk) x e = L.kernelPairValue x e := by
    refine Sym2.inductionOn e ?_
    intro i j he
    have hFc : Fᶜ.Adj i j := by simpa using he
    exact L.graphonPairValue_ae_eq_kernelPairValue hk (Fᶜ.ne_of_adj hFc)
  have hallEdges := (Filter.eventually_all_finset (finiteGraphEdges F)).2
    fun e he ↦ hedge e he
  have hallNonedges := (Filter.eventually_all_finset (finiteGraphEdges Fᶜ)).2
    fun e he ↦ hnonedge e he
  filter_upwards [hallEdges, hallNonedges] with x hxEdge hxNonedge
  unfold graphonInducedIntegrand kernelInducedIntegrand
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    exact hxEdge e he
  · apply Finset.prod_congr rfl
    intro e he
    rw [hxNonedge e he]

/-- The countable block graphon is induced-`K_{1,k}`-free. -/
theorem graphon_inducedStar_free (hk : 3 ≤ k) :
    graphonInducedDensity (inducedStar k) (L.graphon hk) = 0 := by
  unfold graphonInducedDensity
  calc
    ∫ x : Fin (k + 1) → UnitInterval,
        graphonInducedIntegrand (inducedStar k) (L.graphon hk) x =
        ∫ x : Fin (k + 1) → UnitInterval,
          L.kernelInducedIntegrand (inducedStar k) x := by
      exact integral_congr_ae
        (L.graphonInducedIntegrand_ae_eq_kernelInducedIntegrand hk (inducedStar k))
    _ = 0 := by
      apply integral_eq_zero_of_ae
      exact ae_of_all _ (L.kernelInducedStarIntegrand_zero hk)

/-- Edge density of the countable block graphon, in terms of its exact
normalized quadratic mass. -/
theorem graphon_edgeDensity (hk : 3 ≤ k) :
    graphonEdgeDensity (L.graphon hk) =
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) * L.mass := by
  rw [graphonEdgeDensity_eq_integral]
  calc
    ∫ z : UnitSquare, L.graphon hk z ∂unitSquareMeasure =
        ∫ z : UnitSquare, L.kernel z ∂unitSquareMeasure := by
      exact integral_congr_ae (L.graphon_ae_eq_kernel hk)
    _ = _ := L.integral_kernel hk

/-- Entropy of the countable block graphon, in terms of its exact normalized
quadratic mass. -/
theorem graphon_entropy (hk : 3 ≤ k) :
    graphonEntropy (L.graphon hk) =
      (((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k)) * L.mass := by
  unfold graphonEntropy graphonValueFunctional
  calc
    ∫ z : UnitSquare, binaryEntropy ((L.graphon hk).value z)
        ∂unitSquareMeasure =
        ∫ z : UnitSquare, binaryEntropy (L.kernel z) ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [(L.graphon hk).value_ae_eq,
        L.graphon_ae_eq_kernel hk] with z hzValue hzKernel
      rw [hzValue, hzKernel]
    _ = _ := L.integral_binaryEntropy_kernel hk

end AdmissibleBlockSequence

/-- Paper-facing name for the block-sequence graphon `W_Lambda`. -/
def WLambda {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k) : Graphon :=
  L.graphon hk

/-- Exact edge-density formula for the paper's finite or infinite block
candidate `W_Λ`. -/
theorem WLambda_edgeDensity {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    graphonEdgeDensity (WLambda hk L) =
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) *
        ∑' i, L.alpha i ^ 2 / (L.core i).order := by
  rw [WLambda, L.graphon_edgeDensity]
  rfl

/-- Compatibility spelling emphasizing the functional being evaluated. -/
theorem graphonEdgeDensity_WLambda {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    graphonEdgeDensity (WLambda hk L) =
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) *
        ∑' i, L.alpha i ^ 2 / (L.core i).order :=
  WLambda_edgeDensity hk L

/-- Exact entropy formula for the paper's finite or infinite block candidate
`W_Λ`. -/
theorem WLambda_entropy {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    graphonEntropy (WLambda hk L) =
      (((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k)) *
        ∑' i, L.alpha i ^ 2 / (L.core i).order := by
  rw [WLambda, L.graphon_entropy]
  rfl

/-- Compatibility spelling emphasizing the functional being evaluated. -/
theorem graphonEntropy_WLambda {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    graphonEntropy (WLambda hk L) =
      (((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k)) *
        ∑' i, L.alpha i ^ 2 / (L.core i).order :=
  WLambda_entropy hk L

/-- Every paper candidate `W_Λ` is induced-`K_{1,k}`-free. -/
theorem WLambda_inducedStar_free {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    graphonInducedDensity (inducedStar k) (WLambda hk L) = 0 := by
  exact L.graphon_inducedStar_free hk

/-- Compatibility spelling emphasizing the functional being evaluated. -/
theorem graphonInducedDensity_WLambda {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    graphonInducedDensity (inducedStar k) (WLambda hk L) = 0 :=
  WLambda_inducedStar_free hk L

end InducedStars
