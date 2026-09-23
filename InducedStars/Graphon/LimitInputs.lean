import InducedStars.Graphon.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Sequences

/-!
# Finite-dimensional limit inputs for graphons

This file contains only elementary, local infrastructure used by the later
graphon diagonal construction.  In particular, it formalizes the exact
zero-based block-average compatibility condition on nested density matrices
and the compactness/subsequence facts needed to extract their limits.  No
graph-limit theorem is assumed here.
-/

namespace InducedStars

open Filter Set
open scoped BigOperators Topology

namespace Graphon

/-! ## Consecutive refinement blocks -/

/-- The zero-based index in the `i`-th consecutive block of a refinement.

If `k ∣ K`, then each coarse index `i : Fin k` corresponds to the consecutive
fine indices `i * (K / k), ..., (i + 1) * (K / k) - 1`. -/
def refinementIndex {k K : ℕ} (h : k ∣ K) (i : Fin k) (a : Fin (K / k)) : Fin K :=
  ⟨i.1 * (K / k) + a.1, by
    calc
      i.1 * (K / k) + a.1 < i.1 * (K / k) + K / k :=
        Nat.add_lt_add_left a.2 _
      _ = (i.1 + 1) * (K / k) := by simp [Nat.add_mul]
      _ ≤ k * (K / k) := Nat.mul_le_mul_right _ (Nat.succ_le_iff.2 i.2)
      _ = K := Nat.mul_div_cancel' h⟩

@[simp] lemma refinementIndex_val {k K : ℕ} (h : k ∣ K) (i : Fin k)
    (a : Fin (K / k)) :
    (refinementIndex h i a).1 = i.1 * (K / k) + a.1 :=
  rfl

@[simp] lemma refinementIndex_refl {k : ℕ} (hk : 0 < k) (i : Fin k)
    (a : Fin (k / k)) :
    refinementIndex (dvd_refl k) i a = i := by
  have ha_lt : a.1 < 1 := by
    simpa [Nat.div_self hk] using a.2
  have ha : a.1 = 0 := by omega
  apply Fin.ext
  simp [refinementIndex, Nat.div_self hk, ha]

/-- Arithmetic mean of the consecutive fine block belonging to `(i,j)`. -/
noncomputable def matrixBlockAverage {k K : ℕ} (h : k ∣ K)
    (M : Matrix (Fin K) (Fin K) ℝ) (i j : Fin k) : ℝ :=
  (∑ a : Fin (K / k), ∑ b : Fin (K / k),
      M (refinementIndex h i a) (refinementIndex h j b)) / ((K / k : ℕ) : ℝ) ^ 2

lemma matrixBlockAverage_transpose {k K : ℕ} (h : k ∣ K)
    (M : Matrix (Fin K) (Fin K) ℝ) (i j : Fin k) :
    matrixBlockAverage h M.transpose i j = matrixBlockAverage h M j i := by
  simp only [matrixBlockAverage, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Block averaging along the identity refinement returns the original entry. -/
@[simp] lemma matrixBlockAverage_refl {k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin k) (Fin k) ℝ) (i j : Fin k) :
    matrixBlockAverage (dvd_refl k) M i j = M i j := by
  simp [matrixBlockAverage, refinementIndex_refl hk, Nat.div_self hk]

lemma matrixBlockAverage_symm {k K : ℕ} (h : k ∣ K)
    {M : Matrix (Fin K) (Fin K) ℝ} (hM : M.IsSymm) :
    Matrix.IsSymm (Matrix.of fun i j : Fin k ↦ matrixBlockAverage h M i j) := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  change matrixBlockAverage h M j i = matrixBlockAverage h M i j
  rw [← matrixBlockAverage_transpose]
  rw [hM.eq]

/-! ## Nested density matrices -/

/-- A zero-based tower of symmetric `[0,1]`-valued density matrices whose
coarser entries are exact arithmetic means of consecutive fine blocks.

The compatibility field is stated for every `m ≤ n`.  This is precisely the
nested-matrix input used by Lovász--Szegedy Lemmas 5.1--5.2 and avoids hiding
any transitive closure in the representation. -/
structure NestedDensityMatrices where
  size : ℕ → ℕ
  size_pos : ∀ n, 0 < size n
  matrix : (n : ℕ) → Matrix (Fin (size n)) (Fin (size n)) ℝ
  matrix_symmetric : ∀ n, (matrix n).IsSymm
  matrix_mem_Icc : ∀ n i j, matrix n i j ∈ Icc (0 : ℝ) 1
  dvd_of_le : ∀ {m n}, m ≤ n → size m ∣ size n
  blockAverage : ∀ {m n} (h : m ≤ n) (i : Fin (size m)) (j : Fin (size m)),
    matrix m i j = matrixBlockAverage (dvd_of_le h) (matrix n) i j

namespace NestedDensityMatrices

variable (Q : NestedDensityMatrices)

lemma size_ne_zero (n : ℕ) : Q.size n ≠ 0 :=
  (Q.size_pos n).ne'

lemma size_dvd {m n : ℕ} (h : m ≤ n) : Q.size m ∣ Q.size n :=
  Q.dvd_of_le h

lemma size_mono {m n : ℕ} (h : m ≤ n) : Q.size m ≤ Q.size n :=
  Nat.le_of_dvd (Q.size_pos n) (Q.dvd_of_le h)

lemma refinementRatio_pos {m n : ℕ} (h : m ≤ n) :
    0 < Q.size n / Q.size m :=
  Nat.div_pos (Q.size_mono h) (Q.size_pos m)

lemma size_mul_refinementRatio {m n : ℕ} (h : m ≤ n) :
    Q.size m * (Q.size n / Q.size m) = Q.size n :=
  Nat.mul_div_cancel' (Q.dvd_of_le h)

lemma matrix_nonneg (n : ℕ) (i j : Fin (Q.size n)) :
    0 ≤ Q.matrix n i j :=
  (Q.matrix_mem_Icc n i j).1

lemma matrix_le_one (n : ℕ) (i j : Fin (Q.size n)) :
    Q.matrix n i j ≤ 1 :=
  (Q.matrix_mem_Icc n i j).2

lemma matrix_swap (n : ℕ) (i j : Fin (Q.size n)) :
    Q.matrix n j i = Q.matrix n i j :=
  (Q.matrix_symmetric n).apply i j

/-- The structure's all-level compatibility, exposed with a descriptive name. -/
lemma compatible_of_le {m n : ℕ} (h : m ≤ n)
    (i j : Fin (Q.size m)) :
    Q.matrix m i j =
      matrixBlockAverage (Q.dvd_of_le h) (Q.matrix n) i j :=
  Q.blockAverage h i j

/-- Successive levels satisfy the exact consecutive-block average identity. -/
lemma compatible_succ (n : ℕ) (i j : Fin (Q.size n)) :
    Q.matrix n i j =
      matrixBlockAverage (Q.dvd_of_le (Nat.le_succ n)) (Q.matrix (n + 1)) i j :=
  Q.blockAverage (Nat.le_succ n) i j

/-- At a single level, the compatibility field reduces to reflexivity. -/
lemma compatible_refl (n : ℕ) (i j : Fin (Q.size n)) :
    matrixBlockAverage (Q.dvd_of_le (le_refl n)) (Q.matrix n) i j =
      Q.matrix n i j := by
  simpa using matrixBlockAverage_refl (Q.size_pos n) (Q.matrix n) i j

end NestedDensityMatrices

/-! ## Compactness of fixed-size density matrices -/

/-- Every sequence of fixed-size `[0,1]`-valued matrices has a convergent
subsequence in the finite product topology. -/
theorem unitIntervalMatrix_tendsto_subsequence (q : ℕ)
    (M : ℕ → Matrix (Fin q) (Fin q) unitInterval) :
    ∃ L : Matrix (Fin q) (Fin q) unitInterval,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (M ∘ φ) atTop (𝓝 L) := by
  let _ : FirstCountableTopology (Matrix (Fin q) (Fin q) unitInterval) :=
    inferInstanceAs (FirstCountableTopology (Fin q → Fin q → unitInterval))
  let _ : CompactSpace (Matrix (Fin q) (Fin q) unitInterval) :=
    inferInstanceAs (CompactSpace (Fin q → Fin q → unitInterval))
  simpa using CompactSpace.tendsto_subseq M

/-- Real-matrix form of fixed-dimensional entrywise compactness. -/
theorem matrix_mem_Icc_tendsto_subsequence (q : ℕ)
    (M : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hM : ∀ n i j, M n i j ∈ Icc (0 : ℝ) 1) :
    ∃ L : Matrix (Fin q) (Fin q) ℝ,
      (∀ i j, L i j ∈ Icc (0 : ℝ) 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ i j, Tendsto (fun n ↦ M (φ n) i j) atTop (𝓝 (L i j)) := by
  let M' : ℕ → Matrix (Fin q) (Fin q) unitInterval :=
    fun n i j ↦ ⟨M n i j, hM n i j⟩
  obtain ⟨L', φ, hφ, hlim⟩ := unitIntervalMatrix_tendsto_subsequence q M'
  let L : Matrix (Fin q) (Fin q) ℝ := fun i j ↦ L' i j
  refine ⟨L, ?_, φ, hφ, ?_⟩
  · intro i j
    exact (L' i j).2
  · intro i j
    have hij : Tendsto (fun n ↦ (M' (φ n) i j : unitInterval)) atTop (𝓝 (L' i j)) :=
      tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim i) j
    exact (continuous_subtype_val.tendsto (L' i j)).comp hij

/-- Symmetry is retained by the entrywise limit extracted from symmetric
`[0,1]`-valued matrices. -/
theorem symmetricMatrix_mem_Icc_tendsto_subsequence (q : ℕ)
    (M : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hM : ∀ n i j, M n i j ∈ Icc (0 : ℝ) 1)
    (hM_symm : ∀ n, (M n).IsSymm) :
    ∃ L : Matrix (Fin q) (Fin q) ℝ,
      L.IsSymm ∧ (∀ i j, L i j ∈ Icc (0 : ℝ) 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ i j, Tendsto (fun n ↦ M (φ n) i j) atTop (𝓝 (L i j)) := by
  obtain ⟨L, hL, φ, hφ, hlim⟩ := matrix_mem_Icc_tendsto_subsequence q M hM
  refine ⟨L, ?_, hL, φ, hφ, hlim⟩
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  apply tendsto_nhds_unique (hlim j i)
  exact Tendsto.congr'
    (Eventually.of_forall fun n ↦ ((hM_symm (φ n)).apply i j).symm) (hlim i j)

/-! ## Subsequence primitives -/

/-- Composition of strictly monotone extraction maps is an extraction map. -/
lemma strictMono_extraction_comp {φ ψ : ℕ → ℕ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ) :
    StrictMono (φ ∘ ψ) :=
  hφ.comp hψ

/-- A convergent sequence has the same limit along every subsequence. -/
lemma tendsto_subsequence {α : Type*} [TopologicalSpace α]
    {u : ℕ → α} {a : α} (hu : Tendsto u atTop (𝓝 a))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hu.comp hφ.tendsto_atTop

/-- Infinitely many values in a finite type yield an exactly constant
subsequence. -/
theorem finite_constant_subsequence {α : Type*} [Finite α] (u : ℕ → α) :
    ∃ a : α, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) = a := by
  obtain ⟨a, ha⟩ := Finite.exists_infinite_fiber u
  have ha' : (u ⁻¹' {a}).Infinite := Set.infinite_coe_iff.1 ha
  have hcofinal : ∀ N : ℕ, ∃ n > N, u n = a := by
    intro N
    obtain ⟨n, hn, hNn⟩ := Set.Infinite.exists_gt ha' N
    change u n = a at hn
    exact ⟨n, hNn, hn⟩
  obtain ⟨φ, hφ, hu⟩ := Nat.exists_strictMono_subsequence hcofinal
  exact ⟨a, φ, hφ, hu⟩

/-- A sequence of positive integers bounded by a fixed `U` is constant along
an infinite subsequence. -/
theorem boundedNat_constant_subsequence (U : ℕ) (u : ℕ → ℕ)
    (hu_pos : ∀ n, 1 ≤ u n) (hu_le : ∀ n, u n ≤ U) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ U ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) = r := by
  let u' : ℕ → Fin (U + 1) := fun n ↦ ⟨u n, Nat.lt_succ_of_le (hu_le n)⟩
  obtain ⟨r, φ, hφ, hr⟩ := finite_constant_subsequence u'
  refine ⟨r.1, ?_, Nat.le_of_lt_succ r.2, φ, hφ, ?_⟩
  · have h := congrArg Fin.val (hr 0)
    simpa [u'] using h ▸ hu_pos (φ 0)
  · intro n
    exact congrArg Fin.val (hr n)

/-- Simultaneous constant extraction for a finite family of finite-valued
sequences. -/
theorem finiteFamily_constant_subsequence {ι α : Type*} [Finite ι] [Finite α]
    (u : ι → ℕ → α) :
    ∃ a : ι → α, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i n, u i (φ n) = a i := by
  obtain ⟨a, φ, hφ, ha⟩ :=
    finite_constant_subsequence (fun n i ↦ u i n)
  exact ⟨a, φ, hφ, fun i n ↦ congrFun (ha n) i⟩

/-! ## Diagonal extraction from nested subsequences -/

/-- A tower of extraction maps in which every next row is itself a
subsequence of the preceding row. -/
structure SubsequenceTower where
  extraction : ℕ → ℕ → ℕ
  strictMono : ∀ n, StrictMono (extraction n)
  next_refines : ∀ n, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    extraction (n + 1) = extraction n ∘ φ

namespace SubsequenceTower

variable (T : SubsequenceTower)

/-- Every later row in a subsequence tower refines every earlier row. -/
lemma refines_of_le {m n : ℕ} (h : m ≤ n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      T.extraction n = T.extraction m ∘ φ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero =>
      exact ⟨id, strictMono_id, by simp⟩
  | succ d ih =>
      obtain ⟨φ, hφ, hφeq⟩ := ih
      obtain ⟨ψ, hψ, hψeq⟩ := T.next_refines (m + d)
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      rw [Nat.add_succ, hψeq, hφeq]
      rfl

/-- The standard diagonal choice from a tower of nested subsequences. -/
def diagonal (n : ℕ) : ℕ :=
  T.extraction n n

/-- The diagonal choice is itself a subsequence. -/
lemma diagonal_strictMono : StrictMono T.diagonal := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨φ, hφ, hφeq⟩ := T.next_refines n
  rw [diagonal, diagonal, hφeq]
  exact T.strictMono n (lt_of_lt_of_le n.lt_succ_self (hφ.id_le (n + 1)))

/-- A property holding throughout one row of a nested tower holds eventually
along the diagonal. -/
lemma eventually_diagonal_of_row {P : ℕ → Prop} {m : ℕ}
    (hP : ∀ k, P (T.extraction m k)) :
    ∀ᶠ n in atTop, P (T.diagonal n) := by
  filter_upwards [eventually_ge_atTop m] with n hn
  obtain ⟨φ, -, hφeq⟩ := T.refines_of_le hn
  simpa [diagonal, hφeq, Function.comp_def] using hP (φ n)

end SubsequenceTower

end Graphon

end InducedStars
