import InducedStars.Graphon.StepEstimates
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Elementary infrastructure for type towers

This file contains the assumption-free arithmetic, compactness bookkeeping,
and growth facts used by the type-graphon sequence construction.  It is
deliberately independent of the clean-partition construction.
-/

noncomputable section

namespace InducedStars

open Filter Set
open scoped BigOperators Topology

namespace Graphon

/-! ## Composition of consecutive refinement blocks -/

/-- The canonical identification of two successive refinement coordinates
with the single coordinate in the composite refinement. -/
def refinementQuotientEquiv {k K L : ℕ} (hkK : k ∣ K) (hKL : K ∣ L) :
    Fin (K / k) × Fin (L / K) ≃ Fin (L / k) :=
  finProdFinEquiv.trans <| finCongr <| by
    simpa only [Nat.mul_comm] using Nat.div_mul_div hKL hkK

@[simp]
theorem refinementQuotientEquiv_val {k K L : ℕ} (hkK : k ∣ K) (hKL : K ∣ L)
    (a : Fin (K / k)) (b : Fin (L / K)) :
    ((refinementQuotientEquiv hkK hKL (a, b) : Fin (L / k)) : ℕ) =
      (b : ℕ) + (L / K) * (a : ℕ) := by
  simp [refinementQuotientEquiv, finProdFinEquiv]

/-- Refinement indices compose according to the canonical product
enumeration of their two within-block coordinates. -/
theorem refinementIndex_comp {k K L : ℕ} (hkK : k ∣ K) (hKL : K ∣ L)
    (i : Fin k) (a : Fin (K / k)) (b : Fin (L / K)) :
    refinementIndex hKL (refinementIndex hkK i a) b =
      refinementIndex (hkK.trans hKL) i (refinementQuotientEquiv hkK hKL (a, b)) := by
  apply Fin.ext
  simp only [refinementIndex_val, refinementQuotientEquiv_val]
  have hratio : (K / k) * (L / K) = L / k := by
    simpa only [Nat.mul_comm] using Nat.div_mul_div hKL hkK
  rw [← hratio]
  ring

/-- Taking the arithmetic mean over two successive consecutive refinements is
the same as taking the arithmetic mean over the composite refinement. -/
theorem matrixBlockAverage_trans {k K L : ℕ} (hL : 0 < L)
    (hkK : k ∣ K) (hKL : K ∣ L)
    (M : Matrix (Fin L) (Fin L) ℝ) (i j : Fin k) :
    matrixBlockAverage hkK
        (Matrix.of fun u v : Fin K ↦ matrixBlockAverage hKL M u v) i j =
      matrixBlockAverage (hkK.trans hKL) M i j := by
  have hK : 0 < K := Nat.pos_of_dvd_of_pos hKL hL
  have hk : 0 < k := Nat.pos_of_dvd_of_pos hkK hK
  have hr₁ : 0 < K / k := Nat.div_pos (Nat.le_of_dvd hK hkK) hk
  have hr₂ : 0 < L / K := Nat.div_pos (Nat.le_of_dvd hL hKL) hK
  have hratio : (K / k) * (L / K) = L / k := by
    simpa only [Nat.mul_comm] using Nat.div_mul_div hKL hkK
  let e := refinementQuotientEquiv hkK hKL
  have hsum :
      (∑ a : Fin (K / k), ∑ c : Fin (L / K),
          ∑ b : Fin (K / k), ∑ d : Fin (L / K),
            M (refinementIndex hKL (refinementIndex hkK i a) c)
              (refinementIndex hKL (refinementIndex hkK j b) d)) =
        ∑ u : Fin (L / k), ∑ v : Fin (L / k),
          M (refinementIndex (hkK.trans hKL) i u)
            (refinementIndex (hkK.trans hKL) j v) := by
    calc
      _ = ∑ p : Fin (K / k) × Fin (L / K),
          ∑ q : Fin (K / k) × Fin (L / K),
            M (refinementIndex (hkK.trans hKL) i (e p))
              (refinementIndex (hkK.trans hKL) j (e q)) := by
            simp only [Fintype.sum_prod_type]
            apply Fintype.sum_congr
            intro a
            apply Fintype.sum_congr
            intro c
            apply Fintype.sum_congr
            intro b
            apply Fintype.sum_congr
            intro d
            rw [refinementIndex_comp hkK hKL, refinementIndex_comp hkK hKL]
      _ = ∑ p : Fin (K / k) × Fin (L / K),
          ∑ v : Fin (L / k),
            M (refinementIndex (hkK.trans hKL) i (e p))
              (refinementIndex (hkK.trans hKL) j v) := by
            apply Fintype.sum_congr
            intro p
            exact e.sum_comp (fun v ↦
              M (refinementIndex (hkK.trans hKL) i (e p))
                (refinementIndex (hkK.trans hKL) j v))
      _ = _ := e.sum_comp (fun u ↦ ∑ v : Fin (L / k),
            M (refinementIndex (hkK.trans hKL) i u)
              (refinementIndex (hkK.trans hKL) j v))
  have hreorder :
      (∑ a : Fin (K / k), ∑ b : Fin (K / k),
          ∑ c : Fin (L / K), ∑ d : Fin (L / K),
            M (refinementIndex hKL (refinementIndex hkK i a) c)
              (refinementIndex hKL (refinementIndex hkK j b) d)) =
        ∑ a : Fin (K / k), ∑ c : Fin (L / K),
          ∑ b : Fin (K / k), ∑ d : Fin (L / K),
            M (refinementIndex hKL (refinementIndex hkK i a) c)
              (refinementIndex hKL (refinementIndex hkK j b) d) := by
    apply Fintype.sum_congr
    intro a
    rw [Finset.sum_comm]
  have sum_sum_div (A : Fin (K / k) → Fin (K / k) → ℝ) (c : ℝ) :
      (∑ a, ∑ b, A a b / c) = (∑ a, ∑ b, A a b) / c := by
    rw [Finset.sum_div]
    apply Fintype.sum_congr
    intro a
    rw [Finset.sum_div]
  simp only [matrixBlockAverage, Matrix.of_apply]
  field_simp
  rw [sum_sum_div]
  rw [hreorder, hsum]
  have hratioℝ : ((K / k : ℕ) : ℝ) * (L / K : ℕ) = (L / k : ℕ) := by
    exact_mod_cast hratio
  rw [← hratioℝ]
  field_simp

/-! ## Successive matrix systems -/

/-- A tower specified by exact compatibility only between successive levels.
All-level compatibility is derived locally below. -/
structure SuccessiveDensityMatrices where
  size : ℕ → ℕ
  size_pos : ∀ n, 0 < size n
  matrix : (n : ℕ) → Matrix (Fin (size n)) (Fin (size n)) ℝ
  matrix_symmetric : ∀ n, (matrix n).IsSymm
  matrix_mem_Icc : ∀ n i j, matrix n i j ∈ Icc (0 : ℝ) 1
  dvd_succ : ∀ n, size n ∣ size (n + 1)
  blockAverage_succ : ∀ n (i j : Fin (size n)),
    matrix n i j = matrixBlockAverage (dvd_succ n) (matrix (n + 1)) i j

namespace SuccessiveDensityMatrices

variable (Q : SuccessiveDensityMatrices)

/-- Successive divisibility implies divisibility between arbitrary ordered
levels. -/
theorem dvd_of_le {m n : ℕ} (h : m ≤ n) : Q.size m ∣ Q.size n := by
  induction n, h using Nat.le_induction with
  | base => exact dvd_refl _
  | succ n hmn ih => exact ih.trans (Q.dvd_succ n)

/-- Successive exact block averaging implies exact block averaging between any
two ordered levels. -/
theorem blockAverage_of_le {m n : ℕ} (h : m ≤ n)
    (i : Fin (Q.size m)) (j : Fin (Q.size m)) :
    Q.matrix m i j = matrixBlockAverage (Q.dvd_of_le h) (Q.matrix n) i j := by
  induction n, h using Nat.le_induction with
  | base =>
      simpa using (matrixBlockAverage_refl (Q.size_pos m) (Q.matrix m) i j).symm
  | succ n hmn ih =>
      let C : Matrix (Fin (Q.size n)) (Fin (Q.size n)) ℝ :=
        Matrix.of fun u v ↦ matrixBlockAverage (Q.dvd_succ n) (Q.matrix (n + 1)) u v
      have hC : C = Q.matrix n := by
        ext u v
        exact (Q.blockAverage_succ n u v).symm
      calc
        Q.matrix m i j = matrixBlockAverage (Q.dvd_of_le hmn) (Q.matrix n) i j := ih
        _ = matrixBlockAverage (Q.dvd_of_le hmn) C i j := by rw [hC]
        _ = matrixBlockAverage ((Q.dvd_of_le hmn).trans (Q.dvd_succ n))
              (Q.matrix (n + 1)) i j :=
            matrixBlockAverage_trans (Q.size_pos (n + 1))
              (Q.dvd_of_le hmn) (Q.dvd_succ n) (Q.matrix (n + 1)) i j
        _ = matrixBlockAverage (Q.dvd_of_le (Nat.le_succ_of_le hmn))
              (Q.matrix (n + 1)) i j := by
            congr

/-- Assemble an all-level nested density-matrix system from successive exact
compatibility. -/
def toNestedDensityMatrices : NestedDensityMatrices where
  size := Q.size
  size_pos := Q.size_pos
  matrix := Q.matrix
  matrix_symmetric := Q.matrix_symmetric
  matrix_mem_Icc := Q.matrix_mem_Icc
  dvd_of_le := Q.dvd_of_le
  blockAverage := Q.blockAverage_of_le

end SuccessiveDensityMatrices

/-! ## Entrywise limits and block compatibility -/

/-- On a fixed finite matrix space, entrywise convergence is preserved by
taking the average over a prescribed refinement block. -/
theorem matrixBlockAverage_tendsto {k K : ℕ} (h : k ∣ K)
    (M : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (L : Matrix (Fin K) (Fin K) ℝ)
    (hM : ∀ i j, Tendsto (fun n ↦ M n i j) atTop (nhds (L i j)))
    (i j : Fin k) :
    Tendsto (fun n ↦ matrixBlockAverage h (M n) i j) atTop
      (nhds (matrixBlockAverage h L i j)) := by
  simp only [matrixBlockAverage]
  apply Tendsto.div_const
  apply tendsto_finsetSum
  intro a ha
  apply tendsto_finsetSum
  intro b hb
  exact hM _ _

/-- An approximate block identity whose error tends to zero becomes an exact
block identity after taking entrywise limits. -/
theorem matrixBlockAverage_eq_of_tendsto_of_abs_sub_le {k K : ℕ} (h : k ∣ K)
    (C : ℕ → Matrix (Fin k) (Fin k) ℝ)
    (M : ℕ → Matrix (Fin K) (Fin K) ℝ)
    (C_lim : Matrix (Fin k) (Fin k) ℝ)
    (M_lim : Matrix (Fin K) (Fin K) ℝ)
    (hC : ∀ i j, Tendsto (fun n ↦ C n i j) atTop (nhds (C_lim i j)))
    (hM : ∀ i j, Tendsto (fun n ↦ M n i j) atTop (nhds (M_lim i j)))
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (happrox : ∀ n i j,
      |C n i j - matrixBlockAverage h (M n) i j| ≤ error n) :
    ∀ i j, C_lim i j = matrixBlockAverage h M_lim i j := by
  intro i j
  have hblock := matrixBlockAverage_tendsto h M M_lim hM i j
  have hdiff :
      Tendsto (fun n ↦ C n i j - matrixBlockAverage h (M n) i j) atTop
        (nhds (C_lim i j - matrixBlockAverage h M_lim i j)) :=
    (hC i j).sub hblock
  have habs :
      Tendsto (fun n ↦ |C n i j - matrixBlockAverage h (M n) i j|) atTop
        (nhds |C_lim i j - matrixBlockAverage h M_lim i j|) := by
    simpa only [Real.norm_eq_abs] using hdiff.norm
  have habs_zero :
      Tendsto (fun n ↦ |C n i j - matrixBlockAverage h (M n) i j|) atTop
        (nhds 0) :=
    squeeze_zero (fun n ↦ abs_nonneg _) (fun n ↦ happrox n i j) herror
  have hz : |C_lim i j - matrixBlockAverage h M_lim i j| = 0 :=
    tendsto_nhds_unique habs habs_zero
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

/-! ## From fixed-size matrix limits to graphon limits -/

/-- Entrywise convergence on a fixed finite matrix space gives `L¹`
convergence of the corresponding equal-cell matrix graphons. -/
theorem matrixGraphon_tendsto_graphonL1Dist_of_entrywise {q : ℕ}
    (M : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (L : Matrix (Fin q) (Fin q) ℝ)
    (hM_symm : ∀ n, (M n).IsSymm) (hL_symm : L.IsSymm)
    (hM_zero : ∀ n i j, 0 ≤ M n i j) (hM_one : ∀ n i j, M n i j ≤ 1)
    (hL_zero : ∀ i j, 0 ≤ L i j) (hL_one : ∀ i j, L i j ≤ 1)
    (hM : ∀ i j, Tendsto (fun n ↦ M n i j) atTop (nhds (L i j))) :
    Tendsto
      (fun n ↦ graphonL1Dist
        (matrixGraphon (M n) (hM_symm n) (hM_zero n) (hM_one n))
        (matrixGraphon L hL_symm hL_zero hL_one))
      atTop (nhds 0) := by
  let error : ℕ → ℝ := fun n ↦
    ∑ i : Fin q, ∑ j : Fin q, |M n i j - L i j|
  have hterm (i j : Fin q) :
      Tendsto (fun n ↦ |M n i j - L i j|) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ L i j) atTop (nhds (L i j)) :=
      tendsto_const_nhds
    have hsub := (hM i j).sub hconst
    simpa [Real.norm_eq_abs] using hsub.norm
  have herror : Tendsto error atTop (nhds 0) := by
    dsimp only [error]
    simpa using
      (tendsto_finsetSum Finset.univ fun i _ ↦
        tendsto_finsetSum Finset.univ fun j _ ↦ hterm i j)
  have herror_nonneg (n : ℕ) : 0 ≤ error n := by
    dsimp only [error]
    positivity
  have hentry (n : ℕ) (i j : Fin q) : |M n i j - L i j| ≤ error n := by
    dsimp only [error]
    calc
      |M n i j - L i j| ≤ ∑ b : Fin q, |M n i b - L i b| := by
        exact Finset.single_le_sum (fun b _ ↦ abs_nonneg (M n i b - L i b))
          (Finset.mem_univ j)
      _ ≤ ∑ a : Fin q, ∑ b : Fin q, |M n a b - L a b| := by
        exact Finset.single_le_sum
          (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ abs_nonneg (M n a b - L a b))
          (Finset.mem_univ i)
  apply squeeze_zero
  · intro n
    exact graphonL1Dist_nonneg _ _
  · intro n
    exact graphonL1Dist_matrixGraphon_le (M n) L (hM_symm n) hL_symm
      (hM_zero n) (hM_one n) hL_zero hL_one (herror_nonneg n) (hentry n)
  · exact herror

/-! ## Finite-family and diagonal adapters -/

/-- Every sequence of natural-number lower bounds admits one strictly
increasing pointwise majorant. -/
theorem exists_strictMono_ge (bound : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, bound n ≤ φ n := by
  let φ : ℕ → ℕ := fun n ↦ n + (∑ i ∈ Finset.range (n + 1), bound i)
  have hstrict : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    simp only [φ, Finset.sum_range_succ]
    omega
  refine ⟨φ, hstrict, ?_⟩
  intro n
  have hterm : bound n ≤ ∑ i ∈ Finset.range (n + 1), bound i :=
    Finset.single_le_sum (fun i _ ↦ Nat.zero_le (bound i))
      (Finset.mem_range.2 (Nat.lt_succ_self n))
  dsimp only [φ]
  omega

/-- Choose one strictly increasing, hence cofinal, index at every level so
that a level-indexed eventual property holds at the chosen index. -/
theorem exists_strictMono_selection_of_eventually {P : ℕ → ℕ → Prop}
    (hP : ∀ m, ∀ᶠ n in atTop, P m n) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto φ atTop atTop ∧ ∀ m, P m (φ m) := by
  choose bound hbound using fun m ↦ eventually_atTop.1 (hP m)
  obtain ⟨φ, hφ, hφ_bound⟩ := exists_strictMono_ge bound
  refine ⟨φ, hφ, hφ.tendsto_atTop, ?_⟩
  intro m
  exact hbound m (φ m) (hφ_bound m)

/-- Finitely many eventual properties hold simultaneously. -/
theorem eventually_forall_finite {ι : Type*} [Finite ι]
    {P : ι → ℕ → Prop} (hP : ∀ i, ∀ᶠ n in atTop, P i n) :
    ∀ᶠ n in atTop, ∀ i, P i n :=
  Filter.eventually_all.2 hP

/-- Threshold form of simultaneous eventuality for a finite family. -/
theorem exists_threshold_forall_finite {ι : Type*} [Finite ι]
    {P : ι → ℕ → Prop} (hP : ∀ i, ∀ᶠ n in atTop, P i n) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ i, P i n := by
  simpa only [eventually_atTop] using eventually_forall_finite hP

/-- A finite family of convergent sequences retains all its limits along one
strictly monotone extraction. -/
theorem finiteFamily_tendsto_subsequence {ι α : Type*} [Finite ι]
    [TopologicalSpace α] (u : ι → ℕ → α) (a : ι → α)
    (hu : ∀ i, Tendsto (u i) atTop (nhds (a i)))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∀ i, Tendsto (fun n ↦ u i (φ n)) atTop (nhds (a i)) := by
  intro i
  exact (hu i).comp hφ.tendsto_atTop

namespace SubsequenceTower

/-- An eventual property along a fixed row of a subsequence tower holds
eventually along the tower diagonal. -/
theorem eventually_diagonal_of_eventually_row (T : SubsequenceTower)
    {P : ℕ → Prop} {m : ℕ}
    (hP : ∀ᶠ k in atTop, P (T.extraction m k)) :
    ∀ᶠ n in atTop, P (T.diagonal n) := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hP)
  filter_upwards [eventually_ge_atTop (max m N)] with n hn
  have hmn : m ≤ n := (le_max_left m N).trans hn
  have hNn : N ≤ n := (le_max_right m N).trans hn
  obtain ⟨φ, hφ, hφeq⟩ := T.refines_of_le hmn
  have hNφ : N ≤ φ n := hNn.trans (hφ.id_le n)
  simpa only [diagonal, hφeq, Function.comp_apply] using hN (φ n) hNφ

end SubsequenceTower

/-! ## Geometric growth -/

/-- Doubling at every step gives the explicit lower bound `2^n`. -/
theorem pow_two_le_of_two_mul_le_succ (t : ℕ → ℕ) (ht₀ : 1 ≤ t 0)
    (hgrow : ∀ n, 2 * t n ≤ t (n + 1)) :
    ∀ n, 2 ^ n ≤ t n := by
  intro n
  induction n with
  | zero => simpa using ht₀
  | succ n ih =>
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; omega
        _ ≤ 2 * t n := Nat.mul_le_mul_left 2 ih
        _ ≤ t (n + 1) := hgrow n

/-- A positive sequence which at least doubles at every step tends to
infinity. -/
theorem tendsto_atTop_of_two_mul_le_succ (t : ℕ → ℕ) (ht₀ : 1 ≤ t 0)
    (hgrow : ∀ n, 2 * t n ≤ t (n + 1)) :
    Tendsto t atTop atTop := by
  apply tendsto_atTop_mono (pow_two_le_of_two_mul_le_succ t ht₀ hgrow)
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)

/-- The reciprocal of the real cast of a geometrically growing natural
sequence tends to zero. -/
theorem tendsto_one_div_natCast_of_two_mul_le_succ (t : ℕ → ℕ)
    (ht₀ : 1 ≤ t 0) (hgrow : ∀ n, 2 * t n ≤ t (n + 1)) :
    Tendsto (fun n ↦ 1 / (t n : ℝ)) atTop (nhds 0) := by
  have ht : Tendsto t atTop atTop := tendsto_atTop_of_two_mul_le_succ t ht₀ hgrow
  have htℝ : Tendsto (fun n ↦ (t n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  convert tendsto_inv_atTop_zero.comp htℝ using 1
  funext n
  simp only [Function.comp_apply, one_div]

/-! ## Generic recursive matrix towers -/

/-- The matrix-and-extraction projection of one clean Type-tower level.

The concrete construction retains considerably more data (the actual Types
and clean partitions).  This small projection is the interface needed to
assemble the nested subsequences and the successive limiting matrices. -/
structure MatrixSubsequenceLevel where
  size : ℕ
  size_pos : 0 < size
  extraction : ℕ → ℕ
  extraction_strictMono : StrictMono extraction
  matrix : Matrix (Fin size) (Fin size) ℝ
  matrix_symmetric : matrix.IsSymm
  matrix_mem_Icc : ∀ i j, matrix i j ∈ Icc (0 : ℝ) 1

/-- One exact step of a recursive limiting-matrix tower.  The child
extraction is explicitly a subsequence of the parent extraction, and the
parent limiting matrix is the consecutive block average of the child
limiting matrix. -/
structure MatrixSubsequenceStep (parent : MatrixSubsequenceLevel) where
  child : MatrixSubsequenceLevel
  factor : ℕ → ℕ
  factor_strictMono : StrictMono factor
  extraction_eq : child.extraction = parent.extraction ∘ factor
  size_dvd : parent.size ∣ child.size
  blockAverage : ∀ i j,
    parent.matrix i j = matrixBlockAverage size_dvd child.matrix i j

/-- A fully assembled infinite tower of limiting matrices and nested
extraction rows.  Unlike `MatrixSubsequenceSystem.level`, this presentation
is convenient when the richer clean-Type levels have already been built by
dependent recursion and are merely being projected to their matrix data. -/
structure MatrixSubsequenceTower where
  level : ℕ → MatrixSubsequenceLevel
  factor : ℕ → ℕ → ℕ
  factor_strictMono : ∀ n, StrictMono (factor n)
  extraction_succ : ∀ n,
    (level (n + 1)).extraction = (level n).extraction ∘ factor n
  size_dvd_succ : ∀ n, (level n).size ∣ (level (n + 1)).size
  blockAverage_succ : ∀ n (i j : Fin (level n).size),
    (level n).matrix i j =
      matrixBlockAverage (size_dvd_succ n) (level (n + 1)).matrix i j

namespace MatrixSubsequenceTower

variable (T : MatrixSubsequenceTower)

/-- Forget the matrices and retain the nested extraction rows. -/
noncomputable def toSubsequenceTower : SubsequenceTower where
  extraction n := (T.level n).extraction
  strictMono n := (T.level n).extraction_strictMono
  next_refines n :=
    ⟨T.factor n, T.factor_strictMono n, T.extraction_succ n⟩

/-- Forget the extraction rows and retain the exact successive matrices. -/
noncomputable def toSuccessiveDensityMatrices : SuccessiveDensityMatrices where
  size n := (T.level n).size
  size_pos n := (T.level n).size_pos
  matrix n := (T.level n).matrix
  matrix_symmetric n := (T.level n).matrix_symmetric
  matrix_mem_Icc n := (T.level n).matrix_mem_Icc
  dvd_succ n := T.size_dvd_succ n
  blockAverage_succ n := T.blockAverage_succ n

/-- Assemble the exact all-level Lovasz--Szegedy input. -/
noncomputable def toNestedDensityMatrices : NestedDensityMatrices :=
  T.toSuccessiveDensityMatrices.toNestedDensityMatrices

end MatrixSubsequenceTower

namespace MatrixSubsequenceSystem

/-- Recursively iterate a chosen exact matrix-tower extension. -/
noncomputable def level
    (base : MatrixSubsequenceLevel)
    (next : (n : ℕ) → (L : MatrixSubsequenceLevel) →
      MatrixSubsequenceStep L) :
    ℕ → MatrixSubsequenceLevel
  | 0 => base
  | n + 1 => (next n (level base next n)).child

@[simp]
theorem level_zero
    (base : MatrixSubsequenceLevel)
    (next : (n : ℕ) → (L : MatrixSubsequenceLevel) →
      MatrixSubsequenceStep L) :
    level base next 0 = base :=
  rfl

@[simp]
theorem level_succ
    (base : MatrixSubsequenceLevel)
    (next : (n : ℕ) → (L : MatrixSubsequenceLevel) →
      MatrixSubsequenceStep L) (n : ℕ) :
    level base next (n + 1) = (next n (level base next n)).child :=
  rfl

/-- The extraction maps of a recursively chosen exact matrix tower form a
`SubsequenceTower`. -/
noncomputable def subsequenceTower
    (base : MatrixSubsequenceLevel)
    (next : (n : ℕ) → (L : MatrixSubsequenceLevel) →
      MatrixSubsequenceStep L) : SubsequenceTower where
  extraction n := (level base next n).extraction
  strictMono n := (level base next n).extraction_strictMono
  next_refines n :=
    ⟨(next n (level base next n)).factor,
      (next n (level base next n)).factor_strictMono,
      (next n (level base next n)).extraction_eq⟩

/-- The limiting matrices of a recursively chosen exact tower, packaged in
the successive form from which all-level compatibility is derived. -/
noncomputable def successiveDensityMatrices
    (base : MatrixSubsequenceLevel)
    (next : (n : ℕ) → (L : MatrixSubsequenceLevel) →
      MatrixSubsequenceStep L) : SuccessiveDensityMatrices where
  size n := (level base next n).size
  size_pos n := (level base next n).size_pos
  matrix n := (level base next n).matrix
  matrix_symmetric n := (level base next n).matrix_symmetric
  matrix_mem_Icc n := (level base next n).matrix_mem_Icc
  dvd_succ n := (next n (level base next n)).size_dvd
  blockAverage_succ n := (next n (level base next n)).blockAverage

/-- Exact all-level nested matrices assembled from the recursive tower. -/
noncomputable def nestedDensityMatrices
    (base : MatrixSubsequenceLevel)
    (next : (n : ℕ) → (L : MatrixSubsequenceLevel) →
      MatrixSubsequenceStep L) : NestedDensityMatrices :=
  (successiveDensityMatrices base next).toNestedDensityMatrices

end MatrixSubsequenceSystem

end Graphon

end InducedStars
