import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import DenseGraph.FiniteModels.BernoulliProduct

/-!
# Independent fixed-cardinality block models

This file develops the elementary finite counting layer for sampling an
independent uniformly random subset of a prescribed size from each of finitely
many disjoint coordinate blocks.  It contains no probabilistic axioms: all
weights are explicit finite sums.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace DenseGraph

/-- Finite pairwise-disjoint coordinate blocks together with an admissible
cardinality quota in every block. -/
structure FixedCardinalityBlockModel
    (I Ω : Type*) [Fintype I] [DecidableEq I]
    [Fintype Ω] [DecidableEq Ω] where
  block : I → Finset Ω
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ block
  quota : I → ℕ
  quota_le : ∀ i, quota i ≤ (block i).card

namespace FixedCardinalityBlockModel

variable {I Ω : Type*} [Fintype I] [DecidableEq I]
  [Fintype Ω] [DecidableEq Ω]

/-- The exact-size choices available in one block. -/
abbrev BlockSample (M : FixedCardinalityBlockModel I Ω) (i : I) :=
  ↑((Finset.univ : Finset ↑(M.block i)).powersetCard (M.quota i))

/-- A sample chooses one exact-size subset independently in every block. -/
abbrev Sample (M : FixedCardinalityBlockModel I Ω) :=
  ∀ i, M.BlockSample i

/-- The selected ambient coordinates in one block. -/
def selectedInBlock (M : FixedCardinalityBlockModel I Ω)
    (S : M.Sample) (i : I) : Finset Ω :=
  (S i).1.map ⟨Subtype.val, Subtype.val_injective⟩

/-- A selected block sample is contained in its prescribed ambient block. -/
theorem selectedInBlock_subset (M : FixedCardinalityBlockModel I Ω)
    (S : M.Sample) (i : I) :
    M.selectedInBlock S i ⊆ M.block i := by
  intro x hx
  obtain ⟨y, _hy, rfl⟩ := Finset.mem_map.mp hx
  exact y.2

/-- A selected block sample has exactly its prescribed quota. -/
@[simp] theorem card_selectedInBlock (M : FixedCardinalityBlockModel I Ω)
    (S : M.Sample) (i : I) :
    (M.selectedInBlock S i).card = M.quota i := by
  rw [selectedInBlock, Finset.card_map]
  exact (Finset.mem_powersetCard.mp (S i).2).2

/-- The number of fixed-cardinality samples. -/
def sampleSpaceCard (M : FixedCardinalityBlockModel I Ω) : ℕ :=
  ∏ i, Nat.choose (M.block i).card (M.quota i)

/-- Exact product formula for the finite sample space. -/
theorem card_sample (M : FixedCardinalityBlockModel I Ω) :
    Fintype.card M.Sample = M.sampleSpaceCard := by
  classical
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_coe]

/-- Every admissible fixed-cardinality sample space is nonempty. -/
theorem sampleSpaceCard_pos (M : FixedCardinalityBlockModel I Ω) :
    0 < M.sampleSpaceCard := by
  classical
  exact Finset.prod_pos fun i _ ↦ Nat.choose_pos (M.quota_le i)

/-- Every admissible fixed-cardinality sample space has nonzero cardinality. -/
theorem sampleSpaceCard_ne_zero (M : FixedCardinalityBlockModel I Ω) :
    M.sampleSpaceCard ≠ 0 :=
  (M.sampleSpaceCard_pos).ne'

/-- The uniform weight of a fixed-cardinality sample. -/
def sampleWeight (M : FixedCardinalityBlockModel I Ω)
    (_S : M.Sample) : ℝ :=
  (M.sampleSpaceCard : ℝ)⁻¹

/-- Every sample has exactly the same weight. -/
theorem sampleWeight_eq (M : FixedCardinalityBlockModel I Ω)
    (S : M.Sample) :
    M.sampleWeight S = (M.sampleSpaceCard : ℝ)⁻¹ :=
  rfl

/-- The uniform fixed-cardinality weight is strictly positive. -/
theorem sampleWeight_pos (M : FixedCardinalityBlockModel I Ω)
    (S : M.Sample) : 0 < M.sampleWeight S := by
  rw [sampleWeight]
  exact inv_pos.mpr (by exact_mod_cast M.sampleSpaceCard_pos)

/-- The explicit uniform weight normalizes to one. -/
theorem sum_sampleWeight_eq_one (M : FixedCardinalityBlockModel I Ω) :
    ∑ S : M.Sample, M.sampleWeight S = 1 := by
  classical
  simp [sampleWeight, M.card_sample, M.sampleSpaceCard_ne_zero]

/-- Uniform probability of a finite event of fixed-cardinality samples. -/
def eventProbability (M : FixedCardinalityBlockModel I Ω)
    (E : Finset M.Sample) : ℝ :=
  ∑ S ∈ E, M.sampleWeight S

/-- Fixed-cardinality event probability is exactly a cardinality ratio. -/
theorem eventProbability_eq_card_div (M : FixedCardinalityBlockModel I Ω)
    (E : Finset M.Sample) :
    M.eventProbability E = (E.card : ℝ) / M.sampleSpaceCard := by
  classical
  simp [eventProbability, sampleWeight, div_eq_mul_inv, mul_comm]

/-- The full fixed-cardinality sample space has probability one. -/
@[simp] theorem eventProbability_univ (M : FixedCardinalityBlockModel I Ω) :
    M.eventProbability (Finset.univ : Finset M.Sample) = 1 := by
  classical
  simpa [eventProbability] using M.sum_sampleWeight_eq_one

/-- Fixed-cardinality event probabilities are nonnegative. -/
theorem eventProbability_nonneg (M : FixedCardinalityBlockModel I Ω)
    (E : Finset M.Sample) :
    0 ≤ M.eventProbability E := by
  unfold eventProbability
  exact Finset.sum_nonneg fun S _ ↦ (M.sampleWeight_pos S).le

/-- Fixed-cardinality event probabilities are at most one. -/
theorem eventProbability_le_one (M : FixedCardinalityBlockModel I Ω)
    (E : Finset M.Sample) :
    M.eventProbability E ≤ 1 := by
  rw [M.eventProbability_eq_card_div]
  apply (div_le_one (by exact_mod_cast M.sampleSpaceCard_pos)).2
  have hcard : E.card ≤ M.sampleSpaceCard := by
    rw [← M.card_sample, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ E)
  exact_mod_cast hcard

/-- Fixed-cardinality event probability is monotone under event inclusion. -/
theorem eventProbability_mono (M : FixedCardinalityBlockModel I Ω)
    {E F : Finset M.Sample} (hEF : E ⊆ F) :
    M.eventProbability E ≤ M.eventProbability F := by
  unfold eventProbability
  exact Finset.sum_le_sum_of_subset_of_nonneg hEF
    (fun S _ _ ↦ (M.sampleWeight_pos S).le)

/-! ## Elementary binomial masses -/

/-- The real binomial point mass, written without a measure-theory wrapper. -/
def binomialPointMass (N r : ℕ) (q : ℝ) : ℝ :=
  (Nat.choose N r : ℝ) * q ^ r * (1 - q) ^ (N - r)

/-- The success parameter attached to an exact quota.  When `N = 0`,
admissibility forces `m = 0`, and the total real division convention gives
the harmless value zero. -/
def quotaParameter (N m : ℕ) : ℝ :=
  (m : ℝ) / (N : ℝ)

/-- Adjacent binomial masses satisfy the standard cross-multiplied
recurrence.  This form avoids division by `q` or `1-q` and hence remains
valid at the boundary parameters. -/
theorem binomialPointMass_succ_cross
    {N r : ℕ} (hr : r < N) (q : ℝ) :
    ((r + 1 : ℕ) : ℝ) * (1 - q) * binomialPointMass N (r + 1) q =
      ((N - r : ℕ) : ℝ) * q * binomialPointMass N r q := by
  have hrle : r + 1 ≤ N := Nat.succ_le_iff.mpr hr
  have hsub : N - r = (N - (r + 1)) + 1 := by omega
  have hchooseNat := Nat.choose_succ_right_eq N r
  have hchoose :
      (Nat.choose N (r + 1) : ℝ) * (r + 1 : ℕ) =
        (Nat.choose N r : ℝ) * (N - r : ℕ) := by
    exact_mod_cast hchooseNat
  have hpow :
      (1 - q) ^ (N - r) =
        (1 - q) ^ (N - (r + 1)) * (1 - q) := by
    rw [hsub, pow_succ]
  unfold binomialPointMass
  rw [pow_succ q r, hpow]
  calc
    ((r + 1 : ℕ) : ℝ) * (1 - q) *
        ((Nat.choose N (r + 1) : ℝ) * (q ^ r * q) *
          (1 - q) ^ (N - (r + 1))) =
        ((Nat.choose N (r + 1) : ℝ) * (r + 1 : ℕ)) *
          q * q ^ r * (1 - q) ^ (N - (r + 1)) * (1 - q) := by ring
    _ = ((Nat.choose N r : ℝ) * (N - r : ℕ)) *
          q * q ^ r * (1 - q) ^ (N - (r + 1)) * (1 - q) := by rw [hchoose]
    _ = ((N - r : ℕ) : ℝ) * q *
        ((Nat.choose N r : ℝ) * q ^ r *
          ((1 - q) ^ (N - (r + 1)) * (1 - q))) := by ring

/-- Binomial point masses are nonnegative for a genuine Bernoulli
parameter. -/
theorem binomialPointMass_nonneg {N r : ℕ} {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ binomialPointMass N r q := by
  unfold binomialPointMass
  exact mul_nonneg
    (mul_nonneg (by positivity) (pow_nonneg hq.1 _))
    (pow_nonneg (sub_nonneg.mpr hq.2) _)

/-- The binomial point masses through `N` sum to one. -/
theorem sum_binomialPointMass (N : ℕ) (q : ℝ) :
    ∑ r ∈ Finset.range (N + 1), binomialPointMass N r q = 1 := by
  calc
    ∑ r ∈ Finset.range (N + 1), binomialPointMass N r q =
        ∑ r ∈ Finset.range (N + 1),
          q ^ r * (1 - q) ^ (N - r) * (Nat.choose N r : ℝ) := by
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [binomialPointMass]
      ring
    _ = (q + (1 - q)) ^ N :=
      (Commute.add_pow (Commute.all q (1 - q)) N).symm
    _ = 1 := by ring

/-- A single binomial mass is at most one. -/
theorem binomialPointMass_le_one {N r : ℕ} {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hr : r ≤ N) :
    binomialPointMass N r q ≤ 1 := by
  have hrmem : r ∈ Finset.range (N + 1) := by simp; omega
  calc
    binomialPointMass N r q ≤
        ∑ s ∈ Finset.range (N + 1), binomialPointMass N s q := by
      exact Finset.single_le_sum
        (s := Finset.range (N + 1))
        (f := fun s ↦ binomialPointMass N s q)
        (fun s hs ↦ binomialPointMass_nonneg hq) hrmem
    _ = 1 := sum_binomialPointMass N q

private theorem quotaParameter_mem_Icc {N m : ℕ} (hm : m ≤ N) :
    quotaParameter N m ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · by_cases hN : N = 0
    · have hm0 : m = 0 := by omega
      simp [quotaParameter, hN, hm0]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)).2
      exact_mod_cast hm

private theorem quotaParameter_succ_mono
    {N m r : ℕ} (hmpos : 0 < m) (hmN : m < N) (hrm : r < m) :
    binomialPointMass N r (quotaParameter N m) ≤
      binomialPointMass N (r + 1) (quotaParameter N m) := by
  let q := quotaParameter N m
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hmN.trans' hmpos
  have hqpos : 0 < q := by
    dsimp [q, quotaParameter]
    exact div_pos (by exact_mod_cast hmpos) hNpos
  have hqone : q < 1 := by
    dsimp [q, quotaParameter]
    exact (div_lt_one hNpos).2 (by exact_mod_cast hmN)
  have hrN : r < N := hrm.trans hmN
  have hcoefficient :
      ((r + 1 : ℕ) : ℝ) * (1 - q) ≤
        ((N - r : ℕ) : ℝ) * q := by
    dsimp [q, quotaParameter]
    rw [Nat.cast_sub (Nat.le_of_lt hrN)]
    field_simp
    have hrmR : (r : ℝ) < m := by exact_mod_cast hrm
    have hmNR : (m : ℝ) < N := by exact_mod_cast hmN
    have hrNR : (r : ℝ) < N := by exact_mod_cast hrN
    have hsucc : r + 1 ≤ m := Nat.succ_le_iff.mpr hrm
    have hsuccR : ((r + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hsucc
    have hgap : 0 ≤ (m : ℝ) - ((r : ℝ) + 1) := by
      norm_num at hsuccR ⊢
      exact hsuccR
    have hmul : 0 ≤ (N : ℝ) * ((m : ℝ) - ((r : ℝ) + 1)) :=
      mul_nonneg hNpos.le hgap
    norm_num at *
    nlinarith [hmul]
  have hleftpos : 0 < ((r + 1 : ℕ) : ℝ) * (1 - q) := by
    exact mul_pos (by positivity) (sub_pos.mpr hqone)
  have hmassnonneg :
      0 ≤ binomialPointMass N r q :=
    binomialPointMass_nonneg (quotaParameter_mem_Icc (Nat.le_of_lt hmN))
  have hscaled :
      ((r + 1 : ℕ) : ℝ) * (1 - q) * binomialPointMass N r q ≤
        ((r + 1 : ℕ) : ℝ) * (1 - q) *
          binomialPointMass N (r + 1) q := by
    calc
      ((r + 1 : ℕ) : ℝ) * (1 - q) * binomialPointMass N r q ≤
          ((N - r : ℕ) : ℝ) * q * binomialPointMass N r q :=
        mul_le_mul_of_nonneg_right hcoefficient hmassnonneg
      _ = ((r + 1 : ℕ) : ℝ) * (1 - q) *
          binomialPointMass N (r + 1) q :=
        (binomialPointMass_succ_cross hrN q).symm
  exact (mul_le_mul_iff_of_pos_left hleftpos).mp hscaled

private theorem quotaParameter_succ_antitone
    {N m r : ℕ} (hmpos : 0 < m) (hmN : m < N)
    (hmr : m ≤ r) (hrN : r < N) :
    binomialPointMass N (r + 1) (quotaParameter N m) ≤
      binomialPointMass N r (quotaParameter N m) := by
  let q := quotaParameter N m
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hmN.trans' hmpos
  have hqone : q < 1 := by
    dsimp [q, quotaParameter]
    exact (div_lt_one hNpos).2 (by exact_mod_cast hmN)
  have hcoefficient :
      ((N - r : ℕ) : ℝ) * q ≤
        ((r + 1 : ℕ) : ℝ) * (1 - q) := by
    dsimp [q, quotaParameter]
    rw [Nat.cast_sub (Nat.le_of_lt hrN)]
    field_simp
    have hmrR : (m : ℝ) ≤ r := by exact_mod_cast hmr
    have hmNR : (m : ℝ) < N := by exact_mod_cast hmN
    have hrNR : (r : ℝ) < N := by exact_mod_cast hrN
    have hgap : (1 : ℝ) ≤ ((r : ℝ) + 1) - m := by
      nlinarith
    have hmul : (N : ℝ) * 1 ≤
        (N : ℝ) * (((r : ℝ) + 1) - m) :=
      mul_le_mul_of_nonneg_left hgap hNpos.le
    norm_num at *
    have hid :
        ((r : ℝ) + 1) * ((N : ℝ) - m) -
            ((N : ℝ) - r) * m =
          (N : ℝ) * (((r : ℝ) + 1) - m) - m := by ring
    have hnonneg :
        0 ≤ (N : ℝ) * (((r : ℝ) + 1) - m) - m := by
      have hmNRreal : (m : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.le_of_lt hmN
      exact sub_nonneg.mpr (hmNRreal.trans hmul)
    nlinarith [hid, hnonneg]
  have hleftpos : 0 < ((r + 1 : ℕ) : ℝ) * (1 - q) := by
    exact mul_pos (by positivity) (sub_pos.mpr hqone)
  have hmassnonneg :
      0 ≤ binomialPointMass N r q :=
    binomialPointMass_nonneg (quotaParameter_mem_Icc (Nat.le_of_lt hmN))
  have hscaled :
      ((r + 1 : ℕ) : ℝ) * (1 - q) *
          binomialPointMass N (r + 1) q ≤
        ((r + 1 : ℕ) : ℝ) * (1 - q) * binomialPointMass N r q := by
    calc
      ((r + 1 : ℕ) : ℝ) * (1 - q) *
          binomialPointMass N (r + 1) q =
          ((N - r : ℕ) : ℝ) * q * binomialPointMass N r q :=
        binomialPointMass_succ_cross hrN q
      _ ≤ ((r + 1 : ℕ) : ℝ) * (1 - q) * binomialPointMass N r q :=
        mul_le_mul_of_nonneg_right hcoefficient hmassnonneg
  exact (mul_le_mul_iff_of_pos_left hleftpos).mp hscaled

/-- For parameter `m/N`, the mass at `m` is at least every other supported
binomial mass.  The proof is the elementary adjacent-ratio argument, with the
two degenerate parameters handled separately. -/
theorem quotaParameter_is_binomial_mode
    {N m r : ℕ} (hm : m ≤ N) (hr : r ≤ N) :
    binomialPointMass N r (quotaParameter N m) ≤
      binomialPointMass N m (quotaParameter N m) := by
  by_cases hm0 : m = 0
  · subst m
    have hle := binomialPointMass_le_one
      (quotaParameter_mem_Icc (Nat.zero_le N)) hr
    simpa [binomialPointMass, quotaParameter] using hle
  by_cases hmN : m = N
  · subst m
    have hNpos : 0 < N := Nat.pos_of_ne_zero hm0
    have hle := binomialPointMass_le_one
      (quotaParameter_mem_Icc (le_rfl : N ≤ N)) hr
    have hcast : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    simpa [binomialPointMass, quotaParameter, hcast] using hle
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hmLtN : m < N := lt_of_le_of_ne hm hmN
  rcases le_total r m with hrm | hmr
  · have hchain : ∀ n (hrn : r ≤ n), n ≤ m →
        binomialPointMass N r (quotaParameter N m) ≤
          binomialPointMass N n (quotaParameter N m) := by
      refine Nat.le_induction (m := r) (P := fun n _ ↦ n ≤ m →
          binomialPointMass N r (quotaParameter N m) ≤
            binomialPointMass N n (quotaParameter N m)) ?_ ?_
      · intro _hrm
        exact le_rfl
      · intro n hrn ih hsucc
        exact (ih (Nat.le_trans (Nat.le_succ n) hsucc)).trans
          (quotaParameter_succ_mono hmpos hmLtN
            (Nat.lt_of_succ_le hsucc))
    exact hchain m hrm le_rfl
  · have hchain : ∀ n (hmn : m ≤ n), n ≤ N →
        binomialPointMass N n (quotaParameter N m) ≤
          binomialPointMass N m (quotaParameter N m) := by
      refine Nat.le_induction (m := m) (P := fun n _ ↦ n ≤ N →
          binomialPointMass N n (quotaParameter N m) ≤
            binomialPointMass N m (quotaParameter N m)) ?_ ?_
      · intro _hmN
        exact le_rfl
      · intro n hmn ih hsucc
        exact (quotaParameter_succ_antitone hmpos hmLtN hmn
          (Nat.lt_of_succ_le hsucc)).trans
            (ih (Nat.le_trans (Nat.le_succ n) hsucc))
    exact hchain r hmr hr

/-- The mode point mass of `Bin(N,m/N)` is at least `1/(N+1)`, including
the boundary cases `m=0` and `m=N`.  This is the finite maximum-at-least-
average argument and uses no asymptotics. -/
theorem binomialModePointMass_ge_inv_succ
    {N m : ℕ} (hm : m ≤ N) :
    1 / ((N + 1 : ℕ) : ℝ) ≤
      binomialPointMass N m (quotaParameter N m) := by
  have hsum :
      (∑ r ∈ Finset.range (N + 1),
          binomialPointMass N r (quotaParameter N m)) ≤
        ∑ _r ∈ Finset.range (N + 1),
          binomialPointMass N m (quotaParameter N m) := by
    exact Finset.sum_le_sum fun r hrange ↦
      quotaParameter_is_binomial_mode hm (by simpa using hrange)
  rw [sum_binomialPointMass, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hpos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  exact (div_le_iff₀ hpos).2 (by simpa [mul_comm] using hsum)

/-! ## Tagged block coordinates and the associated Bernoulli law -/

/-- The tagged disjoint union of all block coordinates.  Tagging makes block
ownership definitional and also gives a useful model when the ambient type has
coordinates outside the listed blocks. -/
abbrev Coordinate (M : FixedCardinalityBlockModel I Ω) :=
  Σ i, ↑(M.block i)

/-- Combine the independently chosen block subsets into one tagged Bernoulli
outcome. -/
def sampleOutcome (M : FixedCardinalityBlockModel I Ω)
    (S : M.Sample) : Finset M.Coordinate :=
  Finset.univ.sigma fun i ↦ (S i).1

@[simp] theorem mem_sampleOutcome (M : FixedCardinalityBlockModel I Ω)
    (S : M.Sample) (e : M.Coordinate) :
    e ∈ M.sampleOutcome S ↔ e.2 ∈ (S e.1).1 := by
  rcases e with ⟨i, x⟩
  simp [sampleOutcome]

/-- A fixed sample is determined by its combined tagged outcome. -/
theorem sampleOutcome_injective (M : FixedCardinalityBlockModel I Ω) :
    Function.Injective M.sampleOutcome := by
  intro S T hST
  funext i
  apply Subtype.ext
  ext x
  have hmem := congrArg
    (fun U : Finset M.Coordinate ↦ (⟨i, x⟩ : M.Coordinate) ∈ U) hST
  simpa using hmem

/-- The embedding of fixed samples into tagged Bernoulli outcomes. -/
def sampleOutcomeEmbedding (M : FixedCardinalityBlockModel I Ω) :
    M.Sample ↪ Finset M.Coordinate :=
  ⟨M.sampleOutcome, M.sampleOutcome_injective⟩

/-- The coordinates selected by one tagged outcome in block `i`. -/
def outcomeBlock (M : FixedCardinalityBlockModel I Ω)
    (outcome : Finset M.Coordinate) (i : I) : Finset ↑(M.block i) :=
  Finset.univ.filter fun x ↦ (⟨i, x⟩ : M.Coordinate) ∈ outcome

@[simp] theorem mem_outcomeBlock (M : FixedCardinalityBlockModel I Ω)
    (outcome : Finset M.Coordinate) (i : I) (x : ↑(M.block i)) :
    x ∈ M.outcomeBlock outcome i ↔
      (⟨i, x⟩ : M.Coordinate) ∈ outcome := by
  simp [outcomeBlock]

@[simp] theorem outcomeBlock_sampleOutcome
    (M : FixedCardinalityBlockModel I Ω) (S : M.Sample) (i : I) :
    M.outcomeBlock (M.sampleOutcome S) i = (S i).1 := by
  ext x
  simp

@[simp] theorem card_outcomeBlock_sampleOutcome
    (M : FixedCardinalityBlockModel I Ω) (S : M.Sample) (i : I) :
    (M.outcomeBlock (M.sampleOutcome S) i).card = M.quota i := by
  rw [outcomeBlock_sampleOutcome]
  exact (Finset.mem_powersetCard.mp (S i).2).2

/-- The simultaneous exact-cardinality conditioning event. -/
def cardinalityConditionEvent (M : FixedCardinalityBlockModel I Ω) :
    Finset (Finset M.Coordinate) :=
  Finset.univ.filter fun outcome ↦
    ∀ i, (M.outcomeBlock outcome i).card = M.quota i

@[simp] theorem mem_cardinalityConditionEvent
    (M : FixedCardinalityBlockModel I Ω)
    (outcome : Finset M.Coordinate) :
    outcome ∈ M.cardinalityConditionEvent ↔
      ∀ i, (M.outcomeBlock outcome i).card = M.quota i := by
  simp [cardinalityConditionEvent]

/-- Extract the fixed sample encoded by an outcome satisfying all quotas. -/
def sampleOfConditionedOutcome (M : FixedCardinalityBlockModel I Ω)
    (outcome : Finset M.Coordinate)
    (hquota : ∀ i, (M.outcomeBlock outcome i).card = M.quota i) : M.Sample :=
  fun i ↦ ⟨M.outcomeBlock outcome i,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hquota i⟩⟩

/-- Extracting and recombining a quota-satisfying outcome loses no
coordinates. -/
theorem sampleOutcome_sampleOfConditionedOutcome
    (M : FixedCardinalityBlockModel I Ω)
    (outcome : Finset M.Coordinate)
    (hquota : ∀ i, (M.outcomeBlock outcome i).card = M.quota i) :
    M.sampleOutcome (M.sampleOfConditionedOutcome outcome hquota) = outcome := by
  ext e
  rcases e with ⟨i, x⟩
  simp [sampleOfConditionedOutcome]

/-- The exact-cardinality condition is precisely the image of the fixed
sample space. -/
theorem cardinalityConditionEvent_eq_map_univ
    (M : FixedCardinalityBlockModel I Ω) :
    M.cardinalityConditionEvent =
      (Finset.univ : Finset M.Sample).map M.sampleOutcomeEmbedding := by
  ext outcome
  constructor
  · intro houtcome
    have hquota := (M.mem_cardinalityConditionEvent outcome).mp houtcome
    apply Finset.mem_map.mpr
    refine ⟨M.sampleOfConditionedOutcome outcome hquota, Finset.mem_univ _, ?_⟩
    exact M.sampleOutcome_sampleOfConditionedOutcome outcome hquota
  · intro houtcome
    obtain ⟨S, _hS, rfl⟩ := Finset.mem_map.mp houtcome
    exact M.mem_cardinalityConditionEvent (M.sampleOutcome S) |>.mpr
      (M.card_outcomeBlock_sampleOutcome S)

/-- The inhomogeneous Bernoulli product having success probability
`quota/card` on every coordinate of a block. -/
def associatedBernoulli (M : FixedCardinalityBlockModel I Ω) :
    FiniteBernoulliProduct M.Coordinate where
  probability e := quotaParameter (M.block e.1).card (M.quota e.1)
  probability_mem_Icc e := quotaParameter_mem_Icc (M.quota_le e.1)

@[simp] theorem associatedBernoulli_probability
    (M : FixedCardinalityBlockModel I Ω) (e : M.Coordinate) :
    M.associatedBernoulli.probability e =
      quotaParameter (M.block e.1).card (M.quota e.1) :=
  rfl

/-- Pull a tagged Bernoulli event back to the fixed sample space. -/
def sampleEvent (M : FixedCardinalityBlockModel I Ω)
    (event : Finset (Finset M.Coordinate)) : Finset M.Sample :=
  Finset.univ.filter fun S ↦ M.sampleOutcome S ∈ event

@[simp] theorem mem_sampleEvent (M : FixedCardinalityBlockModel I Ω)
    (event : Finset (Finset M.Coordinate)) (S : M.Sample) :
    S ∈ M.sampleEvent event ↔ M.sampleOutcome S ∈ event := by
  simp [sampleEvent]

/-- Fixed-cardinality probability of an event expressed on tagged
coordinates. -/
def outcomeEventProbability (M : FixedCardinalityBlockModel I Ω)
    (event : Finset (Finset M.Coordinate)) : ℝ :=
  M.eventProbability (M.sampleEvent event)

/-- The common Bernoulli weight of every outcome satisfying all block
quotas. -/
def conditionedSampleWeight (M : FixedCardinalityBlockModel I Ω) : ℝ :=
  ∏ i,
    quotaParameter (M.block i).card (M.quota i) ^ M.quota i *
      (1 - quotaParameter (M.block i).card (M.quota i)) ^
        ((M.block i).card - M.quota i)

/-- Every embedded fixed sample has the same exact Bernoulli weight. -/
theorem associatedBernoulli_outcomeWeight_sampleOutcome
    (M : FixedCardinalityBlockModel I Ω) (S : M.Sample) :
    M.associatedBernoulli.outcomeWeight (M.sampleOutcome S) =
      M.conditionedSampleWeight := by
  classical
  rw [FiniteBernoulliProduct.outcomeWeight, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _hi
  let q := quotaParameter (M.block i).card (M.quota i)
  have hcard : (S i).1.card = M.quota i :=
    (Finset.mem_powersetCard.mp (S i).2).2
  simp only [associatedBernoulli_probability, mem_sampleOutcome]
  change (∏ x : ↑(M.block i), if x ∈ (S i).1 then q else 1 - q) =
    q ^ M.quota i * (1 - q) ^ ((M.block i).card - M.quota i)
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hsuccess :
      ((Finset.univ : Finset ↑(M.block i)).filter (fun x ↦ x ∈ (S i).1)) =
        (S i).1 := by
    ext x
    simp
  have hfailure :
      ((Finset.univ : Finset ↑(M.block i)).filter (fun x ↦ x ∉ (S i).1)).card =
        (M.block i).card - M.quota i := by
    have heq :
        ((Finset.univ : Finset ↑(M.block i)).filter (fun x ↦ x ∉ (S i).1)) =
          Finset.univ \ (S i).1 := by
      ext x
      simp
    rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_coe, hcard]
  rw [hsuccess, hcard, hfailure]

/-- Mapping the fixed samples that satisfy an event gives exactly the
intersection of that event with the quota condition. -/
theorem sampleEvent_map_eq_inter_condition
    (M : FixedCardinalityBlockModel I Ω)
    (event : Finset (Finset M.Coordinate)) :
    (M.sampleEvent event).map M.sampleOutcomeEmbedding =
      event ∩ M.cardinalityConditionEvent := by
  ext outcome
  constructor
  · intro houtcome
    obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp houtcome
    exact Finset.mem_inter.mpr ⟨(M.mem_sampleEvent event S).mp hS,
      M.mem_cardinalityConditionEvent (M.sampleOutcome S) |>.mpr
        (M.card_outcomeBlock_sampleOutcome S)⟩
  · intro houtcome
    obtain ⟨hevent, hcondition⟩ := Finset.mem_inter.mp houtcome
    have hquota := (M.mem_cardinalityConditionEvent outcome).mp hcondition
    apply Finset.mem_map.mpr
    refine ⟨M.sampleOfConditionedOutcome outcome hquota, ?_,
      M.sampleOutcome_sampleOfConditionedOutcome outcome hquota⟩
    exact (M.mem_sampleEvent event _).mpr (by
      simpa [M.sampleOutcome_sampleOfConditionedOutcome outcome hquota] using hevent)

/-- Exact Bernoulli mass of the simultaneous quota condition. -/
theorem associatedBernoulli_conditionProbability_eq
    (M : FixedCardinalityBlockModel I Ω) :
    M.associatedBernoulli.eventProbability M.cardinalityConditionEvent =
      (M.sampleSpaceCard : ℝ) * M.conditionedSampleWeight := by
  classical
  rw [M.cardinalityConditionEvent_eq_map_univ]
  unfold FiniteBernoulliProduct.eventProbability
  rw [Finset.sum_map]
  change (∑ S : M.Sample,
      M.associatedBernoulli.outcomeWeight (M.sampleOutcome S)) = _
  simp_rw [M.associatedBernoulli_outcomeWeight_sampleOutcome]
  simp [M.card_sample]

/-- Exact Bernoulli mass of an event intersected with the quota condition. -/
theorem associatedBernoulli_inter_conditionProbability_eq
    (M : FixedCardinalityBlockModel I Ω)
    (event : Finset (Finset M.Coordinate)) :
    M.associatedBernoulli.eventProbability
        (event ∩ M.cardinalityConditionEvent) =
      ((M.sampleEvent event).card : ℝ) * M.conditionedSampleWeight := by
  classical
  rw [← M.sampleEvent_map_eq_inter_condition event]
  unfold FiniteBernoulliProduct.eventProbability
  rw [Finset.sum_map]
  change (∑ S ∈ M.sampleEvent event,
      M.associatedBernoulli.outcomeWeight (M.sampleOutcome S)) = _
  simp_rw [M.associatedBernoulli_outcomeWeight_sampleOutcome]
  simp

/-- Conditioning the associated Bernoulli product on every block quota gives
exactly the independent uniform fixed-cardinality block law. -/
theorem associatedBernoulli_conditioning_identity
    (M : FixedCardinalityBlockModel I Ω)
    (event : Finset (Finset M.Coordinate)) :
    M.associatedBernoulli.eventProbability
        (event ∩ M.cardinalityConditionEvent) =
      M.outcomeEventProbability event *
        M.associatedBernoulli.eventProbability M.cardinalityConditionEvent := by
  rw [M.associatedBernoulli_inter_conditionProbability_eq event,
    outcomeEventProbability, M.eventProbability_eq_card_div,
    M.associatedBernoulli_conditionProbability_eq]
  have hcard : (M.sampleSpaceCard : ℝ) ≠ 0 := by
    exact_mod_cast M.sampleSpaceCard_ne_zero
  field_simp

/-- The quota-condition probability is the product of the corresponding
binomial mode masses. -/
theorem associatedBernoulli_conditionProbability_eq_prod_binomial
    (M : FixedCardinalityBlockModel I Ω) :
    M.associatedBernoulli.eventProbability M.cardinalityConditionEvent =
      ∏ i, binomialPointMass (M.block i).card (M.quota i)
        (quotaParameter (M.block i).card (M.quota i)) := by
  rw [M.associatedBernoulli_conditionProbability_eq]
  unfold sampleSpaceCard conditionedSampleWeight binomialPointMass
  rw [Nat.cast_prod]
  calc
    (∏ i, (Nat.choose (M.block i).card (M.quota i) : ℝ)) *
        ∏ i, quotaParameter (M.block i).card (M.quota i) ^ M.quota i *
          (1 - quotaParameter (M.block i).card (M.quota i)) ^
            ((M.block i).card - M.quota i) =
      ∏ i, (Nat.choose (M.block i).card (M.quota i) : ℝ) *
        (quotaParameter (M.block i).card (M.quota i) ^ M.quota i *
          (1 - quotaParameter (M.block i).card (M.quota i)) ^
            ((M.block i).card - M.quota i)) :=
      (Finset.prod_mul_distrib).symm
    _ = ∏ i, (Nat.choose (M.block i).card (M.quota i) : ℝ) *
        quotaParameter (M.block i).card (M.quota i) ^ M.quota i *
          (1 - quotaParameter (M.block i).card (M.quota i)) ^
            ((M.block i).card - M.quota i) := by
      apply Finset.prod_congr rfl
      intro i _hi
      ring

/-- The polynomial factor lost when replacing independent fixed-count block
sampling by the associated Bernoulli product. -/
def conditioningFactor (M : FixedCardinalityBlockModel I Ω) : ℝ :=
  ∏ i, (((M.block i).card + 1 : ℕ) : ℝ)

/-- The conditioning factor is strictly positive. -/
theorem conditioningFactor_pos (M : FixedCardinalityBlockModel I Ω) :
    0 < M.conditioningFactor := by
  unfold conditioningFactor
  exact Finset.prod_pos fun i _hi ↦ by positivity

/-- The simultaneous quota event has probability at least the inverse of the
product of the elementary `(block-cardinality + 1)` factors. -/
theorem associatedBernoulli_conditionProbability_ge_inv_conditioningFactor
    (M : FixedCardinalityBlockModel I Ω) :
    M.conditioningFactor⁻¹ ≤
      M.associatedBernoulli.eventProbability M.cardinalityConditionEvent := by
  rw [M.associatedBernoulli_conditionProbability_eq_prod_binomial]
  calc
    M.conditioningFactor⁻¹ =
        ∏ i, ((((M.block i).card + 1 : ℕ) : ℝ))⁻¹ := by
      unfold conditioningFactor
      exact (Finset.prod_inv_distrib _).symm
    _ ≤ ∏ i, binomialPointMass (M.block i).card (M.quota i)
          (quotaParameter (M.block i).card (M.quota i)) := by
      exact Finset.prod_le_prod
        (fun i _hi ↦ inv_nonneg.mpr (by positivity))
        (fun i _hi ↦ by
          simpa [one_div] using
            (binomialModePointMass_ge_inv_succ (M.quota_le i)))

/-- The simultaneous quota condition has strictly positive Bernoulli
probability, including blocks with quota zero or full quota. -/
theorem associatedBernoulli_conditionProbability_pos
    (M : FixedCardinalityBlockModel I Ω) :
    0 < M.associatedBernoulli.eventProbability M.cardinalityConditionEvent := by
  exact (inv_pos.mpr M.conditioningFactor_pos).trans_le
    M.associatedBernoulli_conditionProbability_ge_inv_conditioningFactor

/-- Ratio form of the exact conditioning identity. -/
theorem outcomeEventProbability_eq_conditioned_ratio
    (M : FixedCardinalityBlockModel I Ω)
    (event : Finset (Finset M.Coordinate)) :
    M.outcomeEventProbability event =
      M.associatedBernoulli.eventProbability
          (event ∩ M.cardinalityConditionEvent) /
        M.associatedBernoulli.eventProbability M.cardinalityConditionEvent := by
  rw [M.associatedBernoulli_conditioning_identity event]
  field_simp [M.associatedBernoulli_conditionProbability_pos.ne']

/-- Fixed-count event probabilities, expressed on tagged coordinates, are
nonnegative. -/
theorem outcomeEventProbability_nonneg
    (M : FixedCardinalityBlockModel I Ω)
    (event : Finset (Finset M.Coordinate)) :
    0 ≤ M.outcomeEventProbability event :=
  M.eventProbability_nonneg (M.sampleEvent event)

/-- Exact fixed-count-versus-Bernoulli comparison.  The only loss is the
product of `(block-cardinality + 1)` supplied by the finite binomial mode
bound. -/
theorem fixedCardinality_eventProbability_le_conditioningFactor_mul
    (M : FixedCardinalityBlockModel I Ω)
    (event : Finset (Finset M.Coordinate)) :
    M.outcomeEventProbability event ≤
      M.conditioningFactor * M.associatedBernoulli.eventProbability event := by
  have hinter :
      M.associatedBernoulli.eventProbability
          (event ∩ M.cardinalityConditionEvent) ≤
        M.associatedBernoulli.eventProbability event :=
    M.associatedBernoulli.eventProbability_mono Finset.inter_subset_left
  have hlower :=
    M.associatedBernoulli_conditionProbability_ge_inv_conditioningFactor
  have hscaled :
      M.outcomeEventProbability event * M.conditioningFactor⁻¹ ≤
        M.outcomeEventProbability event *
          M.associatedBernoulli.eventProbability M.cardinalityConditionEvent :=
    mul_le_mul_of_nonneg_left hlower (M.outcomeEventProbability_nonneg event)
  have hinv :
      M.outcomeEventProbability event * M.conditioningFactor⁻¹ ≤
        M.associatedBernoulli.eventProbability event := by
    calc
      M.outcomeEventProbability event * M.conditioningFactor⁻¹ ≤
          M.outcomeEventProbability event *
            M.associatedBernoulli.eventProbability M.cardinalityConditionEvent := hscaled
      _ = M.associatedBernoulli.eventProbability
          (event ∩ M.cardinalityConditionEvent) :=
        (M.associatedBernoulli_conditioning_identity event).symm
      _ ≤ M.associatedBernoulli.eventProbability event := hinter
  have hdiv :
      M.outcomeEventProbability event / M.conditioningFactor ≤
        M.associatedBernoulli.eventProbability event := by
    simpa [div_eq_mul_inv] using hinv
  have hmul := (div_le_iff₀ M.conditioningFactor_pos).mp hdiv
  simpa [mul_comm] using hmul

/-- If every block has at most `n²` coordinates, the conditioning factor is
at most `(n²+1)^{|I|}`. -/
theorem conditioningFactor_le_nsq_pow
    (M : FixedCardinalityBlockModel I Ω) (n : ℕ)
    (hblock : ∀ i, (M.block i).card ≤ n ^ 2) :
    M.conditioningFactor ≤
      ((((n ^ 2 + 1 : ℕ) : ℝ)) ^ Fintype.card I) := by
  unfold conditioningFactor
  calc
    (∏ i, (((M.block i).card + 1 : ℕ) : ℝ)) ≤
        ∏ _i : I, (((n ^ 2 + 1 : ℕ) : ℝ)) := by
      exact Finset.prod_le_prod
        (fun _i _hi ↦ by positivity)
        (fun i _hi ↦ by exact_mod_cast Nat.add_le_add_right (hblock i) 1)
    _ = ((((n ^ 2 + 1 : ℕ) : ℝ)) ^ Fintype.card I) := by simp

/-- Paper-oriented coarse comparison when the fixed number of blocks each
contains at most `n²` coordinates. -/
theorem fixedCardinality_eventProbability_le_nsq_factor_mul
    (M : FixedCardinalityBlockModel I Ω) (n : ℕ)
    (hblock : ∀ i, (M.block i).card ≤ n ^ 2)
    (event : Finset (Finset M.Coordinate)) :
    M.outcomeEventProbability event ≤
      ((((n ^ 2 + 1 : ℕ) : ℝ)) ^ Fintype.card I) *
        M.associatedBernoulli.eventProbability event := by
  calc
    M.outcomeEventProbability event ≤
        M.conditioningFactor *
          M.associatedBernoulli.eventProbability event :=
      M.fixedCardinality_eventProbability_le_conditioningFactor_mul event
    _ ≤ ((((n ^ 2 + 1 : ℕ) : ℝ)) ^ Fintype.card I) *
          M.associatedBernoulli.eventProbability event :=
      mul_le_mul_of_nonneg_right (M.conditioningFactor_le_nsq_pow n hblock)
        (M.associatedBernoulli.eventProbability_nonneg event)

/-! ## Audit-stable public aliases -/

/-- Audit-stable name for the exact sample-space cardinality formula. -/
theorem sampleSpace_card (M : FixedCardinalityBlockModel I Ω) :
    Fintype.card M.Sample =
      ∏ i, Nat.choose (M.block i).card (M.quota i) :=
  M.card_sample

/-- Audit-stable name for the finite binomial mode lower bound. -/
theorem binomial_mode_probability_ge_inv_succ
    {N m : ℕ} (hm : m ≤ N) :
    1 / ((N + 1 : ℕ) : ℝ) ≤
      binomialPointMass N m (quotaParameter N m) :=
  binomialModePointMass_ge_inv_succ hm

end FixedCardinalityBlockModel

end DenseGraph
