import InducedStars.Graphon.Densities
import InducedStars.Graphon.LimitInputs
import InducedStars.Graphon.Metric
import InducedStars.Graphon.Step
import Mathlib.Tactic

/-!
# Elementary estimates for matrix step graphons

This file records the finite estimates used when passing between density
matrices and graphons.  They are local consequences of the equal-cell model;
no graph-limit theorem is used.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-- A uniform entrywise matrix bound is a pointwise bound for the associated
raw equal-cell kernels, including the omitted endpoint boundary. -/
theorem abs_matrixKernel_sub_le {q : ℕ}
    (M N : Matrix (Fin q) (Fin q) ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hMN : ∀ i j, |M i j - N i j| ≤ α) (z : UnitSquare) :
    |matrixKernel M z - matrixKernel N z| ≤ α := by
  classical
  by_cases hx : ∃ i : Fin q, z.1 ∈ equalCell i
  · obtain ⟨i, hi⟩ := hx
    by_cases hy : ∃ j : Fin q, z.2 ∈ equalCell j
    · obtain ⟨j, hj⟩ := hy
      rw [matrixKernel_of_mem M i j z hi hj,
        matrixKernel_of_mem N i j z hi hj]
      exact hMN i j
    · push Not at hy
      have hM : matrixKernel M z = 0 := by simp [matrixKernel, hy]
      have hN : matrixKernel N z = 0 := by simp [matrixKernel, hy]
      simp [hM, hN, hα]
  · push Not at hx
    have hM : matrixKernel M z = 0 := by simp [matrixKernel, hx]
    have hN : matrixKernel N z = 0 := by simp [matrixKernel, hx]
    simp [hM, hN, hα]

/-- Uniform entrywise control gives the same `L¹` control for matrix graphons. -/
theorem graphonL1Dist_matrixGraphon_le {q : ℕ}
    (M N : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (hN : N.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (hN₀ : ∀ i j, 0 ≤ N i j) (hN₁ : ∀ i j, N i j ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) (hMN : ∀ i j, |M i j - N i j| ≤ α) :
    graphonL1Dist (matrixGraphon M hM hM₀ hM₁)
      (matrixGraphon N hN hN₀ hN₁) ≤ α := by
  let WM := matrixGraphon M hM hM₀ hM₁
  let WN := matrixGraphon N hN hN₀ hN₁
  have hae : ∀ᵐ z ∂unitSquareMeasure,
      ‖(WM.toL1 - WN.toL1) z‖ ≤ α := by
    filter_upwards [matrixGraphon_ae_eq_kernel M hM hM₀ hM₁,
      matrixGraphon_ae_eq_kernel N hN hN₀ hN₁,
      Lp.coeFn_sub WM.toL1 WN.toL1] with z hzM hzN hzsub
    rw [hzsub]
    change ‖matrixGraphon M hM hM₀ hM₁ z -
      matrixGraphon N hN hN₀ hN₁ z‖ ≤ α
    rw [hzM, hzN, Real.norm_eq_abs]
    exact abs_matrixKernel_sub_le M N hα hMN z
  have hnorm := Lp.norm_le_of_ae_bound (p := (1 : ENNReal)) hα hae
  simpa [graphonL1Dist, dist_eq_norm, WM, WN, measureUnivNNReal,
    volume_unitSquare_univ] using hnorm

/-- Exact integral of a matrix graphon on one canonical cell rectangle. -/
theorem integral_matrixGraphon_equalCell {q : ℕ}
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (i j : Fin q) :
    ∫ z in equalCell i ×ˢ equalCell j,
        matrixGraphon M hM hM₀ hM₁ z ∂unitSquareMeasure =
      (1 / (q : ℝ)) ^ 2 * M i j := by
  let R : Set UnitSquare := equalCell i ×ˢ equalCell j
  calc
    (∫ z in R, matrixGraphon M hM hM₀ hM₁ z ∂unitSquareMeasure) =
        ∫ _z in R, M i j ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (MeasurableCut.measurable_rectangle
        ⟨equalCell i, equalCell j, measurableSet_equalCell i,
          measurableSet_equalCell j⟩),
        ae_restrict_of_ae (matrixGraphon_ae_eq_on_cell M hM hM₀ hM₁ i j)]
        with z hzR hz
      exact hz hzR
    _ = (unitSquareMeasure R).toReal * M i j := by
      rw [integral_const]
      simp [smul_eq_mul, Measure.real_def]
    _ = (1 / (q : ℝ)) ^ 2 * M i j := by
      rw [show unitSquareMeasure R = ENNReal.ofReal (1 / (q : ℝ)) ^ 2 by
        exact volume_equalCell_prod i j]
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal]
      positivity

/-- The LS normalization: an entry is `q²` times its cell integral. -/
theorem matrixGraphon_entry_eq_scaled_integral {q : ℕ}
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (i j : Fin q) :
    M i j = (q : ℝ) ^ 2 *
      ∫ z in equalCell i ×ˢ equalCell j,
        matrixGraphon M hM hM₀ hM₁ z ∂unitSquareMeasure := by
  rw [integral_matrixGraphon_equalCell]
  have hq : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
  field_simp

/-! ## Exact refinement identities -/

/-- A coarse equal cell is exactly the union of its consecutive fine cells. -/
theorem equalCell_eq_iUnion_refinement {k K : ℕ} (hK : 0 < K) (h : k ∣ K)
    (i : Fin k) :
    equalCell i =
      ⋃ a : Fin (K / k), equalCell (Graphon.refinementIndex h i a) := by
  have hk : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hle : k ≤ K := Nat.le_of_dvd hK h
  have hr : 0 < K / k := Nat.div_pos hle hk
  have hmul : k * (K / k) = K := Nat.mul_div_cancel' h
  have hmulR : (k : ℝ) * (K / k : ℕ) = (K : ℝ) := by
    exact_mod_cast hmul
  have hratio (n : ℕ) :
      (((n * (K / k) : ℕ) : ℝ) / (K : ℝ)) = (n : ℝ) / (k : ℝ) := by
    rw [Nat.cast_mul, ← hmulR]
    field_simp
  ext x
  constructor
  · intro hx
    change (i : ℝ) / k ≤ (x : ℝ) ∧
      (x : ℝ) < ((i : ℕ) + 1 : ℝ) / k at hx
    have hright : (((i : ℕ) + 1 : ℝ) / k) ≤ 1 := by
      apply (div_le_one (by exact_mod_cast hk)).2
      exact_mod_cast i.isLt
    obtain ⟨u, hu⟩ := exists_mem_equalCell hK x (hx.2.trans_le hright)
    change (u : ℝ) / K ≤ (x : ℝ) ∧
      (x : ℝ) < ((u : ℕ) + 1 : ℝ) / K at hu
    have hlo : i.1 * (K / k) ≤ u.1 := by
      by_contra hn
      have hs : u.1 + 1 ≤ i.1 * (K / k) := by omega
      have hsR : ((u.1 + 1 : ℕ) : ℝ) / (K : ℝ) ≤
          ((i.1 * (K / k) : ℕ) : ℝ) / (K : ℝ) := by
        gcongr
      rw [hratio i.1] at hsR
      have hsR' : ((u : ℝ) + 1) / (K : ℝ) ≤ (i : ℝ) / (k : ℝ) := by
        simpa using hsR
      exact (not_lt_of_ge hx.1) (hu.2.trans_le hsR')
    have hhi : u.1 < (i.1 + 1) * (K / k) := by
      by_contra hn
      have hs : (i.1 + 1) * (K / k) ≤ u.1 := by omega
      have hsR : (((i.1 + 1) * (K / k) : ℕ) : ℝ) / (K : ℝ) ≤
          (u.1 : ℝ) / (K : ℝ) := by
        gcongr
      rw [hratio (i.1 + 1)] at hsR
      have hsR' : ((i : ℝ) + 1) / (k : ℝ) ≤ (u : ℝ) / (K : ℝ) := by
        simpa using hsR
      exact (not_le_of_gt hx.2) (hsR'.trans hu.1)
    have hhi' : u.1 < i.1 * (K / k) + K / k := by
      simpa [Nat.add_mul] using hhi
    let a : Fin (K / k) := ⟨u.1 - i.1 * (K / k), by omega⟩
    have hau : Graphon.refinementIndex h i a = u := by
      apply Fin.ext
      simp only [Graphon.refinementIndex_val, a]
      omega
    exact Set.mem_iUnion.2 ⟨a, hau ▸ hu⟩
  · intro hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx
    change ((Graphon.refinementIndex h i a : Fin K) : ℝ) / K ≤ (x : ℝ) ∧
      (x : ℝ) < (((Graphon.refinementIndex h i a : Fin K) : ℕ) + 1 : ℝ) / K at ha
    change (i : ℝ) / k ≤ (x : ℝ) ∧
      (x : ℝ) < ((i : ℕ) + 1 : ℝ) / k
    constructor
    · rw [← hratio i.1]
      exact le_trans (by
        gcongr
        simp [Graphon.refinementIndex]) ha.1
    · refine ha.2.trans_le ?_
      have hi1ratio :
          ((((i.1 + 1) * (K / k) : ℕ) : ℝ) / (K : ℝ)) =
            ((i : ℝ) + 1) / (k : ℝ) := by
        simpa using hratio (i.1 + 1)
      rw [← hi1ratio]
      gcongr
      simp only [Graphon.refinementIndex_val]
      have ha : a.1 + 1 ≤ K / k := Nat.succ_le_iff.2 a.isLt
      have haR : (a.1 : ℝ) + 1 ≤ (K / k : ℕ) := by exact_mod_cast ha
      push_cast
      nlinarith

/-- Refinement indices inside one coarse block are injective. -/
theorem refinementIndex_injective {k K : ℕ} (h : k ∣ K) (i : Fin k) :
    Function.Injective (Graphon.refinementIndex h i) := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  simp only [Graphon.refinementIndex_val] at hv
  omega

/-- A coarse cell rectangle is the disjoint union of its fine cell rectangles. -/
theorem equalCell_prod_eq_iUnion_refinement {k K : ℕ} (hK : 0 < K) (h : k ∣ K)
    (i j : Fin k) :
    equalCell i ×ˢ equalCell j =
      ⋃ p : Fin (K / k) × Fin (K / k),
        equalCell (Graphon.refinementIndex h i p.1) ×ˢ
          equalCell (Graphon.refinementIndex h j p.2) := by
  rw [equalCell_eq_iUnion_refinement hK h i,
    equalCell_eq_iUnion_refinement hK h j]
  ext z
  simp only [Set.mem_prod, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), ha, hb⟩
  · rintro ⟨p, hp, hq⟩
    exact ⟨⟨p.1, hp⟩, ⟨p.2, hq⟩⟩

/-- The fine rectangles inside a fixed coarse rectangle are pairwise disjoint. -/
theorem pairwise_disjoint_refinementCell_prod {k K : ℕ} (h : k ∣ K)
    (i j : Fin k) :
    Pairwise fun p q : Fin (K / k) × Fin (K / k) ↦
      Disjoint
        (equalCell (Graphon.refinementIndex h i p.1) ×ˢ
          equalCell (Graphon.refinementIndex h j p.2))
        (equalCell (Graphon.refinementIndex h i q.1) ×ˢ
          equalCell (Graphon.refinementIndex h j q.2)) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro z hp hq
  apply hpq
  apply Prod.ext
  · apply refinementIndex_injective h i
    exact equalCell_eq_of_mem hp.1 hq.1
  · apply refinementIndex_injective h j
    exact equalCell_eq_of_mem hp.2 hq.2

/-- The integral of a fine matrix graphon over one coarse cell is the sum of
the integrals over the constituent fine cells. -/
theorem integral_matrixGraphon_refinementCell {k K : ℕ} (hK : 0 < K)
    (h : k ∣ K) (M : Matrix (Fin K) (Fin K) ℝ) (hM : M.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (i j : Fin k) :
    ∫ z in equalCell i ×ˢ equalCell j,
        matrixGraphon M hM hM₀ hM₁ z ∂unitSquareMeasure =
      (1 / (K : ℝ)) ^ 2 *
        ∑ a : Fin (K / k), ∑ b : Fin (K / k),
          M (Graphon.refinementIndex h i a) (Graphon.refinementIndex h j b) := by
  rw [equalCell_prod_eq_iUnion_refinement hK h i j]
  rw [integral_iUnion_fintype]
  · rw [Fintype.sum_prod_type]
    simp_rw [integral_matrixGraphon_equalCell]
    simp only [← Finset.mul_sum]
  · intro p
    exact (measurableSet_equalCell _).prod (measurableSet_equalCell _)
  · exact pairwise_disjoint_refinementCell_prod h i j
  · intro p
    exact (matrixGraphon M hM hM₀ hM₁).integrable.integrableOn

/-- The exact block average of a fine matrix is `k²` times the integral of
its graphon over the corresponding coarse cell. -/
theorem matrixBlockAverage_eq_scaled_integral_matrixGraphon {k K : ℕ}
    (hK : 0 < K) (h : k ∣ K) (M : Matrix (Fin K) (Fin K) ℝ)
    (hM : M.IsSymm) (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (i j : Fin k) :
    Graphon.matrixBlockAverage h M i j = (k : ℝ) ^ 2 *
      ∫ z in equalCell i ×ˢ equalCell j,
        matrixGraphon M hM hM₀ hM₁ z ∂unitSquareMeasure := by
  rw [integral_matrixGraphon_refinementCell hK h M hM hM₀ hM₁ i j]
  unfold Graphon.matrixBlockAverage
  have hk : 0 < k := Nat.pos_of_dvd_of_pos h hK
  have hr : 0 < K / k := Nat.div_pos (Nat.le_of_dvd hK h) hk
  have hmul : (k : ℝ) * (K / k : ℕ) = (K : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' h
  rw [← hmul]
  field_simp

/-- When `C` is the exact block average of `M`, each coarse entry is the
scaled integral of the fine graphon over the corresponding coarse cell. -/
theorem matrixBlockAverage_entry_eq_scaled_integral {k K : ℕ} (hK : 0 < K)
    (h : k ∣ K) (C : Matrix (Fin k) (Fin k) ℝ)
    (M : Matrix (Fin K) (Fin K) ℝ) (hM : M.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (havg : ∀ i j, C i j = Graphon.matrixBlockAverage h M i j)
    (i j : Fin k) :
    C i j = (k : ℝ) ^ 2 *
      ∫ z in equalCell i ×ˢ equalCell j,
        matrixGraphon M hM hM₀ hM₁ z ∂unitSquareMeasure := by
  rw [havg i j]
  exact matrixBlockAverage_eq_scaled_integral_matrixGraphon
    hK h M hM hM₀ hM₁ i j

/-- Exact block averaging preserves the integral on every coarse cell. -/
theorem integral_matrixGraphon_blockAverage_eq {k K : ℕ} (hK : 0 < K)
    (h : k ∣ K) (C : Matrix (Fin k) (Fin k) ℝ)
    (M : Matrix (Fin K) (Fin K) ℝ)
    (hC : C.IsSymm) (hC₀ : ∀ i j, 0 ≤ C i j) (hC₁ : ∀ i j, C i j ≤ 1)
    (hM : M.IsSymm) (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (havg : ∀ i j, C i j = Graphon.matrixBlockAverage h M i j)
    (i j : Fin k) :
    ∫ z in equalCell i ×ˢ equalCell j,
        matrixGraphon C hC hC₀ hC₁ z ∂unitSquareMeasure =
      ∫ z in equalCell i ×ˢ equalCell j,
        matrixGraphon M hM hM₀ hM₁ z ∂unitSquareMeasure := by
  rw [integral_matrixGraphon_equalCell]
  rw [matrixBlockAverage_entry_eq_scaled_integral hK h C M hM hM₀ hM₁ havg i j]
  have hk : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_dvd_of_pos h hK).ne'
  field_simp

/-- Canonical equal-cell rectangles are pairwise disjoint. -/
theorem pairwise_disjoint_equalCell_prod {q : ℕ} :
    Pairwise fun p r : Fin q × Fin q ↦
      Disjoint (equalCell p.1 ×ˢ equalCell p.2)
        (equalCell r.1 ×ˢ equalCell r.2) := by
  intro p r hpr
  rw [Set.disjoint_left]
  intro z hp hr
  apply hpr
  apply Prod.ext
  · exact equalCell_eq_of_mem hp.1 hr.1
  · exact equalCell_eq_of_mem hp.2 hr.2

/-- Except for the null endpoint lines, the canonical equal-cell rectangles
cover the unit square. -/
theorem ae_mem_iUnion_equalCell_prod {q : ℕ} (hq : 0 < q) :
    ∀ᵐ z : UnitSquare ∂unitSquareMeasure,
      z ∈ ⋃ p : Fin q × Fin q, equalCell p.1 ×ˢ equalCell p.2 := by
  have hone : ∀ᵐ x : UnitInterval ∂volume,
      ∃ i : Fin q, x ∈ equalCell i := by
    filter_upwards [Measure.ae_ne (volume : Measure UnitInterval)
      (1 : UnitInterval)] with x hx
    apply exists_mem_equalCell hq x
    apply lt_of_le_of_ne x.2.2
    intro heq
    apply hx
    exact Subtype.ext heq
  have hfst : ∀ᵐ z : UnitSquare ∂unitSquareMeasure,
      ∃ i : Fin q, z.1 ∈ equalCell i :=
    (measurePreserving_fst (μ := (volume : Measure UnitInterval))
      (ν := (volume : Measure UnitInterval))).quasiMeasurePreserving.ae hone
  have hsnd : ∀ᵐ z : UnitSquare ∂unitSquareMeasure,
      ∃ j : Fin q, z.2 ∈ equalCell j :=
    (measurePreserving_snd (μ := (volume : Measure UnitInterval))
      (ν := (volume : Measure UnitInterval))).quasiMeasurePreserving.ae hone
  filter_upwards [hfst, hsnd] with z hz₁ hz₂
  obtain ⟨i, hi⟩ := hz₁
  obtain ⟨j, hj⟩ := hz₂
  exact Set.mem_iUnion.2 ⟨(i, j), hi, hj⟩

/-- Integrating a graphon is the finite sum of its integrals over canonical
equal-cell rectangles. -/
theorem integral_graphon_eq_sum_equalCell_prod {q : ℕ} (hq : 0 < q)
    (W : Graphon) :
    ∫ z, W z ∂unitSquareMeasure =
      ∑ p : Fin q × Fin q,
        ∫ z in equalCell p.1 ×ˢ equalCell p.2, W z ∂unitSquareMeasure := by
  rw [integral_eq_setIntegral (ae_mem_iUnion_equalCell_prod hq)]
  rw [integral_iUnion_fintype]
  · intro p
    exact (measurableSet_equalCell _).prod (measurableSet_equalCell _)
  · exact pairwise_disjoint_equalCell_prod
  · intro p
    exact W.integrable.integrableOn

/-- Exact block averaging preserves the total integral of the matrix
graphon. -/
theorem integral_matrixGraphon_blockAverage_eq_total {k K : ℕ} (hK : 0 < K)
    (h : k ∣ K) (C : Matrix (Fin k) (Fin k) ℝ)
    (M : Matrix (Fin K) (Fin K) ℝ)
    (hC : C.IsSymm) (hC₀ : ∀ i j, 0 ≤ C i j) (hC₁ : ∀ i j, C i j ≤ 1)
    (hM : M.IsSymm) (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (havg : ∀ i j, C i j = Graphon.matrixBlockAverage h M i j) :
    ∫ z, matrixGraphon C hC hC₀ hC₁ z ∂unitSquareMeasure =
      ∫ z, matrixGraphon M hM hM₀ hM₁ z ∂unitSquareMeasure := by
  have hk : 0 < k := Nat.pos_of_dvd_of_pos h hK
  rw [integral_graphon_eq_sum_equalCell_prod hk,
    integral_graphon_eq_sum_equalCell_prod hk]
  apply Fintype.sum_congr
  intro p
  exact integral_matrixGraphon_blockAverage_eq hK h C M hC hC₀ hC₁
    hM hM₀ hM₁ havg p.1 p.2

/-- Uniformly replicating every coarse entry across its fine refinement block
does not change the represented graphon. -/
theorem matrixGraphon_uniformRefinement_eq {k K : ℕ} (hK : 0 < K)
    (h : k ∣ K) (C : Matrix (Fin k) (Fin k) ℝ)
    (M : Matrix (Fin K) (Fin K) ℝ)
    (hC : C.IsSymm) (hC₀ : ∀ i j, 0 ≤ C i j) (hC₁ : ∀ i j, C i j ≤ 1)
    (hM : M.IsSymm) (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (hrep : ∀ i j a b,
      M (Graphon.refinementIndex h i a) (Graphon.refinementIndex h j b) = C i j) :
    matrixGraphon M hM hM₀ hM₁ = matrixGraphon C hC hC₀ hC₁ := by
  apply Graphon.ext
  have hk : 0 < k := Nat.pos_of_dvd_of_pos h hK
  filter_upwards [matrixGraphon_ae_eq_kernel M hM hM₀ hM₁,
    matrixGraphon_ae_eq_kernel C hC hC₀ hC₁,
    ae_mem_iUnion_equalCell_prod hk] with z hzM hzC hzcell
  obtain ⟨p, hp₁, hp₂⟩ := Set.mem_iUnion.1 hzcell
  have hp₁' := hp₁
  have hp₂' := hp₂
  rw [equalCell_eq_iUnion_refinement hK h p.1] at hp₁'
  rw [equalCell_eq_iUnion_refinement hK h p.2] at hp₂'
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hp₁'
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hp₂'
  rw [hzM, hzC,
    matrixKernel_of_mem M (Graphon.refinementIndex h p.1 a)
      (Graphon.refinementIndex h p.2 b) z ha hb,
    matrixKernel_of_mem C p.1 p.2 z hp₁ hp₂]
  exact hrep p.1 p.2 a b

end InducedStars
