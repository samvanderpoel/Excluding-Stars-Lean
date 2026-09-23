import InducedStars.Graphon.CandidateBlocks
import InducedStars.Graphon.ColorProfile
import InducedStars.Graphon.ValueRegions
import Mathlib.Tactic

/-!
# Profile-valued finite and countable block graphons

This file generalizes the finite core graphon `xiGraphon` and the block-sequence
graphon `WLambda` from the distinguished value `pK k` to an arbitrary profile
value `p ∈ [0,1]`.  The countable construction reuses the already verified
block geometry and measurability development in `CandidateBlocks`: it changes
only the middle palette value of the raw kernel.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal unitInterval

namespace InducedStars

attribute [local instance] profileFiniteCoreAdjDecidable

/-! ## Generic identities for a separated three-value palette -/

private theorem value_eq_profile_of_mem_randomRegion
    {W : Graphon} {p : ℝ}
    {z : UnitSquare}
    (hthree : W.value z = 0 ∨ W.value z = p ∨ W.value z = 1)
    (hz : z ∈ graphonRandomRegion W) :
    W.value z = p := by
  rcases hthree with hzero | hpval | hone
  · exact (not_lt_of_ge (le_of_eq hzero)) hz.1 |>.elim
  · exact hpval
  · exact (ne_of_lt hz.2 hone).elim

/-- Edge density of an a.e. `{0,p,1}`-valued graphon. -/
theorem graphonEdgeDensity_eq_oneMass_add_profile_mul_randomMass
    {W : Graphon} {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hthree : ∀ᵐ z ∂unitSquareMeasure,
      W.value z = 0 ∨ W.value z = p ∨ W.value z = 1) :
    graphonEdgeDensity W =
      graphonOneMass W + p * graphonRandomMass W := by
  have hRandomIntegral :
      (∫ z in graphonRandomRegion W, W.value z ∂unitSquareMeasure) =
        p * graphonRandomMass W := by
    calc
      (∫ z in graphonRandomRegion W, W.value z ∂unitSquareMeasure) =
          ∫ _z in graphonRandomRegion W, p ∂unitSquareMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hthree,
          ae_restrict_mem (measurableSet_graphonRandomRegion W)] with z hzThree hzMem
        exact value_eq_profile_of_mem_randomRegion hzThree hzMem
      _ = p * graphonRandomMass W := by
        simp [graphonRandomMass, smul_eq_mul, mul_comm]
  rw [graphonEdgeDensity_eq_oneMass_add_randomMass_mul_randomMean]
  have hMean : graphonRandomMass W * graphonRandomMean W =
      p * graphonRandomMass W := by
    rw [← setIntegral_value_randomRegion_eq_randomMass_mul_randomMean]
    exact hRandomIntegral
  rw [hMean]

/-- Entropy of an a.e. `{0,p,1}`-valued graphon. -/
theorem graphonEntropy_eq_binaryEntropy_mul_randomMass_of_threeValued
    {W : Graphon} {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hthree : ∀ᵐ z ∂unitSquareMeasure,
      W.value z = 0 ∨ W.value z = p ∨ W.value z = 1) :
    graphonEntropy W =
      binaryEntropy p * graphonRandomMass W := by
  rw [graphonEntropy_eq_setIntegral_randomRegion]
  calc
    (∫ z in graphonRandomRegion W, binaryEntropy (W.value z)
        ∂unitSquareMeasure) =
        ∫ _z in graphonRandomRegion W, binaryEntropy p
          ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hthree,
        ae_restrict_mem (measurableSet_graphonRandomRegion W)] with z hzThree hzMem
      rw [value_eq_profile_of_mem_randomRegion hzThree hzMem]
    _ = binaryEntropy p * graphonRandomMass W := by
      simp [graphonRandomMass, smul_eq_mul, mul_comm]

/-! ## Arbitrary-profile finite cores -/

/-- The equal-cell graphon of a finite regular core with arbitrary middle
profile value. -/
def profileXiGraphon {k : ℕ} (p : ℝ) (C : RegularBlockCore k)
    (hp : p ∈ Icc (0 : ℝ) 1) : Graphon :=
  matrixGraphon (profileXiMatrix p C) (profileXiMatrix_isSymm p C)
    (profileXiMatrix_nonneg hp.1 C) (profileXiMatrix_le_one hp.2 C)

/-- Exact core-matrix value on a canonical graphon cell. -/
theorem profileXiGraphon_ae_eq_on_cell {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (hp : p ∈ Icc (0 : ℝ) 1)
    (i j : Fin C.order) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      profileXiGraphon p C hp z = profileXiMatrix p C i j := by
  simpa only [profileXiGraphon] using
    matrixGraphon_ae_eq_on_cell (profileXiMatrix p C)
      (profileXiMatrix_isSymm p C) (profileXiMatrix_nonneg hp.1 C)
      (profileXiMatrix_le_one hp.2 C) i j

theorem profileXiGraphon_ae_eq_one_on_diagonal_cell {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (hp : p ∈ Icc (0 : ℝ) 1)
    (i : Fin C.order) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell i →
      profileXiGraphon p C hp z = 1 := by
  filter_upwards [profileXiGraphon_ae_eq_on_cell p C hp i i] with z hz hmem
  simpa using hz hmem

theorem profileXiGraphon_ae_eq_profile_on_edge_cell {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (hp : p ∈ Icc (0 : ℝ) 1)
    {i j : Fin C.order} (hij : C.graph.Adj i j) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      profileXiGraphon p C hp z = p := by
  filter_upwards [profileXiGraphon_ae_eq_on_cell p C hp i j] with z hz hmem
  rw [hz hmem, profileXiMatrix_apply_of_adj p C hij]

theorem profileXiGraphon_ae_eq_zero_on_nonedge_cell {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (hp : p ∈ Icc (0 : ℝ) 1)
    {i j : Fin C.order} (hne : i ≠ j) (hij : ¬ C.graph.Adj i j) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      profileXiGraphon p C hp z = 0 := by
  filter_upwards [profileXiGraphon_ae_eq_on_cell p C hp i j] with z hz hmem
  rw [hz hmem, profileXiMatrix_apply_of_ne_of_not_adj p C hne hij]

/-- The arbitrary-profile matrix specializes definitionally to `xiMatrix`. -/
@[simp] theorem profileXiMatrix_pK {k : ℕ} (C : RegularBlockCore k) :
    profileXiMatrix (pK k) C = xiMatrix C :=
  rfl

/-- At `pK k`, the arbitrary-profile core graphon is exactly `xiGraphon`. -/
@[simp] theorem profileXiGraphon_pK {k : ℕ} (hk : 3 ≤ k)
    (C : RegularBlockCore k) :
    profileXiGraphon (pK k) C
        ⟨(pK_pos (by omega : 2 ≤ k)).le,
          (pK_lt_one (by omega : 2 ≤ k)).le⟩ =
      xiGraphon hk C :=
  rfl

/-- Compatibility spelling for the `pK` specialization. -/
theorem profileXiGraphon_eq_xiGraphon {k : ℕ} (hk : 3 ≤ k)
    (C : RegularBlockCore k) :
    profileXiGraphon (pK k) C
        ⟨(pK_pos (by omega : 2 ≤ k)).le,
          (pK_lt_one (by omega : 2 ≤ k)).le⟩ =
      xiGraphon hk C :=
  profileXiGraphon_pK hk C

/-- Exact edge density of an arbitrary-profile finite core. -/
theorem graphonEdgeDensity_profileXiGraphon {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonEdgeDensity (profileXiGraphon p C hp) =
      (1 + ((k - 2 : ℕ) : ℝ) * p) / C.order := by
  rw [profileXiGraphon, graphonEdgeDensity_matrixGraphon C.order_pos,
    sum_profileXiMatrix]
  have horder : (C.order : ℝ) ≠ 0 := by exact_mod_cast C.order_pos.ne'
  field_simp

/-- Exact entropy of an arbitrary-profile finite core. -/
theorem graphonEntropy_profileXiGraphon {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonEntropy (profileXiGraphon p C hp) =
      ((k - 2 : ℕ) : ℝ) * binaryEntropy p / C.order := by
  rw [profileXiGraphon, graphonEntropy_matrixGraphon C.order_pos,
    sum_binaryEntropy_profileXiMatrix]
  have horder : (C.order : ℝ) ≠ 0 := by exact_mod_cast C.order_pos.ne'
  field_simp

/-- An arbitrary-profile finite core is a.e. `{0,p,1}`-valued. -/
theorem profileXiGraphon_ae_threeValued {k : ℕ} (p : ℝ)
    (C : RegularBlockCore k) (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      (profileXiGraphon p C hp).value z = 0 ∨
        (profileXiGraphon p C hp).value z = p ∨
          (profileXiGraphon p C hp).value z = 1 := by
  let W := profileXiGraphon p C hp
  filter_upwards [ae_mem_iUnion_equalCell_prod C.order_pos, W.value_ae_eq,
    matrixGraphon_ae_eq_kernel (profileXiMatrix p C)
      (profileXiMatrix_isSymm p C) (profileXiMatrix_nonneg hp.1 C)
      (profileXiMatrix_le_one hp.2 C)] with z hzCover hzValue hzKernel
  obtain ⟨ij, hzij⟩ := Set.mem_iUnion.mp hzCover
  have hW : W.value z = profileXiMatrix p C ij.1 ij.2 := by
    rw [hzValue]
    have hKernel : (W : UnitSquare → ℝ) z =
        matrixKernel (profileXiMatrix p C) z := by
      simpa only [W, profileXiGraphon] using hzKernel
    rw [hKernel,
      matrixKernel_of_mem (profileXiMatrix p C) ij.1 ij.2 z hzij.1 hzij.2]
  rw [hW]
  by_cases hij : ij.1 = ij.2
  · exact Or.inr (Or.inr (by simp [profileXiMatrix, hij]))
  · by_cases hadj : C.graph.Adj ij.1 ij.2
    · exact Or.inr (Or.inl (profileXiMatrix_apply_of_adj p C hadj))
    · exact Or.inl (profileXiMatrix_apply_of_ne_of_not_adj p C hij hadj)

/-- Exact one-valued mass of an arbitrary-profile finite core. -/
theorem graphonOneMass_profileXiGraphon {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (C : RegularBlockCore k) :
    graphonOneMass
        (profileXiGraphon p C ⟨hp.1.le, hp.2.le⟩) =
      1 / C.order := by
  let hpIcc : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  let W := profileXiGraphon p C hpIcc
  have hRandom : graphonRandomMass W =
      ((k - 2 : ℕ) : ℝ) / C.order := by
    have hEntropy := graphonEntropy_eq_binaryEntropy_mul_randomMass_of_threeValued
      hp (profileXiGraphon_ae_threeValued p C hpIcc)
    have hH : binaryEntropy p ≠ 0 := (binaryEntropy_pos hp.1 hp.2).ne'
    apply (mul_left_cancel₀ hH)
    calc
      binaryEntropy p * graphonRandomMass W = graphonEntropy W := hEntropy.symm
      _ = ((k - 2 : ℕ) : ℝ) * binaryEntropy p / C.order :=
        graphonEntropy_profileXiGraphon p C hpIcc
      _ = binaryEntropy p * (((k - 2 : ℕ) : ℝ) / C.order) := by ring
  have hEdge := graphonEdgeDensity_eq_oneMass_add_profile_mul_randomMass
    hp (profileXiGraphon_ae_threeValued p C hpIcc)
  calc
    graphonOneMass W = graphonEdgeDensity W - p * graphonRandomMass W := by
      linarith
    _ = (1 + ((k - 2 : ℕ) : ℝ) * p) / C.order -
        p * (((k - 2 : ℕ) : ℝ) / C.order) := by
      rw [graphonEdgeDensity_profileXiGraphon p C hpIcc, hRandom]
    _ = 1 / C.order := by ring

/-- Exact random-valued mass of an arbitrary-profile finite core. -/
theorem graphonRandomMass_profileXiGraphon {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (C : RegularBlockCore k) :
    graphonRandomMass
        (profileXiGraphon p C ⟨hp.1.le, hp.2.le⟩) =
      ((k - 2 : ℕ) : ℝ) / C.order := by
  let hpIcc : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  let W := profileXiGraphon p C hpIcc
  have hEntropy := graphonEntropy_eq_binaryEntropy_mul_randomMass_of_threeValued
    hp (profileXiGraphon_ae_threeValued p C hpIcc)
  have hH : binaryEntropy p ≠ 0 := (binaryEntropy_pos hp.1 hp.2).ne'
  apply (mul_left_cancel₀ hH)
  calc
    binaryEntropy p * graphonRandomMass W = graphonEntropy W := hEntropy.symm
    _ = ((k - 2 : ℕ) : ℝ) * binaryEntropy p / C.order :=
      graphonEntropy_profileXiGraphon p C hpIcc
    _ = binaryEntropy p * (((k - 2 : ℕ) : ℝ) / C.order) := by ring

/-- Exact nonzero-region mass of an arbitrary-profile finite core. -/
theorem graphonNonzeroMass_profileXiGraphon {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (C : RegularBlockCore k) :
    graphonNonzeroMass
        (profileXiGraphon p C ⟨hp.1.le, hp.2.le⟩) =
      ((k - 1 : ℕ) : ℝ) / C.order := by
  rw [graphonNonzeroMass_eq_oneMass_add_randomMass,
    graphonOneMass_profileXiGraphon hk hp C,
    graphonRandomMass_profileXiGraphon hk hp C]
  norm_num [Nat.cast_sub (show 1 ≤ k by omega),
    Nat.cast_sub (show 2 ≤ k by omega)]
  ring

/-! ## Palette recoloring of an admissible block sequence -/

/-- Replace the unique middle value of a three-valued kernel by `p`, while
fixing zero and one. -/
def profileRecolor (p t : ℝ) : ℝ :=
  if t = 0 then 0 else if t = 1 then 1 else p

@[simp] theorem profileRecolor_zero (p : ℝ) : profileRecolor p 0 = 0 := by
  simp [profileRecolor]

@[simp] theorem profileRecolor_one (p : ℝ) : profileRecolor p 1 = 1 := by
  simp [profileRecolor]

theorem profileRecolor_of_ne_zero_one {p t : ℝ} (hzero : t ≠ 0)
    (hone : t ≠ 1) : profileRecolor p t = p := by
  simp [profileRecolor, hzero, hone]

theorem profileRecolor_mem_Icc {p t : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    profileRecolor p t ∈ Icc (0 : ℝ) 1 := by
  unfold profileRecolor
  split_ifs <;> simp_all

theorem profileRecolor_eq_zero_or_profile_or_one (p t : ℝ) :
    profileRecolor p t = 0 ∨ profileRecolor p t = p ∨
      profileRecolor p t = 1 := by
  unfold profileRecolor
  split_ifs <;> simp_all

@[fun_prop] theorem measurable_profileRecolor (p : ℝ) :
    Measurable (profileRecolor p) := by
  unfold profileRecolor
  apply Measurable.ite
  · exact measurableSet_singleton 0
  · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_singleton 1
    · exact measurable_const
    · exact measurable_const

namespace AdmissibleBlockSequence

variable {k : ℕ} (L : AdmissibleBlockSequence k)

/-- The raw arbitrary-profile block kernel, obtained by changing only the
middle palette value of the existing block kernel. -/
def profileKernel (p : ℝ) (z : UnitSquare) : ℝ :=
  profileRecolor p (L.kernel z)

@[fun_prop] theorem measurable_profileKernel (p : ℝ) :
    Measurable (L.profileKernel p) :=
  (measurable_profileRecolor p).comp L.measurable_kernel

theorem profileKernel_mem_Icc {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (z : UnitSquare) : L.profileKernel p z ∈ Icc (0 : ℝ) 1 :=
  profileRecolor_mem_Icc hp

theorem integrable_profileKernel {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    Integrable (L.profileKernel p) unitSquareMeasure := by
  apply Integrable.of_bound (L.measurable_profileKernel p).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (L.profileKernel_mem_Icc hp z).1]
  exact (L.profileKernel_mem_Icc hp z).2

theorem profileKernel_symm (p : ℝ) (z : UnitSquare) :
    L.profileKernel p (z.2, z.1) = L.profileKernel p z := by
  rw [profileKernel, profileKernel, L.kernel_symm]

/-- Every raw block-kernel value belongs to `{0,pK k,1}`. -/
theorem kernel_eq_zero_or_pK_or_one (z : UnitSquare) :
    L.kernel z = 0 ∨ L.kernel z = pK k ∨ L.kernel z = 1 := by
  classical
  by_cases hblock : ∃ i, z.1 ∈ L.blockInterval i
  · obtain ⟨i, hi⟩ := hblock
    rw [L.kernel_eq_blockKernel_of_mem i z hi]
    by_cases hx : ∃ v : Fin (L.core i).order, z.1 ∈ L.blockCell i v
    · obtain ⟨v, hv⟩ := hx
      by_cases hy : ∃ w : Fin (L.core i).order, z.2 ∈ L.blockCell i w
      · obtain ⟨w, hw⟩ := hy
        rw [L.blockKernel_of_mem i v w z hv hw]
        by_cases hvw : v = w
        · subst w
          exact Or.inr (Or.inr (xiMatrix_apply_eq (L.core i) v))
        · by_cases hadj : (L.core i).graph.Adj v w
          · exact Or.inr (Or.inl (xiMatrix_apply_of_adj (L.core i) hadj))
          · exact Or.inl
              (xiMatrix_apply_of_ne_of_not_adj (L.core i) hvw hadj)
      · left
        rw [L.blockKernel_eq_zero_of_no_rightCell]
        simpa only [not_exists] using hy
    · left
      rw [L.blockKernel_eq_zero_of_no_leftCell]
      simpa only [not_exists] using hx
  · left
    rw [L.kernel_eq_zero_of_no_block]
    simpa only [not_exists] using hblock

theorem profileRecolor_pK_kernel (hk : 3 ≤ k) (z : UnitSquare) :
    profileRecolor (pK k) (L.kernel z) = L.kernel z := by
  rcases L.kernel_eq_zero_or_pK_or_one z with hzero | hmiddle | hone
  · simp [hzero]
  · rw [hmiddle]
    exact profileRecolor_of_ne_zero_one
      (pK_pos (by omega : 2 ≤ k)).ne'
      (ne_of_lt (pK_lt_one (by omega : 2 ≤ k)))
  · simp [hone]

theorem profileRecolor_xiMatrix (hk : 3 ≤ k) (p : ℝ) (i : ℕ)
    (v w : Fin (L.core i).order) :
    profileRecolor p (xiMatrix (L.core i) v w) =
      profileXiMatrix p (L.core i) v w := by
  classical
  by_cases hvw : v = w
  · subst w
    rw [xiMatrix_apply_eq, profileXiMatrix_apply_eq]
    simp
  · by_cases hadj : (L.core i).graph.Adj v w
    · rw [xiMatrix_apply_of_adj (L.core i) hadj,
        profileXiMatrix_apply_of_adj p (L.core i) hadj]
      exact profileRecolor_of_ne_zero_one
        (pK_pos (by omega : 2 ≤ k)).ne'
        (ne_of_lt (pK_lt_one (by omega : 2 ≤ k)))
    · rw [xiMatrix_apply_of_ne_of_not_adj (L.core i) hvw hadj,
        profileXiMatrix_apply_of_ne_of_not_adj p (L.core i) hvw hadj]
      simp

/-- Exact value of the arbitrary-profile raw kernel on a canonical block
cell. -/
theorem profileKernel_of_mem (hk : 3 ≤ k) (p : ℝ) (i : ℕ)
    (v w : Fin (L.core i).order) (z : UnitSquare)
    (hzv : z.1 ∈ L.blockCell i v) (hzw : z.2 ∈ L.blockCell i w) :
    L.profileKernel p z = profileXiMatrix p (L.core i) v w := by
  rw [profileKernel,
    L.kernel_eq_blockKernel_of_mem i z (L.blockCell_subset_interval i v hzv),
    L.blockKernel_of_mem i v w z hzv hzw,
    L.profileRecolor_xiMatrix hk p i v w]

theorem profileKernel_eq_zero_of_not_mem (p : ℝ) (i : ℕ)
    (z : UnitSquare)
    (hz : z.1 ∉ L.blockInterval i ∨ z.2 ∉ L.blockInterval i)
    (hi : z.1 ∈ L.blockInterval i) :
    L.profileKernel p z = 0 := by
  rw [profileKernel, L.kernel_eq_blockKernel_of_mem i z hi,
    L.blockKernel_eq_zero_of_not_mem i z hz]
  simp

theorem profileKernel_eq_zero_of_no_block (p : ℝ) (z : UnitSquare)
    (hz : ∀ i, z.1 ∉ L.blockInterval i) :
    L.profileKernel p z = 0 := by
  rw [profileKernel, L.kernel_eq_zero_of_no_block z hz]
  simp

/-- Distinct block intervals remain zero-connected after profile recoloring. -/
theorem profileKernel_eq_zero_of_mem_distinct_blocks (p : ℝ)
    {i j : ℕ} (hij : i ≠ j) (z : UnitSquare)
    (hi : z.1 ∈ L.blockInterval i) (hj : z.2 ∈ L.blockInterval j) :
    L.profileKernel p z = 0 := by
  rw [profileKernel, L.kernel_eq_blockKernel_of_mem i z hi,
    L.blockKernel_eq_zero_of_not_mem]
  · simp
  · right
    intro hji
    exact Set.disjoint_left.1 (L.pairwise_disjoint_blockInterval hij) hji hj

end AdmissibleBlockSequence

/-- The arbitrary-profile graphon of a finite or infinite admissible block
sequence. -/
def profileWLambda {k : ℕ} (p : ℝ) (L : AdmissibleBlockSequence k)
    (hp : p ∈ Icc (0 : ℝ) 1) : Graphon :=
  Graphon.ofFun (L.profileKernel p) (L.integrable_profileKernel hp)
    (ae_of_all _ fun z ↦ (L.profileKernel_mem_Icc hp z).1)
    (ae_of_all _ fun z ↦ (L.profileKernel_mem_Icc hp z).2)
    (L.profileKernel_symm p)

theorem profileWLambda_ae_eq_profileKernel {k : ℕ} (p : ℝ)
    (L : AdmissibleBlockSequence k) (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      profileWLambda p L hp z = L.profileKernel p z :=
  Graphon.coe_ofFun _ _ _ _ _

/-- Canonical graphon values agree a.e. with the arbitrary-profile raw
kernel. -/
theorem profileWLambda_value_ae_eq_profileKernel {k : ℕ} (p : ℝ)
    (L : AdmissibleBlockSequence k) (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      (profileWLambda p L hp).value z = L.profileKernel p z := by
  filter_upwards [(profileWLambda p L hp).value_ae_eq,
    profileWLambda_ae_eq_profileKernel p L hp] with z hzValue hzKernel
  exact hzValue.trans hzKernel

/-- Exact canonical value on a pair of vertex cells inside one block. -/
theorem profileWLambda_ae_eq_on_blockCell {k : ℕ} (hk : 3 ≤ k)
    (p : ℝ) (L : AdmissibleBlockSequence k)
    (hp : p ∈ Icc (0 : ℝ) 1) (i : ℕ)
    (v w : Fin (L.core i).order) :
    ∀ᵐ z ∂unitSquareMeasure,
      z.1 ∈ L.blockCell i v → z.2 ∈ L.blockCell i w →
        (profileWLambda p L hp).value z =
          profileXiMatrix p (L.core i) v w := by
  filter_upwards [profileWLambda_value_ae_eq_profileKernel p L hp] with z hz hzv hzw
  rw [hz, L.profileKernel_of_mem hk p i v w z hzv hzw]

/-- An arbitrary-profile block graphon is a.e. `{0,p,1}`-valued. -/
theorem profileWLambda_ae_threeValued {k : ℕ} (p : ℝ)
    (L : AdmissibleBlockSequence k) (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      (profileWLambda p L hp).value z = 0 ∨
        (profileWLambda p L hp).value z = p ∨
          (profileWLambda p L hp).value z = 1 := by
  filter_upwards [profileWLambda_value_ae_eq_profileKernel p L hp] with z hz
  rw [hz]
  exact profileRecolor_eq_zero_or_profile_or_one p (L.kernel z)

/-- At the distinguished value `pK k`, profile block graphons are literally
the existing `WLambda` graphons. -/
@[simp] theorem profileWLambda_pK {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    profileWLambda (pK k) L
        ⟨(pK_pos (by omega : 2 ≤ k)).le,
          (pK_lt_one (by omega : 2 ≤ k)).le⟩ =
      WLambda hk L := by
  change profileWLambda (pK k) L _ = L.graphon hk
  apply Graphon.ext
  filter_upwards [profileWLambda_ae_eq_profileKernel (pK k) L
      ⟨(pK_pos (by omega : 2 ≤ k)).le,
        (pK_lt_one (by omega : 2 ≤ k)).le⟩,
    L.graphon_ae_eq_kernel hk] with z hzProfile hzBase
  rw [hzProfile, hzBase]
  exact L.profileRecolor_pK_kernel hk z

/-- Compatibility spelling for the `pK` specialization. -/
theorem profileWLambda_eq_WLambda {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    profileWLambda (pK k) L
        ⟨(pK_pos (by omega : 2 ≤ k)).le,
          (pK_lt_one (by omega : 2 ≤ k)).le⟩ =
      WLambda hk L :=
  profileWLambda_pK hk L

/-! ### Exact value masses and functionals -/

/-- Canonical values of `WLambda` agree a.e. with its raw block kernel. -/
theorem WLambda_value_ae_eq_kernel {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    ∀ᵐ z ∂unitSquareMeasure, (WLambda hk L).value z = L.kernel z := by
  filter_upwards [(WLambda hk L).value_ae_eq,
    L.graphon_ae_eq_kernel hk] with z hzValue hzKernel
  exact hzValue.trans (by simpa only [WLambda] using hzKernel)

/-- The original `WLambda` graphon has palette `{0,pK k,1}`. -/
theorem WLambda_ae_threeValued {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    ∀ᵐ z ∂unitSquareMeasure,
      (WLambda hk L).value z = 0 ∨
        (WLambda hk L).value z = pK k ∨
          (WLambda hk L).value z = 1 := by
  filter_upwards [WLambda_value_ae_eq_kernel hk L] with z hz
  rw [hz]
  exact L.kernel_eq_zero_or_pK_or_one z

/-- Replacing the middle palette value does not change the one-valued
region, up to the canonical null-set choices of graphon representatives. -/
theorem graphonOneRegion_profileWLambda_ae_eq_WLambda {k : ℕ}
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) :
    graphonOneRegion
        (profileWLambda p L ⟨hp.1.le, hp.2.le⟩) =ᵐ[unitSquareMeasure]
      graphonOneRegion (WLambda hk L) := by
  filter_upwards [profileWLambda_value_ae_eq_profileKernel p L
      ⟨hp.1.le, hp.2.le⟩,
    WLambda_value_ae_eq_kernel hk L] with z hzProfile hzBase
  change ((profileWLambda p L ⟨hp.1.le, hp.2.le⟩).value z = 1) =
    ((WLambda hk L).value z = 1)
  rw [hzProfile, hzBase]
  apply propext
  rcases L.kernel_eq_zero_or_pK_or_one z with hzero | hmiddle | hone
  · simp [AdmissibleBlockSequence.profileKernel, hzero]
  · have hpk0 : pK k ≠ 0 := (pK_pos (by omega : 2 ≤ k)).ne'
    have hpk1 : pK k ≠ 1 := ne_of_lt (pK_lt_one (by omega : 2 ≤ k))
    simp [AdmissibleBlockSequence.profileKernel, hmiddle, profileRecolor,
      hpk0, hpk1, ne_of_lt hp.2]
  · simp [AdmissibleBlockSequence.profileKernel, hone]

/-- Replacing the middle palette value does not change the random-valued
region, up to null sets. -/
theorem graphonRandomRegion_profileWLambda_ae_eq_WLambda {k : ℕ}
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) :
    graphonRandomRegion
        (profileWLambda p L ⟨hp.1.le, hp.2.le⟩) =ᵐ[unitSquareMeasure]
      graphonRandomRegion (WLambda hk L) := by
  filter_upwards [profileWLambda_value_ae_eq_profileKernel p L
      ⟨hp.1.le, hp.2.le⟩,
    WLambda_value_ae_eq_kernel hk L] with z hzProfile hzBase
  change
    (0 < (profileWLambda p L ⟨hp.1.le, hp.2.le⟩).value z ∧
        (profileWLambda p L ⟨hp.1.le, hp.2.le⟩).value z < 1) =
      (0 < (WLambda hk L).value z ∧ (WLambda hk L).value z < 1)
  rw [hzProfile, hzBase]
  apply propext
  rcases L.kernel_eq_zero_or_pK_or_one z with hzero | hmiddle | hone
  · simp [AdmissibleBlockSequence.profileKernel, hzero]
  · have hpk0 : 0 < pK k := pK_pos (by omega : 2 ≤ k)
    have hpk1 : pK k < 1 := pK_lt_one (by omega : 2 ≤ k)
    simp [AdmissibleBlockSequence.profileKernel, hmiddle, profileRecolor,
      hpk0.ne', ne_of_lt hpk1, hp.1, hp.2, hpk0, hpk1]
  · simp [AdmissibleBlockSequence.profileKernel, hone]

/-- Exact random-valued mass of the original block-sequence graphon. -/
theorem graphonRandomMass_WLambda {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    graphonRandomMass (WLambda hk L) =
      ((k - 2 : ℕ) : ℝ) * L.mass := by
  let hpK : pK k ∈ Ioo (0 : ℝ) 1 :=
    ⟨pK_pos (by omega : 2 ≤ k), pK_lt_one (by omega : 2 ≤ k)⟩
  have hEntropy := graphonEntropy_eq_binaryEntropy_mul_randomMass_of_threeValued
    hpK (WLambda_ae_threeValued hk L)
  have hH : binaryEntropy (pK k) ≠ 0 :=
    (binaryEntropy_pos hpK.1 hpK.2).ne'
  apply mul_left_cancel₀ hH
  calc
    binaryEntropy (pK k) * graphonRandomMass (WLambda hk L) =
        graphonEntropy (WLambda hk L) := hEntropy.symm
    _ = (((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k)) * L.mass := by
      simpa only [WLambda] using L.graphon_entropy hk
    _ = binaryEntropy (pK k) * (((k - 2 : ℕ) : ℝ) * L.mass) := by
      ring

/-- Exact one-valued mass of the original block-sequence graphon. -/
theorem graphonOneMass_WLambda {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) :
    graphonOneMass (WLambda hk L) = L.mass := by
  let hpK : pK k ∈ Ioo (0 : ℝ) 1 :=
    ⟨pK_pos (by omega : 2 ≤ k), pK_lt_one (by omega : 2 ≤ k)⟩
  have hEdge := graphonEdgeDensity_eq_oneMass_add_profile_mul_randomMass
    hpK (WLambda_ae_threeValued hk L)
  calc
    graphonOneMass (WLambda hk L) =
        graphonEdgeDensity (WLambda hk L) -
          pK k * graphonRandomMass (WLambda hk L) := by
      linarith
    _ = (1 + ((k - 2 : ℕ) : ℝ) * pK k) * L.mass -
        pK k * (((k - 2 : ℕ) : ℝ) * L.mass) := by
      rw [graphonRandomMass_WLambda hk L]
      congr 1
      simpa only [WLambda] using L.graphon_edgeDensity hk
    _ = L.mass := by ring

/-- Exact one-valued mass of an arbitrary-profile finite or infinite block
sequence. -/
theorem graphonOneMass_profileWLambda {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) :
    graphonOneMass (profileWLambda p L ⟨hp.1.le, hp.2.le⟩) =
      L.mass := by
  unfold graphonOneMass
  rw [Measure.real, measure_congr
    (graphonOneRegion_profileWLambda_ae_eq_WLambda hk hp L),
    ← Measure.real]
  exact graphonOneMass_WLambda hk L

/-- Exact random-valued mass of an arbitrary-profile finite or infinite
block sequence. -/
theorem graphonRandomMass_profileWLambda {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) :
    graphonRandomMass (profileWLambda p L ⟨hp.1.le, hp.2.le⟩) =
      ((k - 2 : ℕ) : ℝ) * L.mass := by
  unfold graphonRandomMass
  rw [Measure.real, measure_congr
    (graphonRandomRegion_profileWLambda_ae_eq_WLambda hk hp L),
    ← Measure.real]
  exact graphonRandomMass_WLambda hk L

/-- Exact nonzero-region mass of an arbitrary-profile finite or infinite
block sequence. -/
theorem graphonNonzeroMass_profileWLambda {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) :
    graphonNonzeroMass (profileWLambda p L ⟨hp.1.le, hp.2.le⟩) =
      ((k - 1 : ℕ) : ℝ) * L.mass := by
  rw [graphonNonzeroMass_eq_oneMass_add_randomMass,
    graphonOneMass_profileWLambda hk hp L,
    graphonRandomMass_profileWLambda hk hp L]
  norm_num [Nat.cast_sub (show 1 ≤ k by omega),
    Nat.cast_sub (show 2 ≤ k by omega)]
  ring

/-- Exact edge density of an arbitrary-profile finite or infinite block
sequence. -/
theorem graphonEdgeDensity_profileWLambda {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) :
    graphonEdgeDensity (profileWLambda p L ⟨hp.1.le, hp.2.le⟩) =
      (1 + ((k - 2 : ℕ) : ℝ) * p) * L.mass := by
  rw [graphonEdgeDensity_eq_oneMass_add_profile_mul_randomMass hp
      (profileWLambda_ae_threeValued p L ⟨hp.1.le, hp.2.le⟩),
    graphonOneMass_profileWLambda hk hp L,
    graphonRandomMass_profileWLambda hk hp L]
  ring

/-- Exact entropy of an arbitrary-profile finite or infinite block
sequence. -/
theorem graphonEntropy_profileWLambda {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) :
    graphonEntropy (profileWLambda p L ⟨hp.1.le, hp.2.le⟩) =
      (((k - 2 : ℕ) : ℝ) * binaryEntropy p) * L.mass := by
  rw [graphonEntropy_eq_binaryEntropy_mul_randomMass_of_threeValued hp
      (profileWLambda_ae_threeValued p L ⟨hp.1.le, hp.2.le⟩),
    graphonRandomMass_profileWLambda hk hp L]
  ring

end InducedStars
