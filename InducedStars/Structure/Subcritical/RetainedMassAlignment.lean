import InducedStars.Graphon.FiniteBlockLayouts
import InducedStars.Structure.Subcritical.DistinguishedReference

/-!
# Aligning a dominant complete block

Paper: the alignment step in `lemma:sub-retained-mass-gap-K1k`.
Deleting the other blocks is charged by their normalized quadratic mass;
moving the endpoints of the surviving complete block costs linearly in
the change of its length.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Classical Topology
namespace InducedStars

def subcriticalSingleBlockLengths (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    FiniteProfileBlockLengths 1 where
  alpha := fun _ ↦ a
  alpha_nonneg := fun _ ↦ ha
  sum_alpha_le_one := by simpa using ha1

theorem subcriticalSingleBlock_endpointError_le
    {k : ℕ} (C : RegularBlockCore k) (a b : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    FiniteProfileBlockLayout.fixedCoreEndpointError
      (subcriticalSingleBlockLengths a ha ha1) (subcriticalSingleBlockLengths b hb hb1)
      (fun _ ↦ C) ≤ 2 * (C.order : ℝ) * |a - b| := by
  have hr : (0 : ℝ) < C.order := by exact_mod_cast C.order_pos
  unfold FiniteProfileBlockLayout.fixedCoreEndpointError
  rw [Fin.sum_univ_one]
  have hpoint (v : Fin C.order) :
      |a * ((v : ℝ) / C.order) - b * ((v : ℝ) / C.order)| +
        |a * (((v : ℕ) + 1 : ℝ) / C.order) -
          b * (((v : ℕ) + 1 : ℝ) / C.order)| ≤ 2 * |a - b| := by
    have hv : (v : ℝ) ≤ C.order := by exact_mod_cast v.isLt.le
    have hv1 : ((v : ℕ) + 1 : ℝ) ≤ C.order := by exact_mod_cast v.isLt
    have h0 : (0 : ℝ) ≤ (v : ℝ) / C.order := by positivity
    have h1 : (0 : ℝ) ≤ ((v : ℕ) + 1 : ℝ) / C.order := by positivity
    rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1]
    have hleft := mul_le_mul_of_nonneg_left ((div_le_one hr).mpr hv) (abs_nonneg (a - b))
    have hright := mul_le_mul_of_nonneg_left ((div_le_one hr).mpr hv1) (abs_nonneg (a - b))
    linarith
  calc
    _ ≤ ∑ _v : Fin C.order, 2 * |a - b| := by
      apply Finset.sum_le_sum
      intro v _
      simpa [FiniteProfileBlockLayout.cellLeft, FiniteProfileBlockLayout.cellRight,
        FiniteProfileBlockLayout.blockStart, FiniteProfileBlockLengths.layout,
        subcriticalSingleBlockLengths] using hpoint v
    _ = _ := by simp; ring

theorem subcriticalSingleBlock_cutDist_le
    {k : ℕ} (C : RegularBlockCore k) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    cutDist (((subcriticalSingleBlockLengths a ha ha1).layout (fun _ ↦ C)).graphon p hp)
      (((subcriticalSingleBlockLengths b hb hb1).layout (fun _ ↦ C)).graphon p hp) ≤
      4 * (C.order : ℝ) * |a - b| := by
  apply (cutDist_le_graphonL1Dist _ _).trans
  apply (FiniteProfileBlockLayout.graphonL1Dist_fixedCoreLayouts_le_endpointError
    p hp _ _ (fun _ ↦ C)).trans
  have hh := mul_le_mul_of_nonneg_left
    (subcriticalSingleBlock_endpointError_le C a b ha ha1 hb hb1) (by norm_num : (0 : ℝ) ≤ 2)
  linarith

theorem subcriticalOneBlockSequence_count
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (oneBlockSequence k hk a ha ha1).count = some 1 := rfl

theorem subcriticalSingleBlock_layout_eq_oneBlock
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (subcriticalSingleBlockLengths a ha.le ha1).layout
      (fun _ ↦ RegularBlockCore.complete k hk) =
    FiniteProfileBlockLayout.ofFiniteSequence (oneBlockSequence k hk a ha ha1) 1
      (subcriticalOneBlockSequence_count hk a ha ha1) := by
  unfold subcriticalSingleBlockLengths FiniteProfileBlockLengths.layout
    FiniteProfileBlockLayout.ofFiniteSequence oneBlockSequence
  congr 1
  funext i
  have hi : (i : ℕ) = 0 := by omega
  simp [hi]

theorem subcriticalOneBlock_cutDist_le
    {k : ℕ} (hk : 3 ≤ k) (a b : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    cutDist (WLambda hk (oneBlockSequence k hk a ha ha1))
      (WLambda hk (oneBlockSequence k hk b hb hb1)) ≤
      4 * ((k - 1 : ℕ) : ℝ) * |a - b| := by
  have hh := subcriticalSingleBlock_cutDist_le (RegularBlockCore.complete k hk)
    (pK k) (pK_mem_Icc k) a b ha.le ha1 hb.le hb1
  rw [subcriticalSingleBlock_layout_eq_oneBlock hk a ha ha1,
    subcriticalSingleBlock_layout_eq_oneBlock hk b hb hb1,
    FiniteProfileBlockLayout.graphon_ofFiniteSequence_eq_profileWLambda hk,
    FiniteProfileBlockLayout.graphon_ofFiniteSequence_eq_profileWLambda hk] at hh
  simpa only [profileWLambda_pK hk, RegularBlockCore.complete_order] using hh

/-- Finite prefix alignment, with the unused infinite tail kept explicitly.
The index j is moved to the first position by a measure-preserving block
permutation before all other prefix blocks are deleted. -/
theorem cutDist_WLambda_oneBlock_le_prefix_error
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k) (j N : ℕ)
    (hj : 0 < L.alpha j) (hjN : j < N)
    (hcore : L.core j = RegularBlockCore.complete k hk) :
    cutDist (WLambda hk L)
      (WLambda hk (oneBlockSequence k hk (L.alpha j) hj (L.alpha_le_one j))) ≤
      L.alphaSquareTail N +
        (1 + ((k - 2 : ℕ) : ℝ) * pK k) * (L.mass - L.massTerm j) := by
  let p := pK k
  let hp := pK_mem_Icc k
  let A := FiniteProfileBlockLayout.ofPrefix L N
  let z : Fin N := ⟨0, by omega⟩
  let jF : Fin N := ⟨j, hjN⟩
  let e := Equiv.swap z jF
  let B := A.permute e
  have hN : 1 ≤ N := by omega
  have hswap (i : Fin 1) : e (Fin.castLE hN i) = jF := by
    have hi : Fin.castLE hN i = z := by apply Fin.ext; dsimp [z]; omega
    rw [hi]
    exact Equiv.swap_apply_left z jF
  have hlayout : B.take 1 hN =
      (subcriticalSingleBlockLengths (L.alpha j) hj.le (L.alpha_le_one j)).layout
        (fun _ ↦ RegularBlockCore.complete k hk) := by
    unfold B A FiniteProfileBlockLayout.take FiniteProfileBlockLayout.permute
      FiniteProfileBlockLayout.ofPrefix subcriticalSingleBlockLengths
      FiniteProfileBlockLengths.layout
    congr 1
    · funext i
      change L.alpha (e (Fin.castLE hN i)) = L.alpha j
      rw [hswap]
    · funext i
      change L.core (e (Fin.castLE hN i)) = RegularBlockCore.complete k hk
      rw [hswap]
      exact hcore
  have hprefix : B.prefixGraphon p hp 1 =
      WLambda hk (oneBlockSequence k hk (L.alpha j) hj (L.alpha_le_one j)) := by
    rw [B.prefixGraphon_eq_graphon_take p hp 1 hN, hlayout,
      subcriticalSingleBlock_layout_eq_oneBlock hk _ hj (L.alpha_le_one j),
      FiniteProfileBlockLayout.graphon_ofFiniteSequence_eq_profileWLambda hk]
    exact profileWLambda_pK hk _
  let f := fun i : Fin N ↦ B.alpha i ^ 2 / (B.core i).order
  let C := 1 + ((k - 2 : ℕ) : ℝ) * pK k
  have hC : 0 ≤ C :=
    add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (pK_mem_Icc k).1)
  have hfz : f z = L.massTerm j := by
    dsimp [f, B, A, FiniteProfileBlockLayout.permute, FiniteProfileBlockLayout.ofPrefix]
    rw [show e z = jF from Equiv.swap_apply_left z jF]
    rfl
  have hmass : (∑ i : Fin N, f i) ≤ L.mass := by
    change (∑ i : Fin N, L.massTerm (e i)) ≤ L.mass
    rw [Equiv.sum_comp e (fun i : Fin N ↦ L.massTerm i), Fin.sum_univ_eq_sum_range]
    exact L.summable_massTerm.sum_le_tsum (Finset.range N) (fun i _ ↦ L.massTerm_nonneg i)
  have hindex (i : Fin N) : 1 ≤ (i : ℕ) ↔ i ≠ z := by
    constructor
    · intro hi heq
      subst i
      dsimp [z] at hi
      omega
    · intro hi
      by_contra h
      apply hi
      apply Fin.ext
      dsimp [z]
      omega
  have herase : (∑ i : Fin N, if 1 ≤ (i : ℕ) then f i else 0) =
      ∑ i ∈ Finset.univ.erase z, f i := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp [hindex, ne_comm]
  have htail : (∑ i : Fin N, if 1 ≤ (i : ℕ) then f i else 0) ≤
      L.mass - L.massTerm j := by
    rw [herase]
    have hh := Finset.sum_erase_add Finset.univ f (Finset.mem_univ z)
    rw [hfz] at hh
    linarith
  have hdelete : graphonL1Dist (B.graphon p hp) (B.prefixGraphon p hp 1) ≤
      C * (L.mass - L.massTerm j) := by
    rw [B.graphonL1Dist_prefixGraphon_eq_sum_omittedBlockMass]
    calc
      _ = C * ∑ i : Fin N, if 1 ≤ (i : ℕ) then f i else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> dsimp [f, C, p] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htail hC
  have hperm : cutDist (A.graphon p hp) (B.graphon p hp) = 0 := by
    rw [cutDist_comm]
    exact A.cutDist_graphon_permute_eq_zero p hp e
  have happrox : cutDist (WLambda hk L) (A.graphon p hp) ≤ L.alphaSquareTail N := by
    simpa only [p, A, profileWLambda_pK hk] using
      FiniteProfileBlockLayout.cutDist_profileWLambda_graphon_ofPrefix_le_alphaSquareTail
        hk p hp L N
  rw [← hprefix]
  calc
    _ ≤ cutDist (WLambda hk L) (A.graphon p hp) +
        cutDist (A.graphon p hp) (B.prefixGraphon p hp 1) := cutDist_triangle _ _ _
    _ ≤ L.alphaSquareTail N +
        (cutDist (A.graphon p hp) (B.graphon p hp) +
          cutDist (B.graphon p hp) (B.prefixGraphon p hp 1)) :=
      add_le_add happrox (cutDist_triangle _ _ _)
    _ ≤ _ := by
      rw [hperm, zero_add]
      exact add_le_add le_rfl ((cutDist_le_graphonL1Dist _ _).trans hdelete)

/-- Aligning one complete block and deleting every other block costs at
most their exact normalized quadratic mass. Infinite tails are removed by
letting the finite-prefix approximation error tend to zero. -/
theorem cutDist_WLambda_oneBlock_le_omitted_mass
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k) (j : ℕ)
    (hj : 0 < L.alpha j) (hcore : L.core j = RegularBlockCore.complete k hk) :
    cutDist (WLambda hk L)
      (WLambda hk (oneBlockSequence k hk (L.alpha j) hj (L.alpha_le_one j))) ≤
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) * (L.mass - L.massTerm j) := by
  have ht := L.alphaSquareTail_tendsto_zero.add_const
    ((1 + ((k - 2 : ℕ) : ℝ) * pK k) * (L.mass - L.massTerm j))
  simp only [zero_add] at ht
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop j] with N hN
  exact cutDist_WLambda_oneBlock_le_prefix_error hk L j N hj hN hcore

/-- Paper: the dominant-block alignment step in
`lemma:sub-retained-mass-gap-K1k`. The resize constant is explicit and only
depends on k; the omitted blocks are charged by normalized quadratic mass,
not by their possibly large total vertex length. -/
theorem cutDist_WLambda_subcriticalDistinguished_le
    {k : ℕ} (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (L : AdmissibleBlockSequence k) (j : ℕ)
    (hj : 0 < L.alpha j) (hcore : L.core j = RegularBlockCore.complete k hk) :
    cutDist (WLambda hk L) (subcriticalDistinguishedGraphon k hk gamma hgamma) ≤
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) * (L.mass - L.massTerm j) +
        4 * ((k - 1 : ℕ) : ℝ) * |L.alpha j - subcriticalOneBlockLength k gamma| := by
  apply (cutDist_triangle _
    (WLambda hk (oneBlockSequence k hk (L.alpha j) hj (L.alpha_le_one j))) _).trans
  exact add_le_add (cutDist_WLambda_oneBlock_le_omitted_mass hk L j hj hcore)
    (subcriticalOneBlock_cutDist_le hk _ _ hj (L.alpha_le_one j)
      (subcriticalOneBlockLength_pos hk hgamma.1)
      (subcriticalOneBlockLength_lt_one hk hgamma.2).le)

end InducedStars
