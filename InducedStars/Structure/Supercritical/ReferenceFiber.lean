import InducedStars.Structure.Supercritical.CoPartiteFamilies
import InducedStars.Structure.Supercritical.Reference
import Mathlib.Tactic

/-!
# A canonical balanced co-multipartite fiber

The consecutive balanced partition supplies an explicit full division.  This
module records the elementary capacity estimate needed to show that its
exact-edge fiber is eventually nonempty at every density strictly above
`1 / (k - 1)` and below one.
-/

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace InducedStars

/-- The transition density is strictly above the internal-edge density of a
balanced `(k-1)`-clique partition. -/
theorem one_div_parts_lt_gammaK {k : ℕ} (hk : 3 ≤ k) :
    (1 : ℝ) / (k - 1 : ℕ) < gammaK k := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  rw [div_lt_iff₀ hr]
  rw [gammaK_mul_denominator k hk]
  have hp : 0 < ((k - 2 : ℕ) : ℝ) * pK k := by
    exact mul_pos (by exact_mod_cast (show 0 < k - 2 by omega))
      (pK_pos (by omega))
  linarith

/-- The canonical balanced full division of `Fin n`. -/
def supercriticalBalancedDivision
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    SupercriticalDivision k (Fin n) where
  parts := supercriticalReferencePart k n
  parts_nonempty := supercriticalReferencePart_nonempty hk hn
  parts_pairwiseDisjoint := supercriticalReferenceParts_pairwiseDisjoint k n

@[simp] theorem supercriticalBalancedDivision_parts
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (i : Fin (k - 1)) :
    (supercriticalBalancedDivision hk hn).parts i =
      supercriticalReferencePart k n i :=
  rfl

@[simp] theorem supercriticalBalancedDivision_isFull
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    (supercriticalBalancedDivision hk hn).IsFull := by
  rw [SupercriticalDivision.isFull_iff_support_eq_univ]
  exact biUnion_supercriticalReferencePart hk

/-- Twice the internal clique capacity of the balanced division, multiplied
by the number of parts, is at most `n²`. -/
theorem two_mul_parts_mul_balancedDivision_internal_le_sq
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    (k - 1) *
        (2 * divisionInternalCliqueCapacity
          (supercriticalBalancedDivision hk hn)) ≤ n * n := by
  let r := k - 1
  let D := supercriticalBalancedDivision hk hn
  have hr : 0 < r := by omega
  have hpart (i : Fin r) : (D.parts i).card - 1 ≤ n / r := by
    change (supercriticalReferencePart k n i).card - 1 ≤ n / (k - 1)
    rw [card_supercriticalReferencePart hk]
    split_ifs <;> simp
  have htwice :
      2 * divisionInternalCliqueCapacity D =
        ∑ i : Fin r, (D.parts i).card * ((D.parts i).card - 1) := by
    unfold divisionInternalCliqueCapacity
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Nat.mul_comm 2, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self _)]
  have hsum :
      (∑ i : Fin r, (D.parts i).card * ((D.parts i).card - 1)) ≤
        ∑ i : Fin r, (D.parts i).card * (n / r) := by
    exact Finset.sum_le_sum fun i _hi ↦
      Nat.mul_le_mul_left (D.parts i).card (hpart i)
  have hcard : ∑ i : Fin r, (D.parts i).card = n := by
    have hs := D.card_parts_add_card_sparse
    have hfull : D.IsFull := supercriticalBalancedDivision_isFull hk hn
    simp only [SupercriticalDivision.IsFull] at hfull
    rw [hfull, Finset.card_empty, Nat.add_zero] at hs
    simpa [D, r] using hs
  have hdiv : r * (n / r) ≤ n := Nat.mul_div_le n r
  calc
    r * (2 * divisionInternalCliqueCapacity D) =
        r * (∑ i : Fin r,
          (D.parts i).card * ((D.parts i).card - 1)) := by rw [htwice]
    _ ≤ r * (∑ i : Fin r, (D.parts i).card * (n / r)) :=
      Nat.mul_le_mul_left r hsum
    _ = n * (r * (n / r)) := by
      rw [← Finset.sum_mul, hcard]
      ac_rfl
    _ ≤ n * n := Nat.mul_le_mul_left n hdiv

/-- The internal-density requirement of the balanced fiber is eventually
below every fixed density strictly larger than `1 / (k - 1)`. -/
theorem eventually_balancedDivision_internal_le_of_density_gt
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgammaLower : (1 : ℝ) / (k - 1 : ℕ) < gamma)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n in atTop, ∀ hn : k - 1 ≤ n,
      divisionInternalCliqueCapacity
          (supercriticalBalancedDivision hk hn) ≤ m n := by
  let a : ℝ := ((1 : ℝ) / (k - 1 : ℕ) + gamma) / 2
  have hOneDivLtA : (1 : ℝ) / (k - 1 : ℕ) < a := by
    dsimp [a]
    linarith
  have hALtGamma : a < gamma := by
    dsimp [a]
    linarith
  have hDensity :
      ∀ᶠ n in atTop,
        a < (m n : ℝ) / (completeEdgeCount n : ℝ) :=
    (tendsto_order.1 hm).1 a hALtGamma
  have hrReal : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have har : 1 < a * (k - 1 : ℕ) := by
    have := (mul_lt_mul_of_pos_right hOneDivLtA hrReal)
    field_simp at this
    simpa [mul_comm] using this
  have hGrowth : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) < a * (k - 1 : ℕ) * (n - 1 : ℕ) := by
    let b : ℝ := a * (k - 1 : ℕ)
    have hb : 1 < b := har
    have hden : 0 < b - 1 := sub_pos.mpr hb
    obtain ⟨N : ℕ, hN : b / (b - 1) < N⟩ := exists_nat_gt (b / (b - 1))
    filter_upwards [eventually_atTop.2 ⟨max N 2, fun _ hn ↦ hn⟩] with n hn
    have hNn : N ≤ n := (Nat.le_max_left _ _).trans hn
    have hnTwo : 2 ≤ n := (Nat.le_max_right _ _).trans hn
    have hnRatio : b / (b - 1) < (n : ℝ) :=
      hN.trans_le (by exact_mod_cast hNn)
    have hbLt : b < (b - 1) * (n : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hden).mp hnRatio
    have hcastSub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    change (n : ℝ) < b * ((n - 1 : ℕ) : ℝ)
    rw [hcastSub]
    nlinarith
  filter_upwards [hDensity, hGrowth,
    eventually_atTop.2 ⟨2, fun _ hn ↦ hn⟩] with n hdensity hgrowth hnLarge
  intro hn
  let D := supercriticalBalancedDivision hk hn
  have hcapacity := two_mul_parts_mul_balancedDivision_internal_le_sq hk hn
  have hcomplete : (completeEdgeCount n : ℝ) =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) / 2 := by
    rw [completeEdgeCount, Nat.cast_choose_two,
      Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hcompletePos : (0 : ℝ) < completeEdgeCount n := by
    exact_mod_cast (Nat.choose_pos hnLarge : 0 < Nat.choose n 2)
  have hmLower : a * (completeEdgeCount n : ℝ) < (m n : ℝ) :=
    (lt_div_iff₀ hcompletePos).mp hdensity
  have hcapReal :
      ((k - 1) * (2 * divisionInternalCliqueCapacity D) : ℕ) ≤ n * n :=
    hcapacity
  have hcapReal' :
      ((k - 1 : ℕ) : ℝ) * (2 * (divisionInternalCliqueCapacity D : ℝ)) ≤
        (n : ℝ) * n := by
    exact_mod_cast hcapReal
  have hstrict :
      ((k - 1 : ℕ) : ℝ) *
          (2 * (divisionInternalCliqueCapacity D : ℝ)) <
        ((k - 1 : ℕ) : ℝ) * (2 * (m n : ℝ)) := by
    calc
      ((k - 1 : ℕ) : ℝ) * (2 * (divisionInternalCliqueCapacity D : ℝ)) ≤
          (n : ℝ) * n := hcapReal'
      _ < a * (k - 1 : ℕ) * ((n - 1 : ℕ) : ℝ) * n := by
        nlinarith
      _ = ((k - 1 : ℕ) : ℝ) *
          (2 * (a * (completeEdgeCount n : ℝ))) := by
        rw [hcomplete]
        ring
      _ < ((k - 1 : ℕ) : ℝ) * (2 * (m n : ℝ)) := by
        gcongr
  have hinternalReal :
      (divisionInternalCliqueCapacity D : ℝ) < (m n : ℝ) := by
    nlinarith
  have hinternalNat : divisionInternalCliqueCapacity D < m n := by
    exact_mod_cast hinternalReal
  exact hinternalNat.le

/-- Every asymptotic density below one eventually has a feasible total edge
count. -/
theorem eventually_edgeCount_le_completeEdgeCount_of_density_lt_one
    (gamma : ℝ) (hgammaUpper : gamma < 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n in atTop, m n ≤ completeEdgeCount n := by
  have hratio : ∀ᶠ n in atTop,
      (m n : ℝ) / (completeEdgeCount n : ℝ) < 1 :=
    (tendsto_order.1 hm).2 1 hgammaUpper
  filter_upwards [hratio, eventually_atTop.2 ⟨2, fun _ hn ↦ hn⟩] with n hnratio hn
  have hcomplete : (0 : ℝ) < completeEdgeCount n := by
    exact_mod_cast (Nat.choose_pos hn : 0 < Nat.choose n 2)
  have hmReal : (m n : ℝ) < completeEdgeCount n :=
    (div_lt_one hcomplete).mp hnratio
  have hmNat : m n < completeEdgeCount n := by
    exact_mod_cast hmReal
  exact hmNat.le

/-- The canonical balanced fiber is eventually nonempty throughout the open
density interval `(1/(k-1), 1)`. -/
theorem eventually_supercriticalBalancedFiber_nonempty
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo ((1 : ℝ) / (k - 1 : ℕ)) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n in atTop, ∃ hn : k - 1 ≤ n,
      (supercriticalCoPartiteFiber
        (supercriticalBalancedDivision hk hn) (m n)).Nonempty := by
  filter_upwards [eventually_balancedDivision_internal_le_of_density_gt
      k hk gamma hgamma.1 m hm,
    eventually_edgeCount_le_completeEdgeCount_of_density_lt_one
      gamma hgamma.2 m hm,
    eventually_atTop.2 ⟨k - 1, fun _ hn ↦ hn⟩] with n hlower hupper hn
  refine ⟨hn, ?_⟩
  let D := supercriticalBalancedDivision hk hn
  have hfull : D.IsFull := supercriticalBalancedDivision_isFull hk hn
  have hsum := supercriticalTotalCrossCapacity_add_internal D
  rw [D.support_eq_univ hfull] at hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  unfold completeEdgeCount at hupper
  have hselected : m n - divisionInternalCliqueCapacity D ≤
      supercriticalTotalCrossCapacity D := by omega
  have hchoose : 0 < Nat.choose (supercriticalTotalCrossCapacity D)
      (m n - divisionInternalCliqueCapacity D) :=
    Nat.choose_pos hselected
  rw [← Finset.card_pos, card_supercriticalCoPartiteFiber D hfull,
    if_pos (hlower hn)]
  exact hchoose

/-- The labeled co-multipartite exact-edge count is eventually positive in
the supercritical density range. -/
theorem eventually_coMultipartiteGraphCountWithEdges_pos
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo ((1 : ℝ) / (k - 1 : ℕ)) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n in atTop,
      0 < coMultipartiteGraphCountWithEdges (k - 1) n (m n) := by
  filter_upwards [eventually_supercriticalBalancedFiber_nonempty
    k hk gamma hgamma m hm] with n hfiber
  obtain ⟨hn, G, hG⟩ := hfiber
  have hglobal : G ∈ coMultipartiteGraphFinsetWithEdges (k - 1) n (m n) := by
    rw [mem_coMultipartiteGraphFinsetWithEdges]
    refine ⟨supercriticalCoPartiteFiber_isCoMultipartite hG, ?_⟩
    rw [← finiteGraphEdges_card_eq_edgeFinset_card]
    exact card_finiteGraphEdges_eq_of_mem_supercriticalCoPartiteFiber hG
  exact Finset.card_pos.mpr ⟨G, hglobal⟩

/-- Supercritical-range specialization of eventual positivity. -/
theorem eventually_supercriticalCoMultipartiteGraphCountWithEdges_pos
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (gammaK k) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n in atTop,
      0 < coMultipartiteGraphCountWithEdges (k - 1) n (m n) :=
  eventually_coMultipartiteGraphCountWithEdges_pos k hk gamma
    ⟨(one_div_parts_lt_gammaK hk).trans hgamma.1, hgamma.2⟩ m hm

end InducedStars
