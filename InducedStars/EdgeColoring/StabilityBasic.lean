import InducedStars.EdgeColoring.Extremal
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-!
# Basic colored stability estimates

Weighted-degree tails and the elementary finite/analytic estimates supporting
them.  Later stability milestones are intentionally kept out of this file.
-/

open Finset
open scoped BigOperators

namespace InducedStars

namespace ColoredGraph

/-! ## Finite averaging -/

variable {α : Type*}

/-- A fixed-cardinality subset whose sum is no larger than its proportional
share of the ambient sum.  This division-free form is convenient for
integer-valued graph parameters. -/
theorem exists_card_eq_mul_sum_le (A : Finset α) (f : α → ℤ) (s : ℕ)
    (hs : s ≤ A.card) :
    ∃ U : Finset α, U ⊆ A ∧ U.card = s ∧
      (A.card : ℤ) * ∑ u ∈ U, f u ≤ (s : ℤ) * ∑ a ∈ A, f a := by
  classical
  obtain ⟨U₀, hU₀A, hU₀card⟩ := A.exists_subset_card_eq hs
  have hfamily : (A.powersetCard s).Nonempty := by
    exact ⟨U₀, Finset.mem_powersetCard.mpr ⟨hU₀A, hU₀card⟩⟩
  obtain ⟨U, hUfamily, hUmin⟩ :=
    Finset.exists_min_image (A.powersetCard s) (fun T ↦ ∑ x ∈ T, f x) hfamily
  have hUA : U ⊆ A := (Finset.mem_powersetCard.mp hUfamily).1
  have hUcard : U.card = s := (Finset.mem_powersetCard.mp hUfamily).2
  have hcross : ∀ u ∈ U, ∀ w ∈ A \ U, f u ≤ f w := by
    intro u hu w hw
    have hwA : w ∈ A := (Finset.mem_sdiff.mp hw).1
    have hwU : w ∉ U := (Finset.mem_sdiff.mp hw).2
    let T := insert w (U.erase u)
    have hTsub : T ⊆ A := by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_erase] at hx
      rcases hx with rfl | ⟨_, hxU⟩
      · exact hwA
      · exact hUA hxU
    have hwErase : w ∉ U.erase u := by simp [hwU]
    have hspos : 0 < s := by
      have : 0 < U.card := Finset.card_pos.mpr ⟨u, hu⟩
      omega
    have hTcard : T.card = s := by
      simp only [T, Finset.card_insert_of_notMem hwErase,
        Finset.card_erase_of_mem hu, hUcard]
      omega
    have hTfamily : T ∈ A.powersetCard s :=
      Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩
    have hmin := hUmin T hTfamily
    simp only [T, Finset.sum_insert hwErase] at hmin
    have herase := Finset.sum_erase_add U f hu
    omega
  have hdouble :
      ∑ u ∈ U, ∑ w ∈ A \ U, f u ≤
        ∑ u ∈ U, ∑ w ∈ A \ U, f w := by
    exact Finset.sum_le_sum fun u hu ↦
      Finset.sum_le_sum fun w hw ↦ hcross u hu w hw
  have hsdiffcard : (A \ U).card = A.card - s := by
    rw [Finset.card_sdiff_of_subset hUA, hUcard]
  have hsplit : ∑ a ∈ A \ U, f a + ∑ u ∈ U, f u = ∑ a ∈ A, f a :=
    Finset.sum_sdiff hUA
  refine ⟨U, hUA, hUcard, ?_⟩
  have hdouble' :
      ((A \ U).card : ℤ) * (∑ u ∈ U, f u) ≤
        (U.card : ℤ) * (∑ w ∈ A \ U, f w) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul, mul_comm] using hdouble
  rw [hsdiffcard, hUcard] at hdouble'
  rw [← hsplit]
  push_cast [Nat.cast_sub hs] at hdouble' ⊢
  nlinarith

/-- If the sum on a finite set is at most `card * b`, some `s`-subset has
sum at most `s * b`. -/
theorem exists_card_eq_sum_le_mul (A : Finset α) (f : α → ℤ) (s : ℕ) (b : ℤ)
    (hs : s ≤ A.card) (havg : ∑ a ∈ A, f a ≤ (A.card : ℤ) * b) :
    ∃ U : Finset α, U ⊆ A ∧ U.card = s ∧
      ∑ u ∈ U, f u ≤ (s : ℤ) * b := by
  classical
  obtain ⟨U, hUA, hUcard, hprop⟩ := exists_card_eq_mul_sum_le A f s hs
  refine ⟨U, hUA, hUcard, ?_⟩
  by_cases hA : A.card = 0
  · have hs0 : s = 0 := by omega
    have hU0 : U = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [hU0, hs0]
  · have hApos : (0 : ℤ) < (A.card : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hA
    have hbound : (A.card : ℤ) * (∑ u ∈ U, f u) ≤
        (A.card : ℤ) * ((s : ℤ) * b) := by
      calc
        (A.card : ℤ) * (∑ u ∈ U, f u) ≤ (s : ℤ) * ∑ a ∈ A, f a := hprop
        _ ≤ (s : ℤ) * ((A.card : ℤ) * b) := by
          exact mul_le_mul_of_nonneg_left havg (by positivity)
        _ = (A.card : ℤ) * ((s : ℤ) * b) := by ring
    exact (Int.mul_le_mul_left hApos).mp hbound

section EraseAverage

variable [Fintype α] [DecidableEq α]

/-- A low-sum fixed-cardinality subset avoiding a distinguished element.
The hypothesis `b ≤ f z` is essential: minimizing only among subsets that
avoid `z` does not, by itself, compare their average with the global one. -/
theorem exists_card_eq_sum_le_mul_erase (z : α) (f : α → ℤ) (s : ℕ) (b : ℤ)
    (hs : s ≤ (Finset.univ.erase z).card)
    (htotal : ∑ a, f a ≤ (Fintype.card α : ℤ) * b)
    (hz : b ≤ f z) :
    ∃ U : Finset α, U ⊆ Finset.univ.erase z ∧ U.card = s ∧
      ∑ u ∈ U, f u ≤ (s : ℤ) * b := by
  classical
  have herase := Finset.sum_erase_add Finset.univ f (Finset.mem_univ z)
  have hcard : (Finset.univ.erase z).card + 1 = Fintype.card α := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ z)
  have hcardz := congrArg (fun m : ℕ ↦ (m : ℤ)) hcard
  push_cast at hcardz
  have havgErase :
      ∑ a ∈ Finset.univ.erase z, f a ≤
        ((Finset.univ.erase z).card : ℤ) * b := by
    calc
      ∑ a ∈ Finset.univ.erase z, f a = (∑ a, f a) - f z := by omega
      _ ≤ (Fintype.card α : ℤ) * b - b := sub_le_sub htotal hz
      _ = ((Finset.univ.erase z).card : ℤ) * b := by
        rw [← hcardz]
        ring
  exact exists_card_eq_sum_le_mul (Finset.univ.erase z) f s b hs havgErase

end EraseAverage

/-! ## Finite transversals -/

section FiniteTransversal

variable {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

private theorem expect_prod_type_real {A B : Type*} [Fintype A] [Fintype B]
    (f : A × B → ℝ) :
    (𝔼 p : A × B, f p) = 𝔼 a : A, 𝔼 b : B, f (a, b) := by
  simpa using Finset.expect_product (Finset.univ : Finset A)
    (Finset.univ : Finset B) f

/-- Number of bad ordered pairs between two choices in a finite family. -/
def transversalBadPairCount (S : I → Finset V) (bad : V → V → Prop)
    [DecidableRel bad] (i j : I) : ℕ :=
  #{p : (S i) × (S j) | bad p.1 p.2}

/-- Two coordinates of a uniformly chosen finite transversal are uniform and
independent. -/
theorem expect_transversal_pair_indicator
    (S : I → Finset V) (hS : ∀ i, (S i).Nonempty)
    (bad : V → V → Prop) [DecidableRel bad]
    {i j : I} (hij : i ≠ j) :
    (𝔼 f : ∀ a, S a, if bad (f i) (f j) then (1 : ℝ) else 0) =
      (transversalBadPairCount S bad i j : ℝ) /
        ((S i).card * (S j).card : ℕ) := by
  classical
  letI (a : I) : Nonempty (S a) := (hS a).to_subtype
  let j' : {a : I // a ≠ i} := ⟨j, hij.symm⟩
  let e₁ := Equiv.piSplitAt i (fun a ↦ (S a))
  let e₂ := Equiv.piSplitAt j'
    (fun a : {a : I // a ≠ i} ↦ (S a.1))
  let e := e₁.trans ((Equiv.refl (S i)).prodCongr e₂)
  calc
    (𝔼 f : ∀ a, S a,
        if bad (f i) (f j) then (1 : ℝ) else 0) =
      𝔼 q : (S i) × ((S j'.1) ×
          ((a : {a : {a : I // a ≠ i} // a ≠ j'}) → (S a.1.1))),
        if bad q.1 q.2.1 then (1 : ℝ) else 0 := by
        apply Fintype.expect_equiv e
        intro f
        rfl
    _ = 𝔼 x : (S i), 𝔼 y : (S j),
        if bad x y then (1 : ℝ) else 0 := by
      let R :=
        (a : {a : {a : I // a ≠ i} // a ≠ j'}) → (S a.1.1)
      letI : Nonempty R :=
        ⟨fun a ↦ Classical.choice (hS a.1.1).to_subtype⟩
      have hc (x : S i) (y : S j) :
          (𝔼 _ : R, if bad x y then (1 : ℝ) else 0) =
            if bad x y then (1 : ℝ) else 0 :=
        Fintype.expect_const _
      rw [expect_prod_type_real]
      simp_rw [expect_prod_type_real]
      change (𝔼 x : S i, 𝔼 y : S j,
        𝔼 _ : R, if bad x y then (1 : ℝ) else 0) =
          𝔼 x : S i, 𝔼 y : S j,
            if bad x y then (1 : ℝ) else 0
      exact congrArg
        (fun F : (S i) → ℝ ↦ 𝔼 x : (S i), F x)
        (funext fun x ↦ congrArg
          (fun F : (S j) → ℝ ↦ 𝔼 y : (S j), F y)
          (funext fun y ↦ hc x y))
    _ = 𝔼 p : (S i) × (S j),
        if bad p.1 p.2 then (1 : ℝ) else 0 := by
      symm
      apply expect_prod_type_real
    _ = (transversalBadPairCount S bad i j : ℝ) /
        ((S i).card * (S j).card : ℕ) := by
      rw [Fintype.expect_eq_sum_div_card]
      simp [transversalBadPairCount, Fintype.card_prod]

private def transversalBadCount (S : I → Finset V)
    (bad : V → V → Prop) [DecidableRel bad] (f : ∀ i, S i) : ℝ :=
  ∑ i : I, ∑ j : I, if i ≠ j ∧ bad (f i) (f j) then 1 else 0

/-- A finite union bound: if every bad two-coordinate marginal is at most
`ε` and `|I|² ε < 1`, there is a transversal with no bad pair. -/
theorem exists_transversal_no_bad
    (S : I → Finset V) (bad : V → V → Prop) [DecidableRel bad]
    (hS : ∀ i, (S i).Nonempty) {ε : ℝ} (hε : 0 ≤ ε)
    (hpair : ∀ i j, i ≠ j →
      (transversalBadPairCount S bad i j : ℝ) /
        ((S i).card * (S j).card : ℕ) ≤ ε)
    (hsmall : (Fintype.card I : ℝ) ^ 2 * ε < 1) :
    ∃ f : ∀ i, S i, ∀ i j, i ≠ j → ¬ bad (f i) (f j) := by
  classical
  let f₀ : ∀ i, S i := fun i ↦ ⟨(hS i).choose, (hS i).choose_spec⟩
  let Z : (∀ i, S i) → ℝ := transversalBadCount S bad
  have hEZ : (𝔼 f : ∀ i, S i, Z f) ≤ (Fintype.card I : ℝ) ^ 2 * ε := by
    calc
      (𝔼 f : ∀ i, S i, Z f) =
          ∑ i : I, ∑ j : I,
            (𝔼 f : ∀ a, S a,
              if i ≠ j ∧ bad (f i) (f j) then (1 : ℝ) else 0) := by
            simp only [Z, transversalBadCount]
            rw [Finset.expect_sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.expect_sum_comm]
      _ ≤ ∑ _i : I, ∑ _j : I, ε := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i = j
        · subst j
          simp [hε]
        · simpa [hij, expect_transversal_pair_indicator S hS bad hij] using
            hpair i j hij
      _ = (Fintype.card I : ℝ) ^ 2 * ε := by
        simp [pow_two]
        ring
  have hEZlt : (𝔼 f : ∀ i, S i, Z f) < 1 := hEZ.trans_lt hsmall
  have huniv : (Finset.univ : Finset (∀ i, S i)).Nonempty :=
    ⟨f₀, Finset.mem_univ _⟩
  obtain ⟨f, _hf, hfZ⟩ := Finset.exists_lt_of_expect_lt huniv hEZlt
  refine ⟨f, ?_⟩
  intro i j hij hbad
  have hone : (1 : ℝ) ≤ Z f := by
    dsimp [Z, transversalBadCount]
    have hterm : (1 : ℝ) ≤
        ∑ j' : I, if i ≠ j' ∧ bad (f i) (f j') then 1 else 0 := by
      calc
        (1 : ℝ) = (if i ≠ j ∧ bad (f i) (f j) then 1 else 0) := by
          simp [hij, hbad]
        _ ≤ ∑ j' : I, if i ≠ j' ∧ bad (f i) (f j') then 1 else 0 := by
          exact Finset.single_le_sum
            (f := fun j' : I ↦ if i ≠ j' ∧ bad (f i) (f j') then (1 : ℝ) else 0)
            (fun _ _ ↦ by positivity) (Finset.mem_univ j)
    exact hterm.trans (Finset.single_le_sum
      (f := fun i' : I ↦
        ∑ j' : I, if i' ≠ j' ∧ bad (f i') (f j') then (1 : ℝ) else 0)
      (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity)
      (Finset.mem_univ i))
  linarith

end FiniteTransversal

/-! ## Restricted weighted degrees -/

section DegreeRestriction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Color-degree contributions from a set and its complement add to the full
color degree. -/
theorem degreeIn_add_degreeIn_compl (C : ColoredGraph V) (c : EdgeColor)
    (v : V) (U : Finset V) :
    C.degreeIn c v U + C.degreeIn c v Uᶜ = C.degree c v := by
  unfold ColoredGraph.degreeIn ColoredGraph.neighborFinsetIn ColoredGraph.degree
  rw [← Finset.sdiff_eq_inter_compl]
  exact Finset.card_inter_add_card_sdiff _ _

/-- Exact decomposition `D(v,U) + D(v,Uᶜ) = D(v)`. -/
theorem weightedDegreeIn_add_compl (k : ℕ) (C : ColoredGraph V)
    (v : V) (U : Finset V) :
    weightedDegreeIn k C v U + weightedDegreeIn k C v Uᶜ =
      weightedDegree k C v := by
  have hr := degreeIn_add_degreeIn_compl C .red v U
  have hb := degreeIn_add_degreeIn_compl C .blue v U
  have hrz := congrArg (fun m : ℕ ↦ (m : ℤ)) hr
  have hbz := congrArg (fun m : ℕ ↦ (m : ℤ)) hb
  unfold weightedDegreeIn weightedDegree
  push_cast at hrz hbz
  linear_combination hrz - (delta k : ℤ) * hbz

/-- A restricted color degree is at most the size of the restricting set. -/
theorem degreeIn_le_card (C : ColoredGraph V) (c : EdgeColor)
    (v : V) (U : Finset V) : C.degreeIn c v U ≤ U.card := by
  unfold ColoredGraph.degreeIn ColoredGraph.neighborFinsetIn
  exact Finset.card_le_card Finset.inter_subset_right

theorem weightedDegreeIn_le_card (k : ℕ) (C : ColoredGraph V)
    (v : V) (U : Finset V) :
    weightedDegreeIn k C v U ≤ (U.card : ℤ) := by
  have hr := degreeIn_le_card C .red v U
  unfold weightedDegreeIn
  have hnonneg : (0 : ℤ) ≤ (delta k : ℤ) * (C.blueDegreeIn v U : ℤ) := by
    positivity
  calc
    (C.redDegreeIn v U : ℤ) -
        (delta k : ℤ) * (C.blueDegreeIn v U : ℤ) ≤
        (C.redDegreeIn v U : ℤ) := sub_le_self _ hnonneg
    _ ≤ (U.card : ℤ) := by exact_mod_cast hr

theorem neg_delta_mul_card_le_weightedDegreeIn (k : ℕ) (C : ColoredGraph V)
    (v : V) (U : Finset V) :
    -(delta k : ℤ) * (U.card : ℤ) ≤ weightedDegreeIn k C v U := by
  have hb := degreeIn_le_card C .blue v U
  have hbz : (C.blueDegreeIn v U : ℤ) ≤ (U.card : ℤ) := by exact_mod_cast hb
  have hmul : (delta k : ℤ) * (C.blueDegreeIn v U : ℤ) ≤
      (delta k : ℤ) * (U.card : ℤ) :=
    mul_le_mul_of_nonneg_left hbz (by positivity)
  unfold weightedDegreeIn
  have hred : (0 : ℤ) ≤ (C.redDegreeIn v U : ℤ) := by positivity
  rw [neg_mul]
  calc
    -((delta k : ℤ) * (U.card : ℤ)) ≤
        -((delta k : ℤ) * (C.blueDegreeIn v U : ℤ)) := neg_le_neg hmul
    _ ≤ (C.redDegreeIn v U : ℤ) -
        (delta k : ℤ) * (C.blueDegreeIn v U : ℤ) := by omega

end DegreeRestriction

/-! ## Fourth-root and floor estimates -/

/-- Positivity of the real fourth-root expression used in the tail bounds. -/
theorem quarterPower_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < δ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hδ _

/-- The fourth root is at most one on `[0,1]`. -/
theorem quarterPower_le_one {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    δ ^ (1 / 4 : ℝ) ≤ 1 := by
  exact Real.rpow_le_one hδ₀ hδ₁ (by norm_num)

/-- Squaring the fourth root gives the square root. -/
theorem quarterPower_sq {δ : ℝ} (hδ : 0 ≤ δ) :
    (δ ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt δ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hδ]
  norm_num [Real.sqrt_eq_rpow]

/-- Taking the fourth power of the fourth root recovers a nonnegative real. -/
theorem quarterPower_fourth {δ : ℝ} (hδ : 0 ≤ δ) :
    (δ ^ (1 / 4 : ℝ)) ^ 4 = δ := by
  simpa [one_div] using
    Real.rpow_inv_natCast_pow hδ (by norm_num : (4 : ℕ) ≠ 0)

/-- If `8 ≤ x`, then the natural floor of `x` is at least `7x/8`. -/
theorem seven_eighths_le_natFloor {x : ℝ} (hx : 8 ≤ x) :
    (7 / 8 : ℝ) * x ≤ (⌊x⌋₊ : ℝ) := by
  have hfloor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  nlinarith

/-- Scalar estimate used to turn the degree-sum inequality into the corrected
exceptional-set bound. -/
theorem exceptionalCard_le {q Δ n x : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hΔ : 1 ≤ Δ) (hn : 0 < n)
    (h : x * q * n ≤ 2 * q ^ 4 * n ^ 2 + 8 * Δ * q ^ 2 * n ^ 2) :
    x ≤ 10 * Δ * q * n := by
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hq2le : q ^ 2 ≤ Δ := by
    have hprod : 0 ≤ (1 - q) * (1 + q) :=
      mul_nonneg (sub_nonneg.mpr hq1) (by linarith)
    nlinarith
  have haux :
      2 * q ^ 4 * n ^ 2 + 8 * Δ * q ^ 2 * n ^ 2 ≤
        10 * Δ * q ^ 2 * n ^ 2 := by
    have hprod : 0 ≤ (Δ - q ^ 2) * (q ^ 2 * n ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hq2le) (mul_nonneg hq2 hn2)
    nlinarith [hprod]
  have hqn : 0 < q * n := mul_pos hq0 hn
  nlinarith

theorem restrictedWeightedDegree_lower {q Δ n d x : ℝ} (hq0 : 0 < q)
    (hΔ : 1 ≤ Δ) (hn : 0 ≤ n)
    (hd : -q * n - x ≤ d) (hx : x ≤ 10 * Δ * q * n) :
    -(12 * Δ ^ 2 * q * n) ≤ d := by
  nlinarith [mul_nonneg (sq_nonneg Δ) (mul_nonneg hq0.le hn)]

theorem restrictedWeightedDegree_upper_of_quarterPower_le {q Δ n d x : ℝ}
    (hq0 : 0 < q) (hqsmall : q ≤ 1 / 4) (hΔ : 1 ≤ Δ) (hn : 0 ≤ n)
    (hd : d ≤ 8 * Δ * q ^ 2 * n + Δ * x)
    (hx : x ≤ 10 * Δ * q * n) :
    d ≤ 12 * Δ ^ 2 * q * n := by
  nlinarith [mul_nonneg (sq_nonneg Δ) (mul_nonneg hq0.le hn)]

theorem restrictedWeightedDegree_upper_of_quarterPower_large {q Δ n d : ℝ}
    (hq : 1 / 4 < q) (hΔ : 1 ≤ Δ) (hn : 0 ≤ n) (hd : d ≤ n) :
    d ≤ 12 * Δ ^ 2 * q * n := by
  have hq0 : 0 < q := by linarith
  have hΔsq : 1 ≤ Δ ^ 2 := by nlinarith [sq_nonneg (Δ - 1)]
  have hscale : 12 * q * 1 ≤ 12 * q * Δ ^ 2 :=
    mul_le_mul_of_nonneg_left hΔsq (by positivity)
  have hcoef : 1 ≤ 12 * Δ ^ 2 * q := by
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) hn]

/-- The scalar heart of the cloning contradiction in the upper-tail proof. -/
theorem cloneGain_gt {r δ Δ n s Dz su gain : ℝ}
    (hr : 0 < r) (hr2 : r ^ 2 = δ) (hΔ : 1 ≤ Δ) (hn : 0 < n)
    (hrn : 8 ≤ r * n) (hslo : (7 / 8 : ℝ) * r * n ≤ s)
    (hshi : s ≤ r * n) (hDz : 8 * Δ * r * n < Dz)
    (hsu : su ≤ s * Δ)
    (hgain : s * Dz - su - (Δ + 1) * s ^ 2 ≤ gain) :
    4 * Δ * δ * n ^ 2 < gain := by
  have hspos : 0 < s := by nlinarith
  have hΔ0 : 0 ≤ Δ := le_trans (by norm_num) hΔ
  have hrn0 : 0 ≤ r * n := (mul_pos hr hn).le
  have hsDz : s * (8 * Δ * r * n) < s * Dz :=
    mul_lt_mul_of_pos_left hDz hspos
  have hsource : 7 * Δ * (r * n) ^ 2 ≤ s * (8 * Δ * r * n) := by
    have hprod : 0 ≤ Δ * (r * n) * (s - (7 / 8 : ℝ) * r * n) :=
      mul_nonneg (mul_nonneg hΔ0 hrn0) (sub_nonneg.mpr hslo)
    nlinarith
  have hsum' : su ≤ Δ * (r * n) := by
    have hprod : 0 ≤ Δ * (r * n - s) :=
      mul_nonneg hΔ0 (sub_nonneg.mpr hshi)
    nlinarith
  have hs_sq : s ^ 2 ≤ (r * n) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hshi) (by nlinarith : 0 ≤ r * n + s)]
  have herror : (Δ + 1) * s ^ 2 ≤ 2 * Δ * (r * n) ^ 2 := by
    have hcoef : Δ + 1 ≤ 2 * Δ := by linarith
    have h1 : (Δ + 1) * s ^ 2 ≤ (2 * Δ) * s ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg s)
    have h2 : (2 * Δ) * s ^ 2 ≤ (2 * Δ) * (r * n) ^ 2 :=
      mul_le_mul_of_nonneg_left hs_sq (by positivity)
    exact h1.trans h2
  have htlin : Δ * (r * n) ≤ Δ * (r * n) ^ 2 := by
    have ht : 1 ≤ r * n := by linarith
    have hp : 0 ≤ Δ * (r * n) * (r * n - 1) :=
      mul_nonneg (mul_nonneg hΔ0 hrn0) (sub_nonneg.mpr ht)
    nlinarith
  have hδ : δ = r ^ 2 := hr2.symm
  rw [hδ]
  nlinarith

theorem cloneGain_contradiction {δ Δ n upper lower : ℝ} (hδ : 0 < δ)
    (hΔ : 1 ≤ Δ) (hn : 0 < n) (hlin : Δ ≤ 2 * δ * n)
    (hlower : 4 * Δ * δ * n ^ 2 < lower)
    (hupper : upper ≤ Δ * n / 2 + δ * n ^ 2) :
    lower ≤ upper → False := by
  intro h
  nlinarith [mul_pos hδ (sq_pos_of_pos hn),
    mul_nonneg (by linarith : 0 ≤ Δ) (mul_nonneg hδ.le (sq_nonneg n))]

/-- A single explicit threshold packages every large-`n` estimate needed in
the cloning argument. -/
theorem exists_tailThreshold (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (Δ : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      8 ≤ Real.sqrt δ * (n : ℝ) ∧
      (Δ : ℝ) ≤ 2 * δ * (n : ℝ) ∧
      let s := ⌊Real.sqrt δ * (n : ℝ)⌋₊
      (7 / 8 : ℝ) * Real.sqrt δ * (n : ℝ) ≤ (s : ℝ) ∧
      (s : ℝ) ≤ Real.sqrt δ * (n : ℝ) ∧ s < n := by
  let r := Real.sqrt δ
  have hr : 0 < r := Real.sqrt_pos.2 hδ0
  have hr0 : 0 ≤ r := hr.le
  have hr1 : r < 1 := (Real.sqrt_lt' zero_lt_one).2 (by simpa using hδ1)
  let M := max (8 / r) ((Δ : ℝ) / (2 * δ))
  refine ⟨Nat.ceil M, ?_⟩
  intro n hn
  have hMle : M ≤ (n : ℝ) := by
    calc
      M ≤ (Nat.ceil M : ℕ) := Nat.le_ceil M
      _ ≤ (n : ℝ) := by exact_mod_cast hn
  have hleft : 8 / r ≤ (n : ℝ) := (le_max_left _ _).trans hMle
  have hright : (Δ : ℝ) / (2 * δ) ≤ (n : ℝ) := (le_max_right _ _).trans hMle
  have hrn8 : 8 ≤ r * (n : ℝ) := by
    have h := (div_le_iff₀ hr).mp hleft
    simpa [mul_comm] using h
  have hΔn : (Δ : ℝ) ≤ 2 * δ * (n : ℝ) := by
    have hp : 0 < 2 * δ := mul_pos (by norm_num) hδ0
    have := (div_le_iff₀ hp).mp hright
    nlinarith
  have hn0 : 0 < (n : ℝ) := by
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_nonneg hr0 hnnonneg]
  let s := ⌊r * (n : ℝ)⌋₊
  have hslo0 : r * (n : ℝ) - 1 < (s : ℝ) := Nat.sub_one_lt_floor _
  have hslo : (7 / 8 : ℝ) * r * (n : ℝ) ≤ (s : ℝ) := by nlinarith
  have hshi : (s : ℝ) ≤ r * (n : ℝ) := Nat.floor_le (mul_nonneg hr0 (by positivity))
  have hrnlt : r * (n : ℝ) < (n : ℝ) := by nlinarith
  have hsn : s < n := (Nat.floor_lt (mul_nonneg hr0 (by positivity))).2 hrnlt
  exact ⟨hrn8, hΔn, hslo, hshi, hsn⟩

/-! ## Weighted-degree tails -/

/-- Upper-tail estimate, with the large-`n` floor estimates supplied
explicitly. -/
theorem weightedDegree_le_eight_sqrt {k n : ℕ} (hk : 3 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) {C : ColoredGraph (Fin n)} (hC : C ∈ Ck k n)
    (hnear : -(δ * (n : ℝ) ^ 2) ≤ (objective k C : ℝ))
    (hrn8 : 8 ≤ Real.sqrt δ * (n : ℝ))
    (hΔn : (delta k : ℝ) ≤ 2 * δ * (n : ℝ))
    (hslo : (7 / 8 : ℝ) * Real.sqrt δ * (n : ℝ) ≤
      (⌊Real.sqrt δ * (n : ℝ)⌋₊ : ℝ))
    (hshi : (⌊Real.sqrt δ * (n : ℝ)⌋₊ : ℝ) ≤
      Real.sqrt δ * (n : ℝ))
    (hsn : ⌊Real.sqrt δ * (n : ℝ)⌋₊ < n) :
    ∀ v, (weightedDegree k C v : ℝ) ≤
      8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ) := by
  intro z
  by_contra hznot
  have hz : 8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ) <
      (weightedDegree k C z : ℝ) := lt_of_not_ge hznot
  have hΔnat : 1 ≤ delta k := by
    unfold delta
    omega
  have hΔreal : (1 : ℝ) ≤ (delta k : ℝ) := by exact_mod_cast hΔnat
  have hr : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hnreal : 0 < (n : ℝ) := by
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_nonneg hr.le hnnonneg]
  have hsumInt : ∑ v, weightedDegree k C v = 2 * objective k C :=
    sum_weightedDegree_eq_two_mul_objective k C
  have hmantel := kthOrderMantel hk hC
  have htotal :
      ∑ v, weightedDegree k C v ≤ (n : ℤ) * (delta k : ℤ) := by
    rw [hsumInt]
    have htwo : 2 * objective k C ≤
        2 * ((delta k * n / 2 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left hmantel (by norm_num)
    have hfloor : 2 * (delta k * n / 2) ≤ delta k * n := by omega
    have hfloorZ : 2 * ((delta k * n / 2 : ℕ) : ℤ) ≤
        ((delta k * n : ℕ) : ℤ) := by exact_mod_cast hfloor
    calc
      2 * objective k C ≤ 2 * ((delta k * n / 2 : ℕ) : ℤ) := htwo
      _ ≤ ((delta k * n : ℕ) : ℤ) := hfloorZ
      _ = (n : ℤ) * (delta k : ℤ) := by push_cast; ring
  have hzDeltaReal : (delta k : ℝ) < (weightedDegree k C z : ℝ) := by
    have hscale : (delta k : ℝ) ≤
        8 * (delta k : ℝ) * (Real.sqrt δ * (n : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hrn8
        (show 0 ≤ 8 * (delta k : ℝ) by positivity)
      nlinarith
    exact hscale.trans_lt (by simpa [mul_assoc] using hz)
  have hzDelta : (delta k : ℤ) ≤ weightedDegree k C z := by
    exact_mod_cast hzDeltaReal.le
  let s := ⌊Real.sqrt δ * (n : ℝ)⌋₊
  have hsCard : s ≤ (Finset.univ.erase z).card := by
    have hslt : s < n := by simpa [s] using hsn
    simp only [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨U, hUerase, hUcard, hUsum⟩ :=
    exists_card_eq_sum_le_mul_erase z (weightedDegree k C) s (delta k : ℤ)
      hsCard (by simpa using htotal) hzDelta
  have hzU : z ∉ U := by
    intro hzmem
    exact (Finset.mem_erase.mp (hUerase hzmem)).1 rfl
  let psi := C.clone z U
  have hpsiC : psi ∈ Ck k n := by
    exact clone_mem_Ck hC hzU
  have hcloneZ := objective_clone_sub_lower_bound k C U hzU
  rw [hUcard] at hcloneZ
  have hcloneR :
      (s : ℝ) * (weightedDegree k C z : ℝ) -
          ((∑ u ∈ U, weightedDegree k C u : ℤ) : ℝ) -
          ((delta k : ℝ) + 1) * (s : ℝ) ^ 2 ≤
        (objective k psi : ℝ) - (objective k C : ℝ) := by
    dsimp only [psi]
    exact_mod_cast hcloneZ
  have hUsumR : ((∑ u ∈ U, weightedDegree k C u : ℤ) : ℝ) ≤
      (s : ℝ) * (delta k : ℝ) := by
    exact_mod_cast hUsum
  have hr2 : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ.le
  have hgainLower :
      4 * (delta k : ℝ) * δ * (n : ℝ) ^ 2 <
        (objective k psi : ℝ) - (objective k C : ℝ) := by
    apply cloneGain_gt hr hr2 hΔreal hnreal hrn8
    · simpa [s] using hslo
    · simpa [s] using hshi
    · exact hz
    · exact hUsumR
    · exact hcloneR
  have hpsiMantel := kthOrderMantel hk hpsiC
  have hpsiTwoZ : 2 * objective k psi ≤ ((delta k * n : ℕ) : ℤ) := by
    have htwo : 2 * objective k psi ≤
        2 * ((delta k * n / 2 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left hpsiMantel (by norm_num)
    have hfloor : 2 * (delta k * n / 2) ≤ delta k * n := by omega
    have hfloorZ : 2 * ((delta k * n / 2 : ℕ) : ℤ) ≤
        ((delta k * n : ℕ) : ℤ) := by exact_mod_cast hfloor
    exact htwo.trans hfloorZ
  have hpsiTwoR : 2 * (objective k psi : ℝ) ≤
      (delta k : ℝ) * (n : ℝ) := by exact_mod_cast hpsiTwoZ
  have hgainUpper :
      (objective k psi : ℝ) - (objective k C : ℝ) ≤
        (delta k : ℝ) * (n : ℝ) / 2 + δ * (n : ℝ) ^ 2 := by
    nlinarith
  exact (cloneGain_contradiction hδ hΔreal hnreal hΔn hgainLower hgainUpper) le_rfl

/-- The corrected exceptional-set estimate following from the upper tail and
the weighted handshake identity. -/
theorem weightedDegree_exceptional_card {k n : ℕ} (hk : 3 ≤ k) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {C : ColoredGraph (Fin n)}
    (hnear : -(δ * (n : ℝ) ^ 2) ≤ (objective k C : ℝ))
    (hn : 0 < n)
    (hupper : ∀ v, (weightedDegree k C v : ℝ) ≤
      8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ)) :
    let X := Finset.univ.filter fun v ↦
      -(δ ^ (1 / 4 : ℝ)) * (n : ℝ) ≤ (weightedDegree k C v : ℝ)
    (((Finset.univ \ X).card : ℕ) : ℝ) ≤
      10 * (delta k : ℝ) * δ ^ (1 / 4 : ℝ) * (n : ℝ) := by
  let q := δ ^ (1 / 4 : ℝ)
  let X : Finset (Fin n) := Finset.univ.filter fun v ↦
    -q * (n : ℝ) ≤ (weightedDegree k C v : ℝ)
  let Y : Finset (Fin n) := Finset.univ \ X
  change (Y.card : ℝ) ≤ 10 * (delta k : ℝ) * q * (n : ℝ)
  have hq0 : 0 < q := quarterPower_pos hδ0
  have hq1 : q ≤ 1 := quarterPower_le_one hδ0.le hδ1.le
  have hq2 : q ^ 2 = Real.sqrt δ := quarterPower_sq hδ0.le
  have hq4 : q ^ 4 = δ := quarterPower_fourth hδ0.le
  have hΔnat : 1 ≤ delta k := by
    unfold delta
    omega
  have hΔreal : (1 : ℝ) ≤ (delta k : ℝ) := by exact_mod_cast hΔnat
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hXsub : X ⊆ Finset.univ := Finset.subset_univ X
  have hsplit :
      ∑ v ∈ Y, (weightedDegree k C v : ℝ) +
          ∑ v ∈ X, (weightedDegree k C v : ℝ) =
        ∑ v, (weightedDegree k C v : ℝ) := by
    dsimp only [Y]
    exact Finset.sum_sdiff hXsub
  have hsumX :
      ∑ v ∈ X, (weightedDegree k C v : ℝ) ≤
        (X.card : ℝ) *
          (8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ)) := by
    calc
      ∑ v ∈ X, (weightedDegree k C v : ℝ) ≤
          ∑ _v ∈ X, 8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ) := by
        exact Finset.sum_le_sum fun v _hv ↦ hupper v
      _ = (X.card : ℝ) *
          (8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ)) := by simp
  have hsumY :
      ∑ v ∈ Y, (weightedDegree k C v : ℝ) ≤
        (Y.card : ℝ) * (-q * (n : ℝ)) := by
    calc
      ∑ v ∈ Y, (weightedDegree k C v : ℝ) ≤
          ∑ _v ∈ Y, -q * (n : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        have hvnot : v ∉ X := (Finset.mem_sdiff.mp hv).2
        have hvlt : (weightedDegree k C v : ℝ) < -q * (n : ℝ) := by
          simpa [X] using hvnot
        exact hvlt.le
      _ = (Y.card : ℝ) * (-q * (n : ℝ)) := by simp
  have hcardX : (X.card : ℝ) ≤ (n : ℝ) := by
    have hcardXnat : X.card ≤ n := by
      simpa using Finset.card_le_card hXsub
    exact_mod_cast hcardXnat
  have hcoeff : 0 ≤ 8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ) := by positivity
  have hsumUpper :
      ∑ v, (weightedDegree k C v : ℝ) ≤
        8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ) ^ 2 -
          (Y.card : ℝ) * q * (n : ℝ) := by
    have hXbound := mul_le_mul_of_nonneg_right hcardX hcoeff
    rw [← hsplit]
    calc
      ∑ v ∈ Y, (weightedDegree k C v : ℝ) +
          ∑ v ∈ X, (weightedDegree k C v : ℝ) ≤
        (Y.card : ℝ) * (-q * (n : ℝ)) +
          (X.card : ℝ) *
            (8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ)) :=
          add_le_add hsumY hsumX
      _ ≤ (Y.card : ℝ) * (-q * (n : ℝ)) +
          (n : ℝ) *
            (8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ)) :=
          add_le_add_right hXbound _
      _ = 8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ) ^ 2 -
          (Y.card : ℝ) * q * (n : ℝ) := by ring
  have hhandshakeZ := sum_weightedDegree_eq_two_mul_objective k C
  have hhandshakeR :
      ∑ v, (weightedDegree k C v : ℝ) = 2 * (objective k C : ℝ) := by
    exact_mod_cast hhandshakeZ
  have hsumLower :
      -(2 * δ * (n : ℝ) ^ 2) ≤
        ∑ v, (weightedDegree k C v : ℝ) := by
    rw [hhandshakeR]
    nlinarith
  have hcore :
      (Y.card : ℝ) * q * (n : ℝ) ≤
        2 * q ^ 4 * (n : ℝ) ^ 2 +
          8 * (delta k : ℝ) * q ^ 2 * (n : ℝ) ^ 2 := by
    rw [hq4, hq2]
    nlinarith
  exact exceptionalCard_le hq0 hq1 hΔreal hnreal hcore

/-- Restricted weighted degrees are uniformly small after deleting the
corrected exceptional set. -/
theorem weightedDegreeIn_goodSet_abs {k n : ℕ} (hk : 3 ≤ k) {δ : ℝ}
    (hδ0 : 0 < δ) {C : ColoredGraph (Fin n)}
    (hupper : ∀ v, (weightedDegree k C v : ℝ) ≤
      8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ))
    (hexceptional :
      let X := Finset.univ.filter fun v ↦
        -(δ ^ (1 / 4 : ℝ)) * (n : ℝ) ≤ (weightedDegree k C v : ℝ)
      (((Finset.univ \ X).card : ℕ) : ℝ) ≤
        10 * (delta k : ℝ) * δ ^ (1 / 4 : ℝ) * (n : ℝ)) :
    let X := Finset.univ.filter fun v ↦
      -(δ ^ (1 / 4 : ℝ)) * (n : ℝ) ≤ (weightedDegree k C v : ℝ)
    ∀ v ∈ X, |(weightedDegreeIn k C v X : ℝ)| ≤
      12 * (delta k : ℝ) ^ 2 * δ ^ (1 / 4 : ℝ) * (n : ℝ) := by
  let q := δ ^ (1 / 4 : ℝ)
  let X : Finset (Fin n) := Finset.univ.filter fun v ↦
    -q * (n : ℝ) ≤ (weightedDegree k C v : ℝ)
  change ∀ v ∈ X, |(weightedDegreeIn k C v X : ℝ)| ≤
    12 * (delta k : ℝ) ^ 2 * q * (n : ℝ)
  have hq0 : 0 < q := quarterPower_pos hδ0
  have hq2 : q ^ 2 = Real.sqrt δ := quarterPower_sq hδ0.le
  have hΔnat : 1 ≤ delta k := by
    unfold delta
    omega
  have hΔreal : (1 : ℝ) ≤ (delta k : ℝ) := by exact_mod_cast hΔnat
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hYcard : ((Xᶜ).card : ℝ) ≤
      10 * (delta k : ℝ) * q * (n : ℝ) := by
    simpa [X, q, Finset.compl_eq_univ_sdiff] using hexceptional
  intro v hv
  have hDlow : -q * (n : ℝ) ≤ (weightedDegree k C v : ℝ) := by
    simpa [X] using hv
  have hdecompZ := weightedDegreeIn_add_compl k C v X
  have hdecompR :
      (weightedDegreeIn k C v X : ℝ) +
          (weightedDegreeIn k C v Xᶜ : ℝ) =
        (weightedDegree k C v : ℝ) := by
    exact_mod_cast hdecompZ
  have houtUpperZ := weightedDegreeIn_le_card k C v Xᶜ
  have houtUpper : (weightedDegreeIn k C v Xᶜ : ℝ) ≤ ((Xᶜ).card : ℝ) := by
    exact_mod_cast houtUpperZ
  have houtLowerZ := neg_delta_mul_card_le_weightedDegreeIn k C v Xᶜ
  have houtLower :
      -(delta k : ℝ) * ((Xᶜ).card : ℝ) ≤
        (weightedDegreeIn k C v Xᶜ : ℝ) := by
    exact_mod_cast houtLowerZ
  have hlowerRaw :
      -q * (n : ℝ) - ((Xᶜ).card : ℝ) ≤
        (weightedDegreeIn k C v X : ℝ) := by
    nlinarith
  have hlower :
      -(12 * (delta k : ℝ) ^ 2 * q * (n : ℝ)) ≤
        (weightedDegreeIn k C v X : ℝ) :=
    restrictedWeightedDegree_lower hq0 hΔreal hnnonneg hlowerRaw hYcard
  have hupperRaw :
      (weightedDegreeIn k C v X : ℝ) ≤
        8 * (delta k : ℝ) * q ^ 2 * (n : ℝ) +
          (delta k : ℝ) * ((Xᶜ).card : ℝ) := by
    have hvUpper := hupper v
    rw [hq2]
    nlinarith
  have hrestrictedUpper :
      (weightedDegreeIn k C v X : ℝ) ≤
        12 * (delta k : ℝ) ^ 2 * q * (n : ℝ) := by
    by_cases hqsmall : q ≤ 1 / 4
    · exact restrictedWeightedDegree_upper_of_quarterPower_le hq0 hqsmall hΔreal
        hnnonneg hupperRaw hYcard
    · have hqlarge : 1 / 4 < q := lt_of_not_ge hqsmall
      have hXin : X.card ≤ n := by
        simpa using Finset.card_le_card (Finset.subset_univ X)
      have htrivialZ := weightedDegreeIn_le_card k C v X
      have htrivial : (weightedDegreeIn k C v X : ℝ) ≤ (n : ℝ) := by
        have htrivialR : (weightedDegreeIn k C v X : ℝ) ≤ (X.card : ℝ) := by
          exact_mod_cast htrivialZ
        have hXinR : (X.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hXin
        exact htrivialR.trans hXinR
      exact restrictedWeightedDegree_upper_of_quarterPower_large hqlarge hΔreal
        hnnonneg htrivial
  exact (abs_le).2 ⟨hlower, hrestrictedUpper⟩

/-- Weighted-degree tails for near-extremal forbidden-pattern-free colorings.

The exceptional set has size at most `10 * Δ * δ^(1/4) * n`. The
restricted-degree conclusion has constant `12 * Δ^2`, obtained by the
small/large fourth-root split.

Paper: Lemma `lemma:D-tails`.
-/
theorem weightedDegreeTails (k : ℕ) (hk : 3 ≤ k) (δ : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
      -(δ * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
      let X := Finset.univ.filter fun v ↦
        -(δ ^ (1 / 4 : ℝ)) * (n : ℝ) ≤ (weightedDegree k C v : ℝ)
      (∀ v, (weightedDegree k C v : ℝ) ≤
          8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ)) ∧
        (((Finset.univ \ X).card : ℕ) : ℝ) ≤
          10 * (delta k : ℝ) * δ ^ (1 / 4 : ℝ) * (n : ℝ) ∧
        ∀ v ∈ X, |(weightedDegreeIn k C v X : ℝ)| ≤
          12 * (delta k : ℝ) ^ 2 * δ ^ (1 / 4 : ℝ) * (n : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := exists_tailThreshold δ hδ.1 hδ.2 (delta k)
  refine ⟨n₀, ?_⟩
  intro n hn C hC hnear
  obtain ⟨hrn8, hΔn, hslo, hshi, hsn⟩ := hn₀ n hn
  have hnpos : 0 < n := by omega
  have hupper : ∀ v, (weightedDegree k C v : ℝ) ≤
      8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ) :=
    weightedDegree_le_eight_sqrt hk hδ.1 hC hnear hrn8 hΔn hslo hshi hsn
  let X : Finset (Fin n) := Finset.univ.filter fun v ↦
    -(δ ^ (1 / 4 : ℝ)) * (n : ℝ) ≤ (weightedDegree k C v : ℝ)
  change (∀ v, (weightedDegree k C v : ℝ) ≤
      8 * (delta k : ℝ) * Real.sqrt δ * (n : ℝ)) ∧
    (((Finset.univ \ X).card : ℕ) : ℝ) ≤
      10 * (delta k : ℝ) * δ ^ (1 / 4 : ℝ) * (n : ℝ) ∧
    ∀ v ∈ X, |(weightedDegreeIn k C v X : ℝ)| ≤
      12 * (delta k : ℝ) ^ 2 * δ ^ (1 / 4 : ℝ) * (n : ℝ)
  have hexceptional : (((Finset.univ \ X).card : ℕ) : ℝ) ≤
      10 * (delta k : ℝ) * δ ^ (1 / 4 : ℝ) * (n : ℝ) := by
    simpa [X] using
      weightedDegree_exceptional_card hk hδ.1 hδ.2 hnear hnpos hupper
  have hrestricted : ∀ v ∈ X, |(weightedDegreeIn k C v X : ℝ)| ≤
      12 * (delta k : ℝ) ^ 2 * δ ^ (1 / 4 : ℝ) * (n : ℝ) := by
    simpa [X] using
      weightedDegreeIn_goodSet_abs hk hδ.1 hupper (by simpa [X] using hexceptional)
  exact ⟨hupper, hexceptional, hrestricted⟩

/-! ## Local near-Turán structure -/

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev redGreenNeighborhoodGraph (C : ColoredGraph V) (x : V) :
    SimpleGraph {v // v ∈ C.redNeighborFinset x} :=
  (C.blueGraph.induce (C.redNeighborFinset x : Set V))ᶜ

@[simp] theorem redGreenNeighborhoodGraph_adj (C : ColoredGraph V) (x : V)
    (u v : {v // v ∈ C.redNeighborFinset x}) :
    (redGreenNeighborhoodGraph C x).Adj u v ↔
      u ≠ v ∧ C.color u v ≠ .blue := by
  change ((C.blueGraph.induce (C.redNeighborFinset x : Set V))ᶜ).Adj u v ↔ _
  rw [SimpleGraph.compl_adj]
  change u ≠ v ∧ ¬(C.blueGraph.Adj (u : V) (v : V)) ↔
    u ≠ v ∧ C.color (u : V) (v : V) ≠ .blue
  constructor
  · rintro ⟨huv, hnblue⟩
    refine ⟨huv, ?_⟩
    intro hblue
    apply hnblue
    exact (C.colorGraph_adj .blue u v).2
      ⟨fun huv' ↦ huv (Subtype.ext huv'), hblue⟩
  · rintro ⟨huv, hnblue⟩
    refine ⟨huv, ?_⟩
    intro hadj
    exact hnblue ((C.colorGraph_adj .blue u v).1 hadj).2

@[simp] theorem card_redNeighborhood (C : ColoredGraph V) (x : V) :
    Fintype.card {v // v ∈ C.redNeighborFinset x} = C.redDegree x := by
  change Fintype.card ↥(C.redNeighborFinset x) = #(C.redNeighborFinset x)
  exact Fintype.card_coe _

theorem redGreenNeighborhoodGraph_cliqueFree {k : ℕ} (hk : 4 ≤ k)
    {C : ColoredGraph V} (hC : C.FkFree k) (x : V) :
    (redGreenNeighborhoodGraph C x).CliqueFree (delta k + 1) := by
  classical
  intro t ht
  let emb : {v // v ∈ C.redNeighborFinset x} ↪ V := Function.Embedding.subtype _
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

theorem card_graph_add_compl (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset + #Gᶜ.edgeFinset = (Fintype.card V).choose 2 := by
  classical
  have hdisj : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    rw [SimpleGraph.disjoint_edgeFinset]
    exact disjoint_compl_right
  have hunion : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset]
        constructor
        · rintro (huv | ⟨hne, _⟩)
          · exact G.ne_of_adj huv
          · exact hne
        · intro hne
          by_cases huv : G.Adj u v
          · exact Or.inl huv
          · exact Or.inr ⟨hne, huv⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

theorem blueInduce_add_redGreenNeighborhood (C : ColoredGraph V) (x : V) :
    #((C.blueGraph.induce (C.redNeighborFinset x : Set V)).edgeFinset) +
        #(redGreenNeighborhoodGraph C x).edgeFinset =
      (C.redDegree x).choose 2 := by
  have h := card_graph_add_compl
    (C.blueGraph.induce (C.redNeighborFinset x : Set V))
  have hcard : Fintype.card {v // v ∈ (C.redNeighborFinset x : Set V)} =
      C.redDegree x := by
    calc
      _ = Fintype.card ↥(C.redNeighborFinset x) :=
        Fintype.card_congr (Equiv.refl _)
      _ = #(C.redNeighborFinset x) := Fintype.card_coe _
      _ = C.redDegree x := rfl
  rw [hcard] at h
  exact h

theorem redGreenNeighborhood_edge_le_turan {k : ℕ} (hk : 4 ≤ k)
    {C : ColoredGraph V} (hC : C.FkFree k) (x : V) :
    #(redGreenNeighborhoodGraph C x).edgeFinset ≤
      SimpleGraph.turanNumber (C.redDegree x) (delta k) := by
  have h := (redGreenNeighborhoodGraph_cliqueFree hk hC x).card_edgeFinset_le
  rw [card_redNeighborhood C x] at h
  exact h

theorem blueInduce_degree_le (C : ColoredGraph V) (x : V)
    (v : {v // v ∈ C.redNeighborFinset x}) :
    (C.blueGraph.induce (C.redNeighborFinset x : Set V)).degree v ≤
      C.blueDegree v := by
  classical
  let emb : {v // v ∈ C.redNeighborFinset x} ↪ V := Function.Embedding.subtype _
  have hsub :
      ((C.blueGraph.induce (C.redNeighborFinset x : Set V)).neighborFinset v).map emb ⊆
        C.blueGraph.neighborFinset v := by
    intro y hy
    rcases Finset.mem_map.mp hy with ⟨u, hu, huy⟩
    subst y
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact hu
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map] at hcard
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,
    ColoredGraph.degree, ColoredGraph.neighborFinset] using hcard

theorem highSet_card {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (a ρ : ℝ)
    (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (haρ : a + ρ < 1)
    (hone : 1 ≤ ρ * (Fintype.card ι : ℝ) * (a + ρ))
    (hf : ∀ i, f i ≤ (Fintype.card ι : ℝ))
    (hsum : (Fintype.card ι : ℝ) ^ 2 * a - (Fintype.card ι : ℝ) +
        2 * ρ * (Fintype.card ι : ℝ) ^ 2 ≤ ∑ i, f i) :
    ρ * (Fintype.card ι : ℝ) ≤
      (((Finset.univ.filter fun i ↦ (a + ρ) * (Fintype.card ι : ℝ) ≤ f i).card : ℕ) : ℝ) := by
  classical
  let M : ℝ := Fintype.card ι
  let B : Finset ι := Finset.univ.filter fun i ↦ (a + ρ) * M ≤ f i
  let N : Finset ι := Finset.univ.filter fun i ↦ ¬((a + ρ) * M ≤ f i)
  change 1 ≤ ρ * M * (a + ρ) at hone
  change ρ * M ≤ (B.card : ℝ)
  by_contra hnot
  have hb : (B.card : ℝ) < ρ * M := lt_of_not_ge hnot
  have hsumB : ∑ i ∈ B, f i ≤ (B.card : ℝ) * M := by
    calc
      ∑ i ∈ B, f i ≤ ∑ _i ∈ B, M :=
        Finset.sum_le_sum fun i _hi ↦ by simpa [M] using hf i
      _ = (B.card : ℝ) * M := by simp
  have hsumN : ∑ i ∈ N, f i ≤ (N.card : ℝ) * ((a + ρ) * M) := by
    calc
      ∑ i ∈ N, f i ≤ ∑ _i ∈ N, (a + ρ) * M := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : ¬((a + ρ) * M ≤ f i) := by simpa [N] using hi
        exact (lt_of_not_ge hi').le
      _ = (N.card : ℝ) * ((a + ρ) * M) := by simp
  have hsplit : (∑ i ∈ B, f i) + ∑ i ∈ N, f i = ∑ i, f i := by
    simpa [B, N] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i ↦ (a + ρ) * M ≤ f i) f)
  have hcardsNat : B.card + N.card = Fintype.card ι := by
    simpa [B, N] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i ↦ (a + ρ) * M ≤ f i))
  have hcards : (B.card : ℝ) + (N.card : ℝ) = M := by
    have h := congrArg (fun q : ℕ ↦ (q : ℝ)) hcardsNat
    push_cast at h
    exact h
  have hsumUpper : ∑ i, f i ≤
      (B.card : ℝ) * M + (N.card : ℝ) * ((a + ρ) * M) := by
    rw [← hsplit]
    exact add_le_add hsumB hsumN
  have hc : 0 < 1 - a - ρ := by linarith
  have hM : 0 < M := by
    have hprod : 0 < ρ * M * (a + ρ) := lt_of_lt_of_le (by norm_num) hone
    by_contra hMn
    have : M ≤ 0 := le_of_not_gt hMn
    have hρM : ρ * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ this
    have haρ0 : 0 ≤ a + ρ := add_nonneg ha hρ
    have : ρ * M * (a + ρ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hρM haρ0
    linarith
  have hbscaled := mul_lt_mul_of_pos_right hb (mul_pos hM hc)
  have honeM := mul_le_mul_of_nonneg_right hone hM.le
  rw [show (Fintype.card ι : ℝ) = M by rfl] at hsum
  nlinarith [hbscaled, honeM]

theorem turan_missing_lower {m r : ℕ} (hr : 0 < r) :
    (m : ℝ) ^ 2 / (2 * (r : ℝ)) - (m : ℝ) / 2 ≤
      (m.choose 2 : ℝ) - (SimpleGraph.turanNumber m r : ℝ) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have htNat := SimpleGraph.mul_turanNumber_le (n := m) (r := r)
  have htCast : ((2 * r * SimpleGraph.turanNumber m r : ℕ) : ℝ) ≤
      (((r - 1) * m ^ 2 : ℕ) : ℝ) := by exact_mod_cast htNat
  have ht : 2 * (r : ℝ) * (SimpleGraph.turanNumber m r : ℝ) ≤
      ((r : ℝ) - 1) * (m : ℝ) ^ 2 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ r)] at htCast
    exact htCast
  have hmchoose : (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    simpa using (Nat.cast_choose_two (K := ℝ) m)
  rw [hmchoose]
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrR
  field_simp
  nlinarith

theorem exists_weightedDegree_ge_neg_two_sqrt {k n : ℕ} {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hn : 0 < n)
    {C : ColoredGraph (Fin n)}
    (hobj : -(δ * (n : ℝ) ^ 2) ≤ (objective k C : ℝ)) :
    ∃ z : Fin n,
      -(2 * Real.sqrt δ * (n : ℝ)) ≤ (weightedDegree k C z : ℝ) := by
  classical
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ < 1 := hδ.2
  have hδsq : δ ^ 2 < δ := by
    nlinarith [mul_pos hδ0 (sub_pos.mpr hδ1)]
  have hδsqrt : δ < Real.sqrt δ :=
    (Real.lt_sqrt (le_of_lt hδ0)).2 hδsq
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  let z₀ : Fin n := ⟨0, hn⟩
  have hsumlt :
      (∑ z : Fin n, (weightedDegree k C z : ℝ)) <
        ∑ _z : Fin n, -(2 * Real.sqrt δ * (n : ℝ)) := by
    exact Finset.sum_lt_sum_of_nonempty ⟨z₀, Finset.mem_univ z₀⟩
      fun z _ ↦ hnone z
  have hhandshake :
      (∑ z : Fin n, (weightedDegree k C z : ℝ)) =
        2 * (objective k C : ℝ) := by
    exact_mod_cast sum_weightedDegree_eq_two_mul_objective k C
  rw [hhandshake] at hsumlt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumlt
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqpos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  nlinarith

/-- Exact lower and upper bounds for the natural floor used for the clone-set
size `s = floor (R / 16)`. -/
theorem natFloor_div_sixteen_bounds {R : ℝ} (hR : 0 ≤ R) :
    R / 16 - 1 < ((⌊R / 16⌋₊ : ℕ) : ℝ) ∧
      ((⌊R / 16⌋₊ : ℕ) : ℝ) ≤ R / 16 := by
  constructor
  · exact Nat.sub_one_lt_floor (R / 16)
  · exact Nat.floor_le (div_nonneg hR (by norm_num))

/-- Once `R ≥ 32`, flooring `R / 16` loses at most a factor of two. -/
theorem half_div_sixteen_le_natFloor {R : ℝ} (hR : 32 ≤ R) :
    R / 32 ≤ ((⌊R / 16⌋₊ : ℕ) : ℝ) := by
  have hlo := (natFloor_div_sixteen_bounds (by linarith : 0 ≤ R)).1
  linarith

/-- The floor-sensitive scalar core of the local near-Turán cloning estimate.
Here `R` abbreviates `ρ m`, and `q` will be `sqrt δ`. -/
theorem cloneGain_gt_R_sq_div_thirtyTwo
    {q α Δ n R : ℝ} (hq : 0 ≤ q) (hα : 0 ≤ α) (hΔ : 2 ≤ Δ)
    (hn : 0 ≤ n) (hRlarge : 32 ≤ R)
    (hRlower : 12 * (q + α) * n < R) :
    let s := ⌊R / 16⌋₊
    R ^ 2 / 32 <
      -(2 * (s : ℝ) * q * n) + (s : ℝ) * Δ * R -
        (s : ℝ) * α * n - (Δ + 1) * (s : ℝ) ^ 2 := by
  let s : ℝ := ((⌊R / 16⌋₊ : ℕ) : ℝ)
  change R ^ 2 / 32 <
    -(2 * s * q * n) + s * Δ * R - s * α * n - (Δ + 1) * s ^ 2
  have hR0 : 0 ≤ R := by linarith
  have hs0 : 0 ≤ s := by positivity
  have hslo : R / 32 ≤ s := half_div_sixteen_le_natFloor hRlarge
  have hshi : s ≤ R / 16 :=
    (natFloor_div_sixteen_bounds hR0).2
  have hweighted0 : 0 ≤ Δ * R := mul_nonneg (by linarith) hR0
  have hmain : (R / 32) * (Δ * R) ≤ s * (Δ * R) :=
    mul_le_mul_of_nonneg_right hslo hweighted0
  have herrorFactor0 : 0 ≤ (2 * q + α) * n := by positivity
  have herrorFactor : (2 * q + α) * n < R / 6 := by
    nlinarith [mul_nonneg hα hn]
  have herror₁ : s * ((2 * q + α) * n) ≤
      (R / 16) * ((2 * q + α) * n) :=
    mul_le_mul_of_nonneg_right hshi herrorFactor0
  have hRdivPos : 0 < R / 16 := by positivity
  have herror₂ : (R / 16) * ((2 * q + α) * n) <
      (R / 16) * (R / 6) :=
    mul_lt_mul_of_pos_left herrorFactor hRdivPos
  have herror : s * ((2 * q + α) * n) < R ^ 2 / 96 := by
    calc
      s * ((2 * q + α) * n) ≤
          (R / 16) * ((2 * q + α) * n) := herror₁
      _ < (R / 16) * (R / 6) := herror₂
      _ = R ^ 2 / 96 := by ring
  have hs2 : s ^ 2 ≤ (R / 16) ^ 2 :=
    (sq_le_sq₀ hs0 (by positivity : 0 ≤ R / 16)).2 hshi
  have hpenalty : (Δ + 1) * s ^ 2 ≤ (Δ + 1) * (R ^ 2 / 256) := by
    have := mul_le_mul_of_nonneg_left hs2 (by linarith : 0 ≤ Δ + 1)
    calc
      (Δ + 1) * s ^ 2 ≤ (Δ + 1) * (R / 16) ^ 2 := this
      _ = (Δ + 1) * (R ^ 2 / 256) := by ring
  have hcoefficient :
      R ^ 2 / 32 ≤
        Δ * R ^ 2 / 32 - R ^ 2 / 96 - (Δ + 1) * (R ^ 2 / 256) := by
    have hprod : 0 ≤ (Δ - 2) * R ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg R)
    nlinarith
  nlinarith

/-- A directly consumable cloning-gain estimate.  The last two hypotheses are
explicit large-`n` conditions: the first absorbs the floor, and the second
absorbs the exact linear Mantel bound. -/
theorem cloneGain_gt_mantel_threshold
    {δ α Δ n R : ℝ} (hδ : 0 < δ) (hα : 0 ≤ α) (hΔ : 2 ≤ Δ)
    (hRrange : R ∈ Set.Icc (0 : ℝ) (n / 2))
    (hRlower : 12 * (Real.sqrt δ + α) * n < R)
    (hnFloor : 32 ≤ 12 * Real.sqrt δ * n)
    (hnLinear : Δ < 7 * δ * n) :
    let s := ⌊R / 16⌋₊
    δ * n ^ 2 + Δ * n / 2 <
      -(2 * (s : ℝ) * Real.sqrt δ * n) + (s : ℝ) * Δ * R -
        (s : ℝ) * α * n - (Δ + 1) * (s : ℝ) ^ 2 := by
  have hR0 : 0 ≤ R := hRrange.1
  have hRupper : R ≤ n / 2 := hRrange.2
  have hn : 0 ≤ n := by nlinarith
  have hq : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hRlarge : 32 ≤ R := by
    have hmiddle : 12 * Real.sqrt δ * n ≤
        12 * (Real.sqrt δ + α) * n := by
      nlinarith [mul_nonneg hα hn]
    exact hnFloor.trans (hmiddle.trans hRlower.le)
  have hcore := cloneGain_gt_R_sq_div_thirtyTwo
    hq hα hΔ hn hRlarge hRlower
  have hsqrtSq : (Real.sqrt δ) ^ 2 = δ :=
    Real.sq_sqrt (le_of_lt hδ)
  have hsmallLower : 12 * Real.sqrt δ * n < R := by
    nlinarith [mul_nonneg hα hn]
  have hsmallLower0 : 0 ≤ 12 * Real.sqrt δ * n := by positivity
  have hR2 : (12 * Real.sqrt δ * n) ^ 2 < R ^ 2 :=
    (sq_lt_sq₀ hsmallLower0 hR0).2 hsmallLower
  have hquadratic : (9 / 2 : ℝ) * δ * n ^ 2 < R ^ 2 / 32 := by
    nlinarith
  have hnpos : 0 < n := by
    have hsqrtpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    nlinarith
  have hlinear : Δ * n / 2 < (7 / 2 : ℝ) * δ * n ^ 2 := by
    have hmul := mul_lt_mul_of_pos_right hnLinear hnpos
    nlinarith
  exact lt_trans (by nlinarith) hcore

/-- The preceding estimate with a single explicit threshold for `n`. -/
theorem cloneGain_gt_mantel_explicit
    {δ α Δ n R : ℝ} (hδ : 0 < δ) (hα : 0 ≤ α) (hΔ : 2 ≤ Δ)
    (hRrange : R ∈ Set.Icc (0 : ℝ) (n / 2))
    (hRlower : 12 * (Real.sqrt δ + α) * n < R)
    (hnLarge :
      max (8 / (3 * Real.sqrt δ)) (Δ / (7 * δ)) < n) :
    let s := ⌊R / 16⌋₊
    δ * n ^ 2 + Δ * n / 2 <
      -(2 * (s : ℝ) * Real.sqrt δ * n) + (s : ℝ) * Δ * R -
        (s : ℝ) * α * n - (Δ + 1) * (s : ℝ) ^ 2 := by
  have hsqrtpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hnFloorRaw : 8 / (3 * Real.sqrt δ) < n :=
    (max_lt_iff.mp hnLarge).1
  have hnLinearRaw : Δ / (7 * δ) < n :=
    (max_lt_iff.mp hnLarge).2
  have hnFloor : 32 ≤ 12 * Real.sqrt δ * n := by
    have hden : 0 < 3 * Real.sqrt δ := by positivity
    have := (div_lt_iff₀ hden).mp hnFloorRaw
    nlinarith
  have hnLinear : Δ < 7 * δ * n := by
    have hden : 0 < 7 * δ := by positivity
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_lt_iff₀ hden).mp hnLinearRaw
  exact cloneGain_gt_mantel_threshold hδ hα hΔ hRrange hRlower
    hnFloor hnLinear

/-- Choose the floor-sized clone set while avoiding one prescribed vertex. -/
theorem exists_cloneSet {ι : Type*}
    (B : Finset ι) (z : ι) {R : ℝ}
    (hR : 32 ≤ R) (hBR : R ≤ (B.card : ℝ)) :
    ∃ W : Finset ι,
      W ⊆ B ∧ z ∉ W ∧ W.card = ⌊R / 16⌋₊ := by
  classical
  have hR0 : 0 ≤ R := by linarith
  have hBpos : 1 ≤ B.card := by
    have hBcast : (1 : ℝ) ≤ (B.card : ℝ) := by linarith
    exact_mod_cast hBcast
  have hpredCast : ((B.card - 1 : ℕ) : ℝ) = (B.card : ℝ) - 1 := by
    rw [Nat.cast_sub hBpos, Nat.cast_one]
  have heraseCast : R - 1 ≤ ((B.erase z).card : ℝ) := by
    have hpred : B.card - 1 ≤ (B.erase z).card := Finset.pred_card_le_card_erase
    have hpred' : ((B.card - 1 : ℕ) : ℝ) ≤
        ((B.erase z).card : ℝ) := by exact_mod_cast hpred
    rw [hpredCast] at hpred'
    linarith
  have hsCast : ((⌊R / 16⌋₊ : ℕ) : ℝ) ≤
      ((B.erase z).card : ℝ) := by
    have hfloor : ((⌊R / 16⌋₊ : ℕ) : ℝ) ≤ R / 16 :=
      Nat.floor_le (div_nonneg hR0 (by norm_num))
    have hdiv : R / 16 ≤ R - 1 := by linarith
    exact hfloor.trans (hdiv.trans heraseCast)
  have hs : ⌊R / 16⌋₊ ≤ (B.erase z).card := by
    exact_mod_cast hsCast
  obtain ⟨W, hWerase, hWcard⟩ := (B.erase z).exists_subset_card_eq hs
  refine ⟨W, hWerase.trans (Finset.erase_subset z B), ?_, hWcard⟩
  intro hzW
  have : z ∈ B.erase z := hWerase hzW
  exact (Finset.mem_erase.mp this).1 rfl

/-- A single threshold for the floor-sensitive part of the local Turan proof. -/
theorem exists_localTuranThreshold (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      0 < n ∧
      max (8 / (3 * Real.sqrt δ)) ((delta k : ℝ) / (7 * δ)) < (n : ℝ) ∧
      (delta k : ℝ) < 12 * Real.sqrt δ * (n : ℝ) := by
  let M : ℝ := max 1 <|
    max (8 / (3 * Real.sqrt δ)) <|
      max ((delta k : ℝ) / (7 * δ)) ((delta k : ℝ) / (12 * Real.sqrt δ))
  refine ⟨Nat.floor M + 1, ?_⟩
  intro n hn
  have hMlt : M < (n : ℝ) := by
    have hfloor : M < ((Nat.floor M + 1 : ℕ) : ℝ) := by
      have hM0 : 0 ≤ M := le_trans (by norm_num) (le_max_left 1 _)
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one M
    have hcast : ((Nat.floor M + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact hfloor.trans_le hcast
  have hn1 : (1 : ℝ) < n := (le_max_left 1 _).trans_lt hMlt
  have hfloorRaw : 8 / (3 * Real.sqrt δ) < n :=
    ((le_max_left _ _).trans (le_max_right 1 _)).trans_lt hMlt
  have hlinearRaw : (delta k : ℝ) / (7 * δ) < n :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right 1 _)).trans_lt hMlt
  have hdeltaRaw : (delta k : ℝ) / (12 * Real.sqrt δ) < n :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right 1 _)).trans_lt hMlt
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hdelta : (delta k : ℝ) < 12 * Real.sqrt δ * n := by
    have hden : 0 < 12 * Real.sqrt δ := by positivity
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_lt_iff₀ hden).mp hdeltaRaw
  exact ⟨by exact_mod_cast (show (0 : ℝ) < n by linarith),
    (max_lt_iff.mpr ⟨hfloorRaw, hlinearRaw⟩), hdelta⟩

/-- The averaging step that extracts many vertices of excess blue degree
inside a red neighborhood. -/
theorem localBlueHighSet_card {k : ℕ} (hk : 4 ≤ k)
    {V : Type*} [Fintype V] [DecidableEq V] (C : ColoredGraph V) (x : V)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρhalf : ρ < 1 / 2)
    (hρdef :
      ρ * (C.redDegree x : ℝ) ^ 2 =
        (SimpleGraph.turanNumber (C.redDegree x) (delta k) : ℝ) -
          (#(redGreenNeighborhoodGraph C x).edgeFinset : ℝ))
    (hone : 1 ≤ ρ * (C.redDegree x : ℝ) *
      (1 / (delta k : ℝ) + ρ)) :
    ρ * (C.redDegree x : ℝ) ≤
      (((Finset.univ.filter fun
          v : {v // v ∈ (C.redNeighborFinset x : Set V)} ↦
            (1 / (delta k : ℝ) + ρ) * (C.redDegree x : ℝ) ≤
              ((C.blueGraph.induce
                (C.redNeighborFinset x : Set V)).degree v : ℝ)).card : ℕ) : ℝ) := by
  classical
  let G := C.blueGraph.induce (C.redNeighborFinset x : Set V)
  have hΔnat : 0 < delta k := by
    unfold delta
    omega
  have hΔR : (0 : ℝ) < (delta k : ℝ) := by exact_mod_cast hΔnat
  have hcard :
      Fintype.card {v // v ∈ (C.redNeighborFinset x : Set V)} = C.redDegree x := by
    calc
      _ = Fintype.card ↥(C.redNeighborFinset x) :=
        Fintype.card_congr (Equiv.refl _)
      _ = #(C.redNeighborFinset x) := Fintype.card_coe _
      _ = C.redDegree x := rfl
  have hcompNat := blueInduce_add_redGreenNeighborhood C x
  have hcomp : (#G.edgeFinset : ℝ) =
      (C.redDegree x).choose 2 -
        (#(redGreenNeighborhoodGraph C x).edgeFinset : ℝ) := by
    have h := congrArg (fun q : ℕ ↦ (q : ℝ)) hcompNat
    push_cast at h
    dsimp only [G]
    linarith
  have hmissing := turan_missing_lower
    (m := C.redDegree x) (r := delta k) hΔnat
  have hdegreeNat := G.sum_degrees_eq_twice_card_edges
  have hdegree : (∑ v, (G.degree v : ℝ)) = 2 * (#G.edgeFinset : ℝ) := by
    exact_mod_cast hdegreeNat
  have hsum : (C.redDegree x : ℝ) ^ 2 * (1 / (delta k : ℝ)) -
        (C.redDegree x : ℝ) + 2 * ρ * (C.redDegree x : ℝ) ^ 2 ≤
      ∑ v, (G.degree v : ℝ) := by
    rw [hdegree, hcomp]
    have hdiv : (C.redDegree x : ℝ) ^ 2 * (1 / (delta k : ℝ)) =
        2 * ((C.redDegree x : ℝ) ^ 2 / (2 * (delta k : ℝ))) := by
      field_simp
    nlinarith [hmissing, hρdef, hdiv]
  have ha : 0 ≤ (1 / (delta k : ℝ)) := by positivity
  have haρ : 1 / (delta k : ℝ) + ρ < 1 := by
    have hΔtwo : (2 : ℝ) ≤ (delta k : ℝ) := by
      exact_mod_cast (show 2 ≤ delta k by unfold delta; omega)
    have hinv : 1 / (delta k : ℝ) ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num) hΔtwo
    linarith
  have hf : ∀ v : {v // v ∈ (C.redNeighborFinset x : Set V)},
      (G.degree v : ℝ) ≤
        (Fintype.card {v // v ∈ (C.redNeighborFinset x : Set V)} : ℝ) := by
    intro v
    exact_mod_cast (G.degree_lt_card_verts v).le
  have hcardR :
      (Fintype.card {v // v ∈ (C.redNeighborFinset x : Set V)} : ℝ) =
        (C.redDegree x : ℝ) := by
    exact_mod_cast hcard
  have hone' : 1 ≤ ρ *
      (Fintype.card {v // v ∈ (C.redNeighborFinset x : Set V)} : ℝ) *
        (1 / (delta k : ℝ) + ρ) := by
    rw [hcardR]
    exact hone
  have hsum' :
      (Fintype.card {v // v ∈ (C.redNeighborFinset x : Set V)} : ℝ) ^ 2 *
          (1 / (delta k : ℝ)) -
        (Fintype.card {v // v ∈ (C.redNeighborFinset x : Set V)} : ℝ) +
          2 * ρ *
            (Fintype.card {v // v ∈ (C.redNeighborFinset x : Set V)} : ℝ) ^ 2 ≤
        ∑ v, (G.degree v : ℝ) := by
    rw [hcardR]
    exact hsum
  have hhigh := highSet_card
    (f := fun v : {v // v ∈ (C.redNeighborFinset x : Set V)} ↦ (G.degree v : ℝ))
    (a := 1 / (delta k : ℝ)) (ρ := ρ) ha hρ0 haρ hone' hf hsum'
  rw [hcardR] at hhigh
  exact hhigh

set_option maxHeartbeats 2000000 in
-- The combined coercion-heavy Turán/cloning argument exceeds the default cap.

/-- Large-`n` core of the local near-Turán estimate. -/
theorem locallyTuran_core {k n : ℕ} (hk : 4 ≤ k)
    {δ α θ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Ioc (0 : ℝ) 1)
    {C : ColoredGraph (Fin n)} (hC : C ∈ Ck k n)
    (hnear : -(δ * (n : ℝ) ^ 2) ≤ (objective k C : ℝ))
    (x : Fin n)
    (hmax : ∀ v : Fin n,
      (C.redDegree v : ℝ) ≤ (C.redDegree x : ℝ) + α * (n : ℝ))
    (hmθ : θ * (n : ℝ) ≤ (C.redDegree x : ℝ))
    (hnLarge :
      max (8 / (3 * Real.sqrt δ)) ((delta k : ℝ) / (7 * δ)) < (n : ℝ)) :
    (SimpleGraph.turanNumber (C.redDegree x) (delta k) : ℝ) -
        12 * (Real.sqrt δ / θ + α / θ) * (C.redDegree x : ℝ) ^ 2 ≤
      (#(redGreenNeighborhoodGraph C x).edgeFinset : ℝ) := by
  classical
  let A := {v // v ∈ C.redNeighborFinset x}
  let G : SimpleGraph A :=
    C.blueGraph.induce (C.redNeighborFinset x : Set (Fin n))
  let m : ℕ := C.redDegree x
  let Δ : ℕ := delta k
  let t : ℕ := SimpleGraph.turanNumber m Δ
  let e : ℕ := #(redGreenNeighborhoodGraph C x).edgeFinset
  let ρ : ℝ := ((t : ℝ) - (e : ℝ)) / (m : ℝ) ^ 2
  let R : ℝ := ρ * (m : ℝ)
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ < 1 := hδ.2
  have hα0 : 0 ≤ α := hα.1
  have hθ0 : 0 < θ := hθ.1
  have hq0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hqpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hΔnat : 2 ≤ Δ := by
    dsimp [Δ, delta]
    omega
  have hΔpos : 0 < Δ := by omega
  have hΔR : (2 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔnat
  have het : e ≤ t := by
    dsimp [e, t, m, Δ]
    exact redGreenNeighborhood_edge_le_turan hk hC x
  have hnR : 0 < (n : ℝ) := by
    have hfirst : 0 < 8 / (3 * Real.sqrt δ) := by positivity
    have := (max_lt_iff.mp hnLarge).1
    linarith
  have hn : 0 < n := by exact_mod_cast hnR
  have hmR : 0 < (m : ℝ) := by
    have : 0 < θ * (n : ℝ) := mul_pos hθ0 hnR
    dsimp [m]
    linarith
  have hm : 0 < m := by exact_mod_cast hmR
  have hm2 : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hmR
  have hρnonneg : 0 ≤ ρ := by
    have hetR : (e : ℝ) ≤ (t : ℝ) := by exact_mod_cast het
    dsimp [ρ]
    exact div_nonneg (sub_nonneg.mpr hetR) (sq_nonneg _)
  by_contra hgoal
  have hbad : (e : ℝ) < (t : ℝ) -
      12 * (Real.sqrt δ / θ + α / θ) * (m : ℝ) ^ 2 := by
    simpa [m, Δ, t, e] using lt_of_not_ge hgoal
  have hρlower : 12 * (Real.sqrt δ / θ + α / θ) < ρ := by
    dsimp [ρ]
    rw [lt_div_iff₀ hm2]
    nlinarith
  have hcoeffpos : 0 < 12 * (Real.sqrt δ / θ + α / θ) := by positivity
  have hρpos : 0 < ρ := hcoeffpos.trans hρlower
  have hRlower : 12 * (Real.sqrt δ + α) * (n : ℝ) < R := by
    have hmul := mul_lt_mul_of_pos_right hρlower hmR
    have hscale :
        12 * (Real.sqrt δ / θ + α / θ) * (θ * (n : ℝ)) ≤
          12 * (Real.sqrt δ / θ + α / θ) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left (by simpa [m] using hmθ) hcoeffpos.le
    have hident :
        12 * (Real.sqrt δ / θ + α / θ) * (θ * (n : ℝ)) =
          12 * (Real.sqrt δ + α) * (n : ℝ) := by
      field_simp
    dsimp [R]
    rw [hident] at hscale
    exact hscale.trans_lt (by simpa [mul_assoc] using hmul)
  have htchoose : t ≤ m.choose 2 := by
    change #(SimpleGraph.turanGraph m Δ).edgeFinset ≤ m.choose 2
    simpa using
      (SimpleGraph.card_edgeFinset_le_card_choose_two
        (G := SimpleGraph.turanGraph m Δ))
  have htRlt : (t : ℝ) < (m : ℝ) ^ 2 / 2 := by
    have htR : (t : ℝ) ≤ (m.choose 2 : ℝ) := by exact_mod_cast htchoose
    have hmchoose : (m.choose 2 : ℝ) =
        (m : ℝ) * ((m : ℝ) - 1) / 2 := by
      simpa using (Nat.cast_choose_two (K := ℝ) m)
    rw [hmchoose] at htR
    nlinarith
  have hρhalf : ρ < 1 / 2 := by
    dsimp [ρ]
    rw [div_lt_iff₀ hm2]
    have he0 : (0 : ℝ) ≤ (e : ℝ) := by positivity
    nlinarith
  have hmleN : (m : ℝ) ≤ (n : ℝ) := by
    have hdeg := (C.redGraph.degree_lt_card_verts x).le
    have hdeg' : C.redDegree x ≤ n := by
      change C.redGraph.degree x ≤ n
      simpa using hdeg
    dsimp [m]
    exact_mod_cast hdeg'
  have hRrange : R ∈ Set.Icc (0 : ℝ) ((n : ℝ) / 2) := by
    constructor
    · dsimp [R]
      exact mul_nonneg hρnonneg hmR.le
    · dsimp [R]
      have := mul_le_mul_of_nonneg_left hmleN hρpos.le
      nlinarith [mul_pos hρpos hmR]
  have hρeq : (t : ℝ) - (e : ℝ) = ρ * (m : ℝ) ^ 2 := by
    dsimp [ρ]
    field_simp
  let a : ℝ := 1 / (Δ : ℝ)
  let B : Finset A :=
    Finset.univ.filter fun v ↦ (a + ρ) * (m : ℝ) ≤ (G.degree v : ℝ)
  have hδsqrt : δ < Real.sqrt δ := by
    have hδsq : δ ^ 2 < δ := by
      nlinarith [mul_pos hδ0 (sub_pos.mpr hδ1)]
    exact (Real.lt_sqrt (le_of_lt hδ0)).2 hδsq
  have hΔlinear : (Δ : ℝ) < 7 * δ * (n : ℝ) := by
    have hraw := (max_lt_iff.mp hnLarge).2
    have hden : 0 < 7 * δ := by positivity
    have h := (div_lt_iff₀ hden).mp hraw
    simpa [Δ, mul_comm, mul_left_comm, mul_assoc] using h
  have hΔltR : (Δ : ℝ) < R := by
    have hqbound : 7 * δ * (n : ℝ) ≤
        12 * (Real.sqrt δ + α) * (n : ℝ) := by
      nlinarith [mul_nonneg hα0 hnR.le]
    exact hΔlinear.trans (hqbound.trans_lt hRlower)
  have hone : 1 ≤ ρ * (m : ℝ) * (a + ρ) := by
    have hRa : 1 < R * a := by
      dsimp [a]
      rw [mul_one_div]
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (Δ : ℝ))]
      simpa using hΔltR
    have hmono : R * a ≤ R * (a + ρ) := by
      exact mul_le_mul_of_nonneg_left (by linarith : a ≤ a + ρ)
        (by positivity : 0 ≤ R)
    change 1 ≤ R * (a + ρ)
    exact hRa.le.trans hmono
  have hBcard : R ≤ (B.card : ℝ) := by
    have h := localBlueHighSet_card hk C x ρ hρnonneg hρhalf
      (by simpa [m, Δ, t, e] using hρeq.symm)
      (by simpa [m, Δ, a] using hone)
    simpa [B, A, G, m, Δ, a, R] using h
  let emb : A ↪ Fin n := Function.Embedding.subtype _
  let B₀ : Finset (Fin n) := B.map emb
  let s : ℕ := ⌊R / 16⌋₊
  obtain ⟨z, hz⟩ := exists_weightedDegree_ge_neg_two_sqrt
    hδ hn hnear
  have hRlarge : 32 ≤ R := by
    have hnFloorRaw := (max_lt_iff.mp hnLarge).1
    have hnFloor : 32 < 12 * Real.sqrt δ * (n : ℝ) := by
      have hden : 0 < 3 * Real.sqrt δ := by positivity
      have := (div_lt_iff₀ hden).mp hnFloorRaw
      nlinarith
    have hmiddle : 12 * Real.sqrt δ * (n : ℝ) ≤
        12 * (Real.sqrt δ + α) * (n : ℝ) := by
      nlinarith [mul_nonneg hα0 hnR.le]
    exact (le_of_lt hnFloor).trans (hmiddle.trans hRlower.le)
  have hB₀card : (B₀.card : ℝ) = (B.card : ℝ) := by simp [B₀]
  have hB₀R : R ≤ (B₀.card : ℝ) := by
    rw [hB₀card]
    exact hBcard
  obtain ⟨U, hUsub, hzU, hUcard⟩ :=
    exists_cloneSet B₀ z hRlarge hB₀R
  have hUcard' : U.card = s := by simpa [s] using hUcard
  have hUweighted :
      (((∑ u ∈ U, weightedDegree k C u : ℤ) : ℤ) : ℝ) ≤
        (s : ℝ) * (α * (n : ℝ) - (Δ : ℝ) * R) := by
    rw [show s = U.card by omega]
    push_cast
    calc
      ∑ u ∈ U, (weightedDegree k C u : ℝ) ≤
          ∑ _u ∈ U, (α * (n : ℝ) - (Δ : ℝ) * R) := by
        apply Finset.sum_le_sum
        intro u hu
        have huB₀ : u ∈ B₀ := hUsub hu
        rcases Finset.mem_map.mp huB₀ with ⟨v, hvB, huv⟩
        subst u
        have hvThresh : (a + ρ) * (m : ℝ) ≤ (G.degree v : ℝ) := by
          simpa [B] using hvB
        have hvBlueNat := blueInduce_degree_le C x v
        have hvBlue : (G.degree v : ℝ) ≤ (C.blueDegree v : ℝ) := by
          simpa [G, A] using (show
            ((C.blueGraph.induce (C.redNeighborFinset x : Set (Fin n))).degree v : ℝ) ≤
              (C.blueDegree v : ℝ) by exact_mod_cast hvBlueNat)
        have hblue : (m : ℝ) + (Δ : ℝ) * R ≤
            (Δ : ℝ) * (C.blueDegree v : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left (hvThresh.trans hvBlue)
            (by positivity : (0 : ℝ) ≤ (Δ : ℝ))
          have hident : (Δ : ℝ) * ((a + ρ) * (m : ℝ)) =
              (m : ℝ) + (Δ : ℝ) * R := by
            dsimp [a, R]
            field_simp
          rw [hident] at hmul
          exact hmul
        have hred : (C.redDegree (v : Fin n) : ℝ) ≤
            (m : ℝ) + α * (n : ℝ) := by
          simpa [m] using hmax v
        rw [weightedDegree]
        push_cast
        change (C.redDegree (v : Fin n) : ℝ) -
            (Δ : ℝ) * (C.blueDegree (v : Fin n) : ℝ) ≤
          α * (n : ℝ) - (Δ : ℝ) * R
        nlinarith
      _ = (U.card : ℝ) * (α * (n : ℝ) - (Δ : ℝ) * R) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  let psi := C.clone z U
  have hpsiC : psi ∈ Ck k n := clone_mem_Ck hC hzU
  have hcloneZ := objective_clone_sub_lower_bound k C U hzU
  rw [hUcard'] at hcloneZ
  have hcloneR :
      (s : ℝ) * (weightedDegree k C z : ℝ) -
          (((∑ u ∈ U, weightedDegree k C u : ℤ) : ℤ) : ℝ) -
          ((Δ : ℝ) + 1) * (s : ℝ) ^ 2 ≤
        (objective k psi : ℝ) - (objective k C : ℝ) := by
    dsimp [psi, Δ]
    exact_mod_cast hcloneZ
  have hscalar : δ * (n : ℝ) ^ 2 + (Δ : ℝ) * (n : ℝ) / 2 <
      -(2 * (s : ℝ) * Real.sqrt δ * (n : ℝ)) +
        (s : ℝ) * (Δ : ℝ) * R - (s : ℝ) * α * (n : ℝ) -
          ((Δ : ℝ) + 1) * (s : ℝ) ^ 2 := by
    simpa [s] using cloneGain_gt_mantel_explicit hδ0 hα0 hΔR hRrange
      hRlower hnLarge
  have hgain : δ * (n : ℝ) ^ 2 + (Δ : ℝ) * (n : ℝ) / 2 <
      (objective k psi : ℝ) - (objective k C : ℝ) := by
    have hz' : -(2 * Real.sqrt δ * (n : ℝ)) ≤
        (weightedDegree k C z : ℝ) := hz
    exact hscalar.trans_le (by nlinarith [hUweighted, hcloneR])
  have hpsiMantel := kthOrderMantel (by omega : 3 ≤ k) hpsiC
  have hpsiTwoZ : 2 * objective k psi ≤ ((Δ * n : ℕ) : ℤ) := by
    have htwo : 2 * objective k psi ≤
        2 * (((Δ * n) / 2 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left (by simpa [Δ] using hpsiMantel) (by norm_num)
    have hfloor : 2 * ((Δ * n) / 2) ≤ Δ * n := by omega
    have hfloorZ : 2 * (((Δ * n) / 2 : ℕ) : ℤ) ≤
        ((Δ * n : ℕ) : ℤ) := by exact_mod_cast hfloor
    exact htwo.trans hfloorZ
  have hpsiTwoR : 2 * (objective k psi : ℝ) ≤
      (Δ : ℝ) * (n : ℝ) := by
    exact_mod_cast hpsiTwoZ
  nlinarith

/-- Local near-Turán structure in a large red neighborhood.

The maximum-red-degree hypothesis is written in its pointwise equivalent form:
every red degree is at most the red degree of `x` plus `α * n`. The
large-`n` threshold depends only on `k`, `δ`, and `α` (in fact the
constructed threshold is independent of `α`), and precedes the universal
quantifier over `θ`.

The finite proof uses a high-blue-degree subset and explicit floor bounds.
The manuscript's direct weighted-degree averaging proof has the same
cloning mechanism and proves the same statement and constant.

Paper: Lemma `lemma:locally-turan`.
-/
theorem locallyTuran (k : ℕ) (hk : 4 ≤ k) (δ α : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
      -(δ * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
      ∀ x : Fin n,
        (∀ v : Fin n,
          (C.redDegree v : ℝ) ≤
            (C.redDegree x : ℝ) + α * (n : ℝ)) →
        ∀ θ : ℝ, θ ∈ Set.Ioc (0 : ℝ) 1 →
          θ * (n : ℝ) ≤ (C.redDegree x : ℝ) →
          (SimpleGraph.turanNumber (C.redDegree x) (delta k) : ℝ) -
              12 * (Real.sqrt δ / θ + α / θ) *
                (C.redDegree x : ℝ) ^ 2 ≤
            (#(redGreenNeighborhoodGraph C x).edgeFinset : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := exists_localTuranThreshold k hδ.1
  refine ⟨n₀, ?_⟩
  intro n hn C hC hnear x hmax θ hθ hmθ
  obtain ⟨_hnpos, hnLarge, _hdelta⟩ := hn₀ n hn
  exact locallyTuran_core hk hδ hα hθ hC hnear x hmax hmθ hnLarge

/-! ## Between-cluster dominant colors: abstract double counting -/

variable {A B : Type*}

noncomputable def finiteAverage {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  Finset.expect Finset.univ f

noncomputable def finiteAverageOn {X : Type*} (S : Finset X) (f : X → ℝ) : ℝ :=
  Finset.expect S f

/-- The real indicator of a specified edge color. -/
noncomputable def colorIndicator {V : Type*} [DecidableEq V]
    (C : ColoredGraph V) (c : EdgeColor) (v w : V) : ℝ :=
  if C.color v w = c then 1 else 0

theorem finiteAverage_colorIndicator_eq_colorDegreeRatio
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (c : EdgeColor) (v : V) (T : Finset V)
    (hv : v ∉ T) :
    finiteAverage (fun w : T ↦ colorIndicator C c v w) =
      C.colorDegreeRatio c v T := by
  classical
  have hfilter :
      {w ∈ T | C.color v w = c} = C.neighborFinsetIn c v T := by
    ext w
    rw [C.mem_neighborFinsetIn, Finset.mem_filter]
    constructor
    · rintro ⟨hw, hc⟩
      exact ⟨fun hvw ↦ hv (hvw ▸ hw), hc, hw⟩
    · rintro ⟨_, hc, hw⟩
      exact ⟨hw, hc⟩
  unfold finiteAverage colorDegreeRatio
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_coe,
    Finset.univ_eq_attach T, Finset.sum_attach]
  simp only [colorIndicator, Finset.sum_boole]
  rw [hfilter]
  rfl

theorem finiteAverage_colorDegreeRatio_eq_colorDensity
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (c : EdgeColor) (S T : Finset V)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    finiteAverage (fun v : S ↦ C.colorDegreeRatio c v T) =
      C.colorDensity c S T := by
  classical
  unfold finiteAverage colorDegreeRatio colorDensity
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_coe,
    Finset.univ_eq_attach S]
  rw [Finset.sum_attach S
    (fun v ↦ (C.degreeIn c v T : ℝ) / (T.card : ℝ))]
  have hT0 : (T.card : ℝ) ≠ 0 := by positivity
  have hS0 : (S.card : ℝ) ≠ 0 := by positivity
  rw [← Finset.sum_div]
  rw [show (∑ v ∈ S, (C.degreeIn c v T : ℝ)) =
      (C.colorEdgeCountBetween c S T : ℝ) by
    exact_mod_cast C.sum_degreeIn_eq_colorEdgeCountBetween c S T]
  field_simp

theorem finiteAverage_colorIndicator_eq_colorDensity
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (c : EdgeColor) (S T : Finset V)
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : Disjoint S T) :
    finiteAverage (fun v : S ↦
      finiteAverage (fun w : T ↦ colorIndicator C c v w)) =
      C.colorDensity c S T := by
  calc
    finiteAverage (fun v : S ↦
        finiteAverage (fun w : T ↦ colorIndicator C c v w)) =
        finiteAverage (fun v : S ↦ C.colorDegreeRatio c v T) := by
          unfold finiteAverage
          apply Finset.expect_congr rfl
          intro v _
          exact finiteAverage_colorIndicator_eq_colorDegreeRatio C c v T
            (fun hvT ↦ Finset.disjoint_left.mp hST v.property hvT)
    _ = C.colorDensity c S T :=
      finiteAverage_colorDegreeRatio_eq_colorDensity C c S T hS hT

private noncomputable abbrev uavg {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  finiteAverage f

private noncomputable abbrev savg {X : Type*} (S : Finset X) (f : X → ℝ) : ℝ :=
  finiteAverageOn S f

private theorem expect_univ_partition
    [Fintype A] [Nonempty A] [DecidableEq A]
    (H : Finset A) (f : A → ℝ) (hH : H.Nonempty) (hL : Hᶜ.Nonempty) :
    (Finset.expect Finset.univ fun a : A ↦ f a) =
      ((H.card : ℝ) / Fintype.card A) * (Finset.expect H fun a ↦ f a) +
      (((Hᶜ).card : ℝ) / Fintype.card A) * (Finset.expect Hᶜ fun a ↦ f a) := by
  rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
    Finset.expect_eq_sum_div_card]
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := by positivity
  have hH0 : (H.card : ℝ) ≠ 0 := by exact_mod_cast hH.card_ne_zero
  have hL0 : ((Hᶜ).card : ℝ) ≠ 0 := by exact_mod_cast hL.card_ne_zero
  have hsum : (∑ a : A, f a) = ∑ a ∈ H, f a + ∑ a ∈ Hᶜ, f a := by
    rw [← Finset.sum_union disjoint_compl_right]
    congr 1
    exact (Finset.union_compl H).symm
  rw [hsum]
  field_simp
  <;> ring

private theorem card_ratio_add_compl
    [Fintype A] [Nonempty A] [DecidableEq A] (H : Finset A) :
    (H.card : ℝ) / Fintype.card A + ((Hᶜ).card : ℝ) / Fintype.card A = 1 := by
  have hA0 : (Fintype.card A : ℝ) ≠ 0 := by positivity
  rw [← add_div]
  have hcard : H.card + (Hᶜ).card = Fintype.card A := by
    simpa [add_comm] using Finset.card_add_card_compl H
  have hcardR : (H.card : ℝ) + ((Hᶜ).card : ℝ) = Fintype.card A := by
    exact_mod_cast hcard
  rw [hcardR, div_self hA0]

private theorem min_one_sub_dichotomy {x μ : ℝ}
    (h : min x (1 - x) ≤ μ) : x ≤ μ ∨ 1 - μ ≤ x := by
  rw [min_le_iff] at h
  rcases h with hx | hx
  · exact Or.inl hx
  · exact Or.inr (by linarith)

/-!
An abstract form of Stage II of the between-cluster dominant-color proof.
The three functions are the normalized color indicators on a finite
bipartite pair.  Both orientations satisfy the vertex-level mixed-mass
bound; the conclusion is the paper's `10 * μ` dominant-color estimate.
-/
set_option maxHeartbeats 800000 in
-- Nested finite averaging and the resulting linear arithmetic need the larger budget.
theorem dominantColor_of_vertexMixedMass
    [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype B] [Nonempty B]
    (red green blue : A → B → ℝ) (μ : ℝ)
    (hμpos : 0 < μ)
    (hred0 : ∀ a b, 0 ≤ red a b)
    (hgreen0 : ∀ a b, 0 ≤ green a b)
    (hblue0 : ∀ a b, 0 ≤ blue a b)
    (hpartition : ∀ a b, red a b + green a b + blue a b = 1)
    (hblue : finiteAverage (fun a : A ↦ finiteAverage (fun b : B ↦ blue a b)) ≤ μ)
    (hrowMixed : ∀ a,
      min (finiteAverage (fun b : B ↦ red a b))
        (1 - finiteAverage (fun b : B ↦ red a b)) ≤ μ)
    (hcolMixed : ∀ b,
      min (finiteAverage (fun a : A ↦ red a b))
        (1 - finiteAverage (fun a : A ↦ red a b)) ≤ μ) :
    max (finiteAverage (fun a : A ↦ finiteAverage (fun b : B ↦ red a b)))
        (finiteAverage (fun a : A ↦ finiteAverage (fun b : B ↦ green a b))) ≥
      1 - 10 * μ := by
  classical
  let rowR : A → ℝ := fun a ↦ uavg (fun b : B ↦ red a b)
  let rowG : A → ℝ := fun a ↦ uavg (fun b : B ↦ green a b)
  let rowB : A → ℝ := fun a ↦ uavg (fun b : B ↦ blue a b)
  let R : ℝ := uavg rowR
  let G : ℝ := uavg rowG
  let Bl : ℝ := uavg rowB
  have hrowpart (a : A) : rowR a + rowG a + rowB a = 1 := by
    dsimp [rowR, rowG, rowB, uavg, finiteAverage]
    rw [← Finset.expect_add_distrib, ← Finset.expect_add_distrib]
    rw [← Fintype.expect_const (ι := B) (1 : ℝ)]
    apply Finset.expect_congr rfl
    intro b _
    exact hpartition a b
  have hglobalpart : R + G + Bl = 1 := by
    dsimp [R, G, Bl, uavg, finiteAverage]
    rw [← Finset.expect_add_distrib, ← Finset.expect_add_distrib]
    rw [← Fintype.expect_const (ι := A) (1 : ℝ)]
    apply Finset.expect_congr rfl
    intro a _
    exact hrowpart a
  have hrowR0 (a : A) : 0 ≤ rowR a := by
    dsimp [rowR, uavg, finiteAverage]
    exact Finset.expect_nonneg (fun b _ ↦ hred0 a b)
  have hrowG0 (a : A) : 0 ≤ rowG a := by
    dsimp [rowG, uavg, finiteAverage]
    exact Finset.expect_nonneg (fun b _ ↦ hgreen0 a b)
  have hrowB0 (a : A) : 0 ≤ rowB a := by
    dsimp [rowB, uavg, finiteAverage]
    exact Finset.expect_nonneg (fun b _ ↦ hblue0 a b)
  have hrowR1 (a : A) : rowR a ≤ 1 := by
    nlinarith [hrowpart a, hrowG0 a, hrowB0 a]
  have hBl : Bl ≤ μ := by simpa [Bl, rowB] using hblue
  by_contra hdom
  have hmax : max R G < 1 - 10 * μ := by
    simpa [R, G, rowR, rowG] using (lt_of_not_ge hdom)
  have hRupper : R < 1 - 10 * μ := lt_of_le_of_lt (le_max_left _ _) hmax
  have hGupper : G < 1 - 10 * μ := lt_of_le_of_lt (le_max_right _ _) hmax
  have hRlower : 9 * μ < R := by
    nlinarith [hglobalpart, hGupper, hBl]
  have hrowDich (a : A) : rowR a ≤ μ ∨ 1 - μ ≤ rowR a := by
    exact min_one_sub_dichotomy (by simpa [rowR] using hrowMixed a)
  let H : Finset A := Finset.univ.filter (fun a ↦ 1 - μ ≤ rowR a)
  have hmemH (a : A) : a ∈ H ↔ 1 - μ ≤ rowR a := by simp [H]
  have hlow (a : A) (ha : a ∉ H) : rowR a ≤ μ := by
    rcases hrowDich a with haLow | haHigh
    · exact haLow
    · exact False.elim (ha (hmemH a |>.2 haHigh))
  let share : ℝ := (H.card : ℝ) / Fintype.card A
  have hindicator :
      uavg (fun a : A ↦ if a ∈ H then (1 : ℝ) else 0) = share := by
    change Finset.expect Finset.univ
      (fun a : A ↦ if a ∈ H then (1 : ℝ) else 0) = share
    rw [Fintype.expect_eq_sum_div_card]
    simp [share]
  have hpointUpper (a : A) :
      rowR a ≤ (if a ∈ H then (1 : ℝ) else 0) + μ := by
    by_cases ha : a ∈ H
    · simp [ha]
      linarith [hrowR1 a]
    · simp [ha, hlow a ha]
  have hpointLower (a : A) :
      (if a ∈ H then (1 : ℝ) else 0) ≤ rowR a + μ := by
    by_cases ha : a ∈ H
    · simp [ha]
      linarith [(hmemH a).1 ha]
    · simp [ha]
      nlinarith [hrowR0 a, hμpos]
  have hRle : R ≤ share + μ := by
    calc
      R ≤ uavg (fun a : A ↦ (if a ∈ H then (1 : ℝ) else 0) + μ) := by
        exact Finset.expect_le_expect (fun a _ ↦ hpointUpper a)
      _ = share + μ := by
        change Finset.expect Finset.univ
          (fun a : A ↦ (if a ∈ H then (1 : ℝ) else 0) + μ) = _
        rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
        change uavg (fun a : A ↦ if a ∈ H then (1 : ℝ) else 0) + μ = _
        rw [hindicator]
  have hsharele : share ≤ R + μ := by
    calc
      share = uavg (fun a : A ↦ if a ∈ H then (1 : ℝ) else 0) := hindicator.symm
      _ ≤ uavg (fun a : A ↦ rowR a + μ) := by
        exact Finset.expect_le_expect (fun a _ ↦ hpointLower a)
      _ = R + μ := by
        change Finset.expect Finset.univ (fun a : A ↦ rowR a + μ) = _
        rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
        rfl
  have hshareLower : 8 * μ < share := by nlinarith
  have hshareUpper : share < 1 - 9 * μ := by nlinarith
  have hH : H.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have : share = 0 := by simp [share, hEmpty]
    nlinarith
  have hshareLtOne : share < 1 := by nlinarith
  have hL : Hᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcard : H.card = Fintype.card A := by
      have := Finset.card_add_card_compl H
      simp [hEmpty] at this
      omega
    have : share = 1 := by
      simp [share, hcard, Fintype.card_ne_zero]
    nlinarith
  let p : B → ℝ := fun b ↦ savg H (fun a ↦ 1 - red a b)
  let q : B → ℝ := fun b ↦ savg Hᶜ (fun a ↦ red a b)
  have hpavg : uavg p ≤ μ := by
    rw [show uavg p = savg H (fun a ↦ uavg (fun b : B ↦ 1 - red a b)) by
      dsimp [p]
      exact Finset.expect_comm _ _ _]
    apply Finset.expect_le hH
    intro a ha
    change Finset.expect Finset.univ (fun b : B ↦ 1 - red a b) ≤ μ
    rw [Finset.expect_sub_distrib, Fintype.expect_const]
    have haHigh := (hmemH a).1 ha
    change 1 - μ ≤ Finset.expect Finset.univ (fun b : B ↦ red a b) at haHigh
    linarith
  have hqavg : uavg q ≤ μ := by
    rw [show uavg q = savg Hᶜ (fun a ↦ uavg (fun b : B ↦ red a b)) by
      dsimp [q]
      exact Finset.expect_comm _ _ _]
    apply Finset.expect_le hL
    intro a ha
    have haNot : a ∉ H := by simpa using ha
    simpa [rowR] using hlow a haNot
  have hpqavg : uavg (fun b : B ↦ p b + q b) ≤ 2 * μ := by
    change Finset.expect Finset.univ (fun b : B ↦ p b + q b) ≤ 2 * μ
    rw [Finset.expect_add_distrib]
    change Finset.expect Finset.univ p ≤ μ at hpavg
    change Finset.expect Finset.univ q ≤ μ at hqavg
    linarith
  obtain ⟨b₀, _, hb₀⟩ := Finset.exists_le_of_expect_le (s := (Finset.univ : Finset B))
    Finset.univ_nonempty hpqavg
  have hp0 : 0 ≤ p b₀ := by
    apply Finset.expect_nonneg
    intro a _
    have := hrowR1 a
    -- Pointwise red is at most one by the color partition.
    nlinarith [hpartition a b₀, hgreen0 a b₀, hblue0 a b₀]
  have hq0 : 0 ≤ q b₀ := by
    exact Finset.expect_nonneg (fun a _ ↦ hred0 a b₀)
  have hp : p b₀ ≤ 2 * μ := by nlinarith
  have hq : q b₀ ≤ 2 * μ := by nlinarith
  let lshare : ℝ := ((Hᶜ).card : ℝ) / Fintype.card A
  have hshares : share + lshare = 1 := by
    simpa [share, lshare] using card_ratio_add_compl (A := A) H
  have hshare0 : 0 ≤ share := by positivity
  have hlshare0 : 0 ≤ lshare := by positivity
  have hshare1 : share ≤ 1 := by nlinarith
  have hlshare1 : lshare ≤ 1 := by nlinarith
  let col : ℝ := uavg (fun a : A ↦ red a b₀)
  let highAvg : ℝ := savg H (fun a ↦ red a b₀)
  let lowAvg : ℝ := savg Hᶜ (fun a ↦ red a b₀)
  have hhigh : 1 - 2 * μ ≤ highAvg := by
    have hp' : savg H (fun a ↦ 1 - red a b₀) ≤ 2 * μ := by simpa [p] using hp
    change Finset.expect H (fun a ↦ 1 - red a b₀) ≤ 2 * μ at hp'
    rw [Finset.expect_sub_distrib, Finset.expect_const hH] at hp'
    change 1 - 2 * μ ≤ Finset.expect H (fun a ↦ red a b₀)
    linarith
  have hhigh1 : highAvg ≤ 1 := by
    apply Finset.expect_le hH
    intro a _
    nlinarith [hpartition a b₀, hgreen0 a b₀, hblue0 a b₀]
  have hhigh0 : 0 ≤ highAvg := by
    exact Finset.expect_nonneg (fun a _ ↦ hred0 a b₀)
  have hlowAvg : lowAvg ≤ 2 * μ := by simpa [lowAvg, q] using hq
  have hlowAvg0 : 0 ≤ lowAvg := by
    exact Finset.expect_nonneg (fun a _ ↦ hred0 a b₀)
  have hcolsplit : col = share * highAvg + lshare * lowAvg := by
    simpa [col, share, lshare, highAvg, lowAvg, uavg, savg,
      finiteAverage, finiteAverageOn] using
      expect_univ_partition (A := A) H (fun a ↦ red a b₀) hH hL
  have hcolLower : share - 2 * μ ≤ col := by
    have htwomu : 0 ≤ 2 * μ := by positivity
    have hmushare : 2 * μ * share ≤ 2 * μ :=
      mul_le_of_le_one_right htwomu hshare1
    calc
      share - 2 * μ ≤ share - 2 * μ * share := sub_le_sub_left hmushare share
      _ = share * (1 - 2 * μ) := by ring
      _ ≤ share * highAvg := mul_le_mul_of_nonneg_left hhigh hshare0
      _ ≤ share * highAvg + lshare * lowAvg :=
        le_add_of_nonneg_right (mul_nonneg hlshare0 hlowAvg0)
      _ = col := hcolsplit.symm
  have hcolUpper : col ≤ share + 2 * μ := by
    have htwomu : 0 ≤ 2 * μ := by positivity
    have hmulHigh : share * highAvg ≤ share := by
      simpa using mul_le_mul_of_nonneg_left hhigh1 hshare0
    have hmulLow : lshare * lowAvg ≤ 2 * μ := by
      calc
        lshare * lowAvg ≤ lshare * (2 * μ) :=
          mul_le_mul_of_nonneg_left hlowAvg hlshare0
        _ = (2 * μ) * lshare := by ring
        _ ≤ 2 * μ := mul_le_of_le_one_right htwomu hlshare1
    rw [hcolsplit]
    linarith
  have hcolMiddleLow : 6 * μ < col := by nlinarith
  have hcolMiddleHigh : col < 1 - 7 * μ := by nlinarith
  have hcolDich : col ≤ μ ∨ 1 - μ ≤ col := by
    exact min_one_sub_dichotomy (by simpa [col] using hcolMixed b₀)
  rcases hcolDich with hcolLow | hcolHigh <;> nlinarith

/-- Graph-facing Stage II: two nonempty disjoint clusters whose red profiles
are almost Boolean in both orientations have a dominant red or green color,
provided their blue density is small. -/
theorem colorDensity_dominant_of_vertexMixedMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (S T : Finset V) (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : Disjoint S T) (μ : ℝ) (hμpos : 0 < μ)
    (hblue : C.colorDensity .blue S T ≤ μ)
    (hrowMixed : ∀ v ∈ S,
      min (C.colorDegreeRatio .red v T) (1 - C.colorDegreeRatio .red v T) ≤ μ)
    (hcolMixed : ∀ v ∈ T,
      min (C.colorDegreeRatio .red v S) (1 - C.colorDegreeRatio .red v S) ≤ μ) :
    max (C.colorDensity .red S T) (C.colorDensity .green S T) ≥
      1 - 10 * μ := by
  classical
  letI : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  let redM : S → T → ℝ := fun v w ↦ colorIndicator C .red v w
  let greenM : S → T → ℝ := fun v w ↦ colorIndicator C .green v w
  let blueM : S → T → ℝ := fun v w ↦ colorIndicator C .blue v w
  have hred0 : ∀ v w, 0 ≤ redM v w := by
    intro v w
    dsimp [redM, colorIndicator]
    positivity
  have hgreen0 : ∀ v w, 0 ≤ greenM v w := by
    intro v w
    dsimp [greenM, colorIndicator]
    positivity
  have hblue0 : ∀ v w, 0 ≤ blueM v w := by
    intro v w
    dsimp [blueM, colorIndicator]
    positivity
  have hpartition : ∀ v w, redM v w + greenM v w + blueM v w = 1 := by
    intro v w
    dsimp [redM, greenM, blueM, colorIndicator]
    cases hcolor : C.color v w <;> simp [hcolor]
  have hblue' :
      finiteAverage (fun v : S ↦ finiteAverage (fun w : T ↦ blueM v w)) ≤ μ := by
    rw [show finiteAverage (fun v : S ↦ finiteAverage (fun w : T ↦ blueM v w)) =
        C.colorDensity .blue S T by
      simpa [blueM] using
        finiteAverage_colorIndicator_eq_colorDensity C .blue S T hS hT hST]
    exact hblue
  have hrowMixed' : ∀ v : S,
      min (finiteAverage (fun w : T ↦ redM v w))
        (1 - finiteAverage (fun w : T ↦ redM v w)) ≤ μ := by
    intro v
    have hvT : (v : V) ∉ T := fun hv ↦
      Finset.disjoint_left.mp hST v.property hv
    rw [show finiteAverage (fun w : T ↦ redM v w) =
        C.colorDegreeRatio .red v T by
      simpa [redM] using
        finiteAverage_colorIndicator_eq_colorDegreeRatio C .red v T hvT]
    exact hrowMixed v v.property
  have hcolMixed' : ∀ w : T,
      min (finiteAverage (fun v : S ↦ redM v w))
        (1 - finiteAverage (fun v : S ↦ redM v w)) ≤ μ := by
    intro w
    have hwS : (w : V) ∉ S := fun hw ↦
      Finset.disjoint_left.mp hST hw w.property
    have hcomm : finiteAverage (fun v : S ↦ redM v w) =
        finiteAverage (fun v : S ↦ colorIndicator C .red w v) := by
      unfold finiteAverage
      apply Finset.expect_congr rfl
      intro v _
      simp only [redM, colorIndicator]
      rw [C.color_comm]
    rw [hcomm, finiteAverage_colorIndicator_eq_colorDegreeRatio C .red w S hwS]
    exact hcolMixed w w.property
  have hmain := dominantColor_of_vertexMixedMass redM greenM blueM μ hμpos
    hred0 hgreen0 hblue0 hpartition hblue' hrowMixed' hcolMixed'
  have hredDensity :
      finiteAverage (fun v : S ↦ finiteAverage (fun w : T ↦ redM v w)) =
        C.colorDensity .red S T := by
    simpa [redM] using
      finiteAverage_colorIndicator_eq_colorDensity C .red S T hS hT hST
  have hgreenDensity :
      finiteAverage (fun v : S ↦ finiteAverage (fun w : T ↦ greenM v w)) =
        C.colorDensity .green S T := by
    simpa [greenM] using
      finiteAverage_colorIndicator_eq_colorDensity C .green S T hS hT hST
  rw [hredDensity, hgreenDensity] at hmain
  exact hmain

/-! ## High-red clusters and the finite forbidden transversal -/

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def highRedClusterIndices {t : ℕ} (C : ColoredGraph V)
    (clusters : Fin t → Finset V) (i : Fin t) (v : V) (θ : ℝ) :
    Finset (Fin t) :=
  Finset.univ.filter fun j ↦ j ≠ i ∧ θ ≤ C.colorDegreeRatio .red v (clusters j)

@[simp] theorem mem_highRedClusterIndices {t : ℕ} (C : ColoredGraph V)
    (clusters : Fin t → Finset V) (i j : Fin t) (v : V) (θ : ℝ) :
    j ∈ highRedClusterIndices C clusters i v θ ↔
      j ≠ i ∧ θ ≤ C.colorDegreeRatio .red v (clusters j) := by
  simp [highRedClusterIndices]

theorem highRedClusterIndices_card_le_delta
    (k : ℕ) (hk : 3 ≤ k) {β : ℝ} (hβ : 0 < β)
    {n t : ℕ} {C : ColoredGraph (Fin n)} (hC : C ∈ Ck k n)
    (clusters : Fin t → Finset (Fin n))
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin t)) clusters)
    (hnonempty : ∀ j, (clusters j).Nonempty)
    (hblue : ∀ a b, a ≠ b →
      C.colorDensity .blue (clusters a) (clusters b) ≤ β)
    (i : Fin t) (v : Fin n) (hv : v ∈ clusters i) :
    (highRedClusterIndices C clusters i v
      (8 * (delta k : ℝ) * Real.sqrt β)).card ≤ delta k := by
  classical
  let Δ := delta k
  let θ : ℝ := 8 * (Δ : ℝ) * Real.sqrt β
  let A := highRedClusterIndices C clusters i v θ
  have hΔ : 1 ≤ Δ := by dsimp [Δ, delta]; omega
  have hΔR : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hsqrt : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hθ : 0 < θ := by dsimp [θ]; positivity
  change A.card ≤ Δ
  by_contra hcard
  have hlarge : Δ + 1 ≤ A.card := by omega
  obtain ⟨J, hJA, hJcard⟩ := A.exists_subset_card_eq hlarge
  let e : Fin (Δ + 1) ≃ J := (Finset.equivFinOfCardEq hJcard).symm
  let idx : Fin (Δ + 1) → Fin t := fun r ↦ (e r).1
  have hidxinj : Function.Injective idx := by
    intro r q hrq
    apply e.injective
    apply Subtype.ext
    exact hrq
  have hidxA (r : Fin (Δ + 1)) : idx r ∈ A :=
    hJA (e r).property
  have hidxne (r : Fin (Δ + 1)) : idx r ≠ i :=
    (mem_highRedClusterIndices C clusters i (idx r) v θ).mp (hidxA r) |>.1
  let S : Fin (Δ + 1) → Finset (Fin n) := fun r ↦
    C.redNeighborFinsetIn v (clusters (idx r))
  have hclusterpos (r : Fin (Δ + 1)) :
      0 < ((clusters (idx r)).card : ℝ) := by
    exact_mod_cast (hnonempty (idx r)).card_pos
  have hScard (r : Fin (Δ + 1)) :
      θ * ((clusters (idx r)).card : ℝ) ≤ (S r).card := by
    have hrho :=
      (mem_highRedClusterIndices C clusters i (idx r) v θ).mp (hidxA r) |>.2
    rw [colorDegreeRatio] at hrho
    exact (le_div_iff₀ (hclusterpos r)).mp hrho
  have hSnonempty (r : Fin (Δ + 1)) : (S r).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hcardzero : ((S r).card : ℝ) = 0 := by simp [hzero]
    have hs := hScard r
    rw [hcardzero] at hs
    have := mul_pos hθ (hclusterpos r)
    linarith
  have hSsub (r : Fin (Δ + 1)) : S r ⊆ clusters (idx r) := by
    intro x hx
    exact (C.mem_neighborFinsetIn .red v x (clusters (idx r))).mp hx |>.2.2
  let bad : Fin n → Fin n → Prop := fun x y ↦ C.blueGraph.Adj x y
  have hbadCount (r q : Fin (Δ + 1)) :
      transversalBadPairCount S bad r q =
        C.colorEdgeCountBetween .blue (S r) (S q) := by
    unfold transversalBadPairCount colorEdgeCountBetween
    rw [SimpleGraph.interedges_def]
    refine Finset.card_bij
      (fun p _hp ↦ ((p.1 : Fin n), (p.2 : Fin n))) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_product.mpr ⟨p.1.property, p.2.property⟩, hp.2⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst heq)
      · exact Subtype.ext (congrArg Prod.snd heq)
    · intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_product] at hp
      obtain ⟨⟨hpS, hpT⟩, hpbad⟩ := hp
      refine ⟨(⟨p.1, hpS⟩, ⟨p.2, hpT⟩), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpbad
  let ε : ℝ := β / θ ^ 2
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hpair (r q : Fin (Δ + 1)) (hrq : r ≠ q) :
      (transversalBadPairCount S bad r q : ℝ) /
          ((S r).card * (S q).card : ℕ) ≤ ε := by
    have hidxne' : idx r ≠ idx q := hidxinj.ne hrq
    have hmonoNat := C.colorEdgeCountBetween_mono .blue (hSsub r) (hSsub q)
    have hmono : (C.colorEdgeCountBetween .blue (S r) (S q) : ℝ) ≤
        C.colorEdgeCountBetween .blue (clusters (idx r)) (clusters (idx q)) := by
      exact_mod_cast hmonoNat
    have hclusterden : 0 <
        ((clusters (idx r)).card : ℝ) * ((clusters (idx q)).card : ℝ) :=
      mul_pos (hclusterpos r) (hclusterpos q)
    have hlargeCount :
        (C.colorEdgeCountBetween .blue (clusters (idx r)) (clusters (idx q)) : ℝ) ≤
          β * (((clusters (idx r)).card : ℝ) *
            ((clusters (idx q)).card : ℝ)) := by
      exact (div_le_iff₀ hclusterden).mp (hblue _ _ hidxne')
    have hsr : 0 < ((S r).card : ℝ) := by
      exact_mod_cast (hSnonempty r).card_pos
    have hsq : 0 < ((S q).card : ℝ) := by
      exact_mod_cast (hSnonempty q).card_pos
    have hSden : 0 < ((S r).card : ℝ) * ((S q).card : ℝ) := mul_pos hsr hsq
    have hθsq : 0 < θ ^ 2 := sq_pos_of_pos hθ
    rw [hbadCount]
    dsimp [ε]
    push_cast
    change (C.colorEdgeCountBetween .blue (S r) (S q) : ℝ) /
        (((S r).card : ℝ) * ((S q).card : ℝ)) ≤ β / θ ^ 2
    rw [div_le_div_iff₀ hSden hθsq]
    have hprod := mul_le_mul (hScard r) (hScard q)
      (by positivity : 0 ≤ θ * ((clusters (idx q)).card : ℝ))
      (by positivity : 0 ≤ ((S r).card : ℝ))
    have hscaled := mul_le_mul_of_nonneg_left hprod (le_of_lt hβ)
    calc
      (C.colorEdgeCountBetween .blue (S r) (S q) : ℝ) * θ ^ 2 ≤
          (C.colorEdgeCountBetween .blue (clusters (idx r))
            (clusters (idx q)) : ℝ) * θ ^ 2 :=
        mul_le_mul_of_nonneg_right hmono (sq_nonneg θ)
      _ ≤ (β * (((clusters (idx r)).card : ℝ) *
            ((clusters (idx q)).card : ℝ))) * θ ^ 2 :=
        mul_le_mul_of_nonneg_right hlargeCount (sq_nonneg θ)
      _ = β * ((θ * ((clusters (idx r)).card : ℝ)) *
            (θ * ((clusters (idx q)).card : ℝ))) := by ring
      _ ≤ β * (((S r).card : ℝ) * ((S q).card : ℝ)) := hscaled
  have hsqrtSq : (Real.sqrt β) ^ 2 = β := Real.sq_sqrt hβ.le
  have hcoef : (((Δ : ℝ) + 1) ^ 2) < 64 * (Δ : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((Δ : ℝ) - 1)]
  have hcoefβ := mul_lt_mul_of_pos_right hcoef hβ
  have hsmall : (Fintype.card (Fin (Δ + 1)) : ℝ) ^ 2 * ε < 1 := by
    have hθsq : θ ^ 2 = 64 * (Δ : ℝ) ^ 2 * β := by
      dsimp [θ]
      nlinarith
    rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    dsimp [ε]
    rw [show ((Δ : ℝ) + 1) ^ 2 * (β / θ ^ 2) =
      (((Δ : ℝ) + 1) ^ 2 * β) / θ ^ 2 by ring]
    rw [div_lt_one (sq_pos_of_pos hθ), hθsq]
    nlinarith
  obtain ⟨f, hf⟩ := exists_transversal_no_bad S bad hSnonempty hε hpair hsmall
  let y : Fin (Δ + 1) → Fin n := fun r ↦ f r
  have hymem (r : Fin (Δ + 1)) : y r ∈ S r := (f r).property
  have hycluster (r : Fin (Δ + 1)) : y r ∈ clusters (idx r) := hSsub r (hymem r)
  have hyinj : Function.Injective y := by
    intro r q hrq
    by_contra hrq'
    have hidxne' : idx r ≠ idx q := hidxinj.ne hrq'
    exact Finset.disjoint_left.mp
      (hdisj (Set.mem_univ _) (Set.mem_univ _) hidxne')
      (hycluster r) (hrq ▸ hycluster q)
  let leaves : Finset (Fin n) := Finset.univ.image y
  have hleavescard : leaves.card = k - 1 := by
    have himage : leaves.card = Fintype.card (Fin (Δ + 1)) := by
      dsimp [leaves]
      rw [Finset.card_image_of_injective _ hyinj]
      simp
    rw [himage, Fintype.card_fin]
    dsimp [Δ, delta]
    omega
  have hvleaves : v ∉ leaves := by
    intro hvleaf
    obtain ⟨r, _hr, hyr⟩ := Finset.mem_image.mp hvleaf
    have hdi := hdisj (Set.mem_univ i) (Set.mem_univ (idx r)) (Ne.symm (hidxne r))
    exact Finset.disjoint_left.mp hdi hv (hyr ▸ hycluster r)
  have hred : ∀ x ∈ leaves, C.color v x = .red := by
    intro x hx
    obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp hx
    exact (C.mem_neighborFinsetIn .red v (y r) (clusters (idx r))).mp (hymem r) |>.2.1
  have hleaf : ∀ x ∈ leaves, ∀ z ∈ leaves, x ≠ z →
      (C.color x z).IsLeafColor := by
    intro x hx z hz hxz
    obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hz
    have hrq : r ≠ q := fun hrq ↦ hxz (hrq ▸ rfl)
    rw [EdgeColor.isLeafColor_iff_ne_blue]
    intro hblueColor
    exact hf r q hrq ((C.colorGraph_adj .blue (y r) (y q)).2 ⟨hxz, hblueColor⟩)
  have hconfig : IsForbiddenConfig k C v leaves :=
    ⟨hvleaves, hleavescard, hred, hleaf⟩
  exact (not_fkFree_of_forbiddenConfig (by omega) hconfig) hC

/-! ## Vertexwise red-profile mixed mass -/

private theorem redDegreeIn_add_blueDegreeIn_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (v : V) (U : Finset V) :
    C.redDegreeIn v U + C.blueDegreeIn v U ≤ U.card := by
  classical
  change C.degreeIn .red v U + C.degreeIn .blue v U ≤ U.card
  unfold degreeIn neighborFinsetIn
  have hdisj :
      Disjoint (C.neighborFinset .red v ∩ U) (C.neighborFinset .blue v ∩ U) := by
    rw [Finset.disjoint_left]
    intro w hwred hwblue
    have hr := (Finset.mem_inter.mp hwred).1
    have hb := (Finset.mem_inter.mp hwblue).1
    have hr' := (C.mem_neighborFinset .red v w).1 hr
    have hb' := (C.mem_neighborFinset .blue v w).1 hb
    simp_all
  rw [← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card (Finset.union_subset
    Finset.inter_subset_right Finset.inter_subset_right)

private theorem sum_min_le_of_highCard
    {I : Type*} [Fintype I] [DecidableEq I]
    (rho : I → ℝ) (H : Finset I) (theta Delta eps : ℝ)
    (htheta0 : 0 ≤ theta)
    (hlow : ∀ j ∉ H, rho j ≤ theta)
    (hHcard : (H.card : ℝ) ≤ Delta)
    (hsum : |(∑ j, rho j) - Delta| ≤ eps) :
    ∑ j, min (rho j) (1 - rho j) ≤
      eps + 2 * theta * (Fintype.card I : ℝ) := by
  classical
  have hpoint (j : I) :
      min (rho j) (1 - rho j) ≤
        (if j ∈ H then (1 : ℝ) else 0) - rho j +
          2 * theta * (if j ∈ H then (0 : ℝ) else 1) := by
    by_cases hj : j ∈ H
    · simpa [hj] using (min_le_right (rho j) (1 - rho j))
    · simp [hj]
      have hm : min (rho j) (1 - rho j) ≤ rho j := min_le_left _ _
      nlinarith [hlow j hj]
  calc
    ∑ j, min (rho j) (1 - rho j) ≤
        ∑ j, ((if j ∈ H then (1 : ℝ) else 0) - rho j +
          2 * theta * (if j ∈ H then (0 : ℝ) else 1)) :=
      Finset.sum_le_sum fun j _ ↦ hpoint j
    _ = (H.card : ℝ) - ∑ j, rho j +
          2 * theta * ((Hᶜ).card : ℝ) := by
      have hzero :
          (∑ j : I, (if j ∈ H then (0 : ℝ) else 1)) = ((Hᶜ).card : ℝ) := by
        calc
          (∑ j : I, (if j ∈ H then (0 : ℝ) else 1)) =
              ∑ j : I, (if j ∉ H then (1 : ℝ) else 0) := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases hj : j ∈ H <;> simp [hj]
          _ = (({j ∈ (Finset.univ : Finset I) | j ∉ H}).card : ℝ) :=
            Finset.sum_boole (R := ℝ) (fun j : I ↦ j ∉ H) Finset.univ
          _ = ((Hᶜ).card : ℝ) := by
            congr 2
            ext j
            simp
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      rw [hzero]
      simp
    _ ≤ Delta - ∑ j, rho j +
          2 * theta * (Fintype.card I : ℝ) := by
      have hcomp : ((Hᶜ).card : ℝ) ≤ (Fintype.card I : ℝ) := by
        exact_mod_cast Finset.card_le_univ Hᶜ
      have hmul : 2 * theta * ((Hᶜ).card : ℝ) ≤
          2 * theta * (Fintype.card I : ℝ) :=
        mul_le_mul_of_nonneg_left hcomp (by positivity)
      linarith
    _ ≤ eps + 2 * theta * (Fintype.card I : ℝ) := by
      have habs : Delta - ∑ j, rho j ≤ eps := by
        have := le_trans (le_abs_self (Delta - ∑ j, rho j)) (by
          simpa [abs_sub_comm] using hsum)
        exact this
      linarith

private theorem redProfile_sum_close
    {n t k : ℕ} (hk : 3 ≤ k) (C : ColoredGraph (Fin n))
    (clusters : Fin t → Finset (Fin n)) (i : Fin t) (v : Fin n)
    (eta beta : ℝ)
    (hn : 0 < n) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (0 : ℝ) 1)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin t)) clusters)
    (hsize : ∀ j, eta * (n : ℝ) ≤ ((clusters j).card : ℝ))
    (hbalanced : ∀ a b,
      |((clusters a).card : ℝ) - ((clusters b).card : ℝ)| ≤ beta * (n : ℝ))
    (hownBlue : (1 - beta) * ((clusters i).card : ℝ) ≤
      (C.blueDegreeIn v (clusters i) : ℝ))
    (houtBlue : (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
      beta * (n : ℝ))
    (hweighted : |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
      beta * (n : ℝ)) :
    |(∑ j : Fin t,
        (C.redDegreeIn v (clusters j) : ℝ) / ((clusters j).card : ℝ)) -
      (delta k : ℝ)| ≤
      ((delta k : ℝ) + 2) * beta / eta ^ 2 := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have heta0 : 0 < eta := heta.1
  have heta1 : eta < 1 := heta.2
  have hbeta0 : 0 < beta := hbeta.1
  have hbeta1 : beta < 1 := hbeta.2
  have hDelta : 1 ≤ (delta k : ℝ) := by
    exact_mod_cast (show 1 ≤ delta k by simp [delta]; omega)
  have hcardpos (j : Fin t) : 0 < ((clusters j).card : ℝ) :=
    lt_of_lt_of_le (mul_pos heta0 hnR) (hsize j)
  have hcardle (j : Fin t) : ((clusters j).card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show (clusters j).card ≤ n by
      simpa using Finset.card_le_card (Finset.subset_univ (clusters j)))
  have htboundRaw :=
    card_mul_clusterLower_le_card clusters (eta * (n : ℝ)) hdisj hsize
  have htbound : (t : ℝ) ≤ 1 / eta := by
    rw [le_div_iff₀ heta0]
    have : (t : ℝ) * eta * (n : ℝ) ≤ (n : ℝ) := by
      simpa [mul_assoc] using htboundRaw
    nlinarith
  have hblueSplitNat := C.degreeIn_add_degreeIn_sdiff .blue v
    (cluster_subset_clusterUnion clusters i)
  have hblueSplit :
      (C.blueDegreeIn v (clusterUnion clusters) : ℝ) =
        (C.blueDegreeIn v (clusters i) : ℝ) +
          (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) := by
    exact_mod_cast hblueSplitNat.symm
  have hownBlueUpper : (C.blueDegreeIn v (clusters i) : ℝ) ≤
      ((clusters i).card : ℝ) := by
    exact_mod_cast degreeIn_le_card C .blue v (clusters i)
  have hblueLower :
      (1 - beta) * ((clusters i).card : ℝ) ≤
        (C.blueDegreeIn v (clusterUnion clusters) : ℝ) := by
    rw [hblueSplit]
    nlinarith
  have hblueUpper :
      (C.blueDegreeIn v (clusterUnion clusters) : ℝ) ≤
        ((clusters i).card : ℝ) + beta * (n : ℝ) := by
    rw [hblueSplit]
    linarith
  have hweighted' :
      |(C.redDegreeIn v (clusterUnion clusters) : ℝ) -
          (delta k : ℝ) * (C.blueDegreeIn v (clusterUnion clusters) : ℝ)| ≤
        beta * (n : ℝ) := by
    simpa [weightedDegreeIn] using hweighted
  have hredNear :
      |(C.redDegreeIn v (clusterUnion clusters) : ℝ) -
          (delta k : ℝ) * ((clusters i).card : ℝ)| ≤
        ((delta k : ℝ) + 1) * beta * (n : ℝ) := by
    have hDelta0 : 0 ≤ (delta k : ℝ) := by positivity
    have hDbeta0 : 0 ≤ (delta k : ℝ) * beta := mul_nonneg hDelta0 hbeta0.le
    have hblueLowerMul := mul_le_mul_of_nonneg_left hblueLower hDelta0
    have hblueUpperMul := mul_le_mul_of_nonneg_left hblueUpper hDelta0
    have hcardMul := mul_le_mul_of_nonneg_left (hcardle i) hDbeta0
    rw [abs_le] at hweighted' ⊢
    constructor <;> nlinarith
  let rho : Fin t → ℝ := fun j ↦
    (C.redDegreeIn v (clusters j) : ℝ) / ((clusters j).card : ℝ)
  have hrho0 (j : Fin t) : 0 ≤ rho j := by
    dsimp [rho]
    positivity
  have hrho1 (j : Fin t) : rho j ≤ 1 := by
    dsimp [rho]
    rw [div_le_one (hcardpos j)]
    exact_mod_cast degreeIn_le_card C .red v (clusters j)
  have hrhoMul (j : Fin t) :
      rho j * ((clusters j).card : ℝ) =
        (C.redDegreeIn v (clusters j) : ℝ) := by
    dsimp [rho]
    exact div_mul_cancel₀ _ (ne_of_gt (hcardpos j))
  have hterm (j : Fin t) :
      |((clusters i).card : ℝ) * rho j -
          (C.redDegreeIn v (clusters j) : ℝ)| ≤ beta * (n : ℝ) := by
    have hid :
        ((clusters i).card : ℝ) * rho j -
            (C.redDegreeIn v (clusters j) : ℝ) =
          rho j * (((clusters i).card : ℝ) - ((clusters j).card : ℝ)) := by
      rw [← hrhoMul j]
      ring
    rw [hid, abs_mul, abs_of_nonneg (hrho0 j)]
    have hbal := hbalanced i j
    nlinarith [mul_le_mul (hrho1 j) hbal (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  have hdisj' :
      ((Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint clusters := by
    simpa using hdisj
  have hredSumNat :=
    C.degreeIn_biUnion .red v (Finset.univ : Finset (Fin t)) clusters hdisj'
  have hredSum :
      (C.redDegreeIn v (clusterUnion clusters) : ℝ) =
        ∑ j : Fin t, (C.redDegreeIn v (clusters j) : ℝ) := by
    have hredSumNat' :
        C.redDegreeIn v (clusterUnion clusters) =
          ∑ j : Fin t, C.redDegreeIn v (clusters j) := by
      simpa [clusterUnion] using hredSumNat
    exact_mod_cast hredSumNat'
  have hsumError :
      |((clusters i).card : ℝ) * (∑ j : Fin t, rho j) -
          (C.redDegreeIn v (clusterUnion clusters) : ℝ)| ≤
        (t : ℝ) * beta * (n : ℝ) := by
    rw [hredSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      |∑ j : Fin t,
          (((clusters i).card : ℝ) * rho j -
            (C.redDegreeIn v (clusters j) : ℝ))| ≤
          ∑ j : Fin t,
            |((clusters i).card : ℝ) * rho j -
              (C.redDegreeIn v (clusters j) : ℝ)| := by
            simpa using Finset.abs_sum_le_sum_abs
              (fun j : Fin t ↦ ((clusters i).card : ℝ) * rho j -
                (C.redDegreeIn v (clusters j) : ℝ)) Finset.univ
      _ ≤ ∑ _j : Fin t, beta * (n : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ hterm j
      _ = (t : ℝ) * beta * (n : ℝ) := by simp; ring
  have hcombined :
      |((clusters i).card : ℝ) *
          ((∑ j : Fin t, rho j) - (delta k : ℝ))| ≤
        ((t : ℝ) + (delta k : ℝ) + 1) * beta * (n : ℝ) := by
    have hid :
        ((clusters i).card : ℝ) *
            ((∑ j : Fin t, rho j) - (delta k : ℝ)) =
          (((clusters i).card : ℝ) * (∑ j : Fin t, rho j) -
            (C.redDegreeIn v (clusterUnion clusters) : ℝ)) +
          ((C.redDegreeIn v (clusterUnion clusters) : ℝ) -
            (delta k : ℝ) * ((clusters i).card : ℝ)) := by ring
    rw [hid]
    calc
      |(((clusters i).card : ℝ) * (∑ j : Fin t, rho j) -
          (C.redDegreeIn v (clusterUnion clusters) : ℝ)) +
        ((C.redDegreeIn v (clusterUnion clusters) : ℝ) -
          (delta k : ℝ) * ((clusters i).card : ℝ))| ≤
          |((clusters i).card : ℝ) * (∑ j : Fin t, rho j) -
            (C.redDegreeIn v (clusterUnion clusters) : ℝ)| +
          |(C.redDegreeIn v (clusterUnion clusters) : ℝ) -
            (delta k : ℝ) * ((clusters i).card : ℝ)| := abs_add_le _ _
      _ ≤ (t : ℝ) * beta * (n : ℝ) +
          ((delta k : ℝ) + 1) * beta * (n : ℝ) :=
        add_le_add hsumError hredNear
      _ = ((t : ℝ) + (delta k : ℝ) + 1) * beta * (n : ℝ) := by ring
  have hDeltaPart : (delta k : ℝ) + 1 ≤
      ((delta k : ℝ) + 1) / eta := by
    rw [le_div_iff₀ heta0]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (delta k : ℝ) + 1)
      (by linarith : 0 ≤ 1 - eta)]
  have hcoeff : (t : ℝ) + (delta k : ℝ) + 1 ≤
      ((delta k : ℝ) + 2) / eta := by
    have hid : ((delta k : ℝ) + 2) / eta =
        1 / eta + ((delta k : ℝ) + 1) / eta := by ring
    rw [hid]
    linarith
  have hcombined' :
      |((clusters i).card : ℝ) *
          ((∑ j : Fin t, rho j) - (delta k : ℝ))| ≤
        ((delta k : ℝ) + 2) / eta * beta * (n : ℝ) := by
    exact hcombined.trans (by
      have hscale := mul_le_mul_of_nonneg_right hcoeff
        (mul_nonneg hbeta0.le hnR.le)
      simpa [mul_assoc] using hscale)
  have hscaled :
      eta * (n : ℝ) * |(∑ j : Fin t, rho j) - (delta k : ℝ)| ≤
        ((delta k : ℝ) + 2) / eta * beta * (n : ℝ) := by
    have hleft := mul_le_mul_of_nonneg_right (hsize i)
      (abs_nonneg ((∑ j : Fin t, rho j) - (delta k : ℝ)))
    have habsMul :
        |((clusters i).card : ℝ) *
            ((∑ j : Fin t, rho j) - (delta k : ℝ))| =
          ((clusters i).card : ℝ) *
            |(∑ j : Fin t, rho j) - (delta k : ℝ)| := by
      rw [abs_mul, abs_of_pos (hcardpos i)]
    rw [← habsMul] at hleft
    exact hleft.trans hcombined'
  have hmulEta := mul_le_mul_of_nonneg_left hscaled heta0.le
  have hmulN :
      (n : ℝ) *
          (eta ^ 2 * |(∑ j : Fin t, rho j) - (delta k : ℝ)|) ≤
        (n : ℝ) * (((delta k : ℝ) + 2) * beta) := by
    calc
      (n : ℝ) *
          (eta ^ 2 * |(∑ j : Fin t, rho j) - (delta k : ℝ)|) =
        eta * (eta * (n : ℝ) *
          |(∑ j : Fin t, rho j) - (delta k : ℝ)|) := by ring
      _ ≤ eta * (((delta k : ℝ) + 2) / eta * beta * (n : ℝ)) := hmulEta
      _ = (n : ℝ) * (((delta k : ℝ) + 2) * beta) := by
        field_simp
        <;> ring
  have hcancel :
      eta ^ 2 * |(∑ j : Fin t, rho j) - (delta k : ℝ)| ≤
        ((delta k : ℝ) + 2) * beta :=
    (mul_le_mul_iff_of_pos_left hnR).mp hmulN
  change |(∑ j : Fin t, rho j) - (delta k : ℝ)| ≤
    ((delta k : ℝ) + 2) * beta / eta ^ 2
  exact (le_div_iff₀ (sq_pos_of_pos heta0)).2 (by
    simpa [mul_comm] using hcancel)

/-- Stage I of the between-cluster dominant-color argument, conditional on
the transversal step that bounds the number of high-red clusters. -/
theorem vertexRedProfileMixedMass_of_highCard
    {n t k : ℕ} (hk : 3 ≤ k) (C : ColoredGraph (Fin n))
    (clusters : Fin t → Finset (Fin n)) (i : Fin t) (v : Fin n)
    (eta beta : ℝ)
    (hn : 0 < n) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (0 : ℝ) 1)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin t)) clusters)
    (hsize : ∀ j, eta * (n : ℝ) ≤ ((clusters j).card : ℝ))
    (hbalanced : ∀ a b,
      |((clusters a).card : ℝ) - ((clusters b).card : ℝ)| ≤ beta * (n : ℝ))
    (hv : v ∈ clusters i)
    (hownBlue : (1 - beta) * ((clusters i).card : ℝ) ≤
      (C.blueDegreeIn v (clusters i) : ℝ))
    (houtBlue : (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
      beta * (n : ℝ))
    (hweighted : |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
      beta * (n : ℝ))
    (hhighCard :
      ({j : Fin t |
        j ≠ i ∧
          8 * (delta k : ℝ) * Real.sqrt beta ≤
            (C.redDegreeIn v (clusters j) : ℝ) /
              ((clusters j).card : ℝ)} : Finset (Fin t)).card ≤ delta k) :
    ∑ j : Fin t,
        min ((C.redDegreeIn v (clusters j) : ℝ) / ((clusters j).card : ℝ))
          (1 - (C.redDegreeIn v (clusters j) : ℝ) /
            ((clusters j).card : ℝ)) ≤
      20 * (k : ℝ) * Real.sqrt beta / eta ^ 2 := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have heta0 : 0 < eta := heta.1
  have heta1 : eta < 1 := heta.2
  have hbeta0 : 0 < beta := hbeta.1
  have hbeta1 : beta < 1 := hbeta.2
  have hDelta : 1 ≤ (delta k : ℝ) := by
    exact_mod_cast (show 1 ≤ delta k by simp [delta]; omega)
  have hq0 : 0 ≤ Real.sqrt beta := Real.sqrt_nonneg beta
  have hqpos : 0 < Real.sqrt beta := Real.sqrt_pos.2 hbeta0
  have hqsq : (Real.sqrt beta) ^ 2 = beta := Real.sq_sqrt hbeta0.le
  have hbetaq : beta ≤ Real.sqrt beta := by
    have hqle : Real.sqrt beta ≤ 1 := Real.sqrt_le_one.mpr hbeta1.le
    nlinarith
  have hcardpos (j : Fin t) : 0 < ((clusters j).card : ℝ) :=
    lt_of_lt_of_le (mul_pos heta0 hnR) (hsize j)
  let rho : Fin t → ℝ := fun j ↦
    (C.redDegreeIn v (clusters j) : ℝ) / ((clusters j).card : ℝ)
  let theta : ℝ := 8 * (delta k : ℝ) * Real.sqrt beta
  let H : Finset (Fin t) := Finset.univ.filter fun j ↦
    j ≠ i ∧ theta ≤ rho j
  have htheta0 : 0 ≤ theta := by
    dsimp [theta]
    positivity
  have hthetaBeta : beta ≤ theta := by
    dsimp [theta]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (delta k : ℝ) - 1) hq0]
  have hrho0 (j : Fin t) : 0 ≤ rho j := by
    dsimp [rho]
    positivity
  have hrho1 (j : Fin t) : rho j ≤ 1 := by
    dsimp [rho]
    rw [div_le_one (hcardpos j)]
    exact_mod_cast degreeIn_le_card C .red v (clusters j)
  have hownRedBlueNat := redDegreeIn_add_blueDegreeIn_le_card C v (clusters i)
  have hownRedBlue :
      (C.redDegreeIn v (clusters i) : ℝ) +
          (C.blueDegreeIn v (clusters i) : ℝ) ≤
        ((clusters i).card : ℝ) := by
    exact_mod_cast hownRedBlueNat
  have hownRho : rho i ≤ beta := by
    have hred : (C.redDegreeIn v (clusters i) : ℝ) ≤
        beta * ((clusters i).card : ℝ) := by
      nlinarith
    dsimp [rho]
    rw [div_le_iff₀ (hcardpos i)]
    simpa [mul_comm] using hred
  have hlow (j : Fin t) (hj : j ∉ H) : rho j ≤ theta := by
    by_cases hji : j = i
    · subst j
      exact hownRho.trans hthetaBeta
    · have : ¬theta ≤ rho j := by
        simpa [H, hji] using hj
      exact le_of_lt (lt_of_not_ge this)
  have hHcard : (H.card : ℝ) ≤ (delta k : ℝ) := by
    exact_mod_cast (show H.card ≤ delta k by
      simpa [H, theta, rho] using hhighCard)
  have hsum :
      |(∑ j : Fin t, rho j) - (delta k : ℝ)| ≤
        ((delta k : ℝ) + 2) * beta / eta ^ 2 := by
    simpa [rho] using redProfile_sum_close hk C clusters i v eta beta hn heta hbeta
      hdisj hsize hbalanced hownBlue houtBlue hweighted
  have hmixed := sum_min_le_of_highCard rho H theta (delta k : ℝ)
    (((delta k : ℝ) + 2) * beta / eta ^ 2) htheta0 hlow hHcard hsum
  have htboundRaw :=
    card_mul_clusterLower_le_card clusters (eta * (n : ℝ)) hdisj hsize
  have htbound : (t : ℝ) ≤ 1 / eta := by
    rw [le_div_iff₀ heta0]
    have : (t : ℝ) * eta * (n : ℝ) ≤ (n : ℝ) := by
      simpa [mul_assoc] using htboundRaw
    nlinarith
  have hthetaTerm :
      2 * theta * (t : ℝ) ≤
        16 * (delta k : ℝ) * Real.sqrt beta / eta ^ 2 := by
    have hfirst :
        2 * theta * (t : ℝ) ≤
          16 * (delta k : ℝ) * Real.sqrt beta * (1 / eta) := by
      have hcoef0 : 0 ≤ 16 * (delta k : ℝ) * Real.sqrt beta := by positivity
      dsimp [theta]
      nlinarith [mul_le_mul_of_nonneg_left htbound hcoef0]
    have hetaSqLe : eta ^ 2 ≤ eta := by
      nlinarith [mul_pos heta0 (sub_pos.mpr heta1)]
    have hinv : 1 / eta ≤ 1 / eta ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos heta0) hetaSqLe
    have hcoef0 : 0 ≤ 16 * (delta k : ℝ) * Real.sqrt beta := by positivity
    calc
      2 * theta * (t : ℝ) ≤
          16 * (delta k : ℝ) * Real.sqrt beta * (1 / eta) := hfirst
      _ ≤ 16 * (delta k : ℝ) * Real.sqrt beta * (1 / eta ^ 2) :=
        mul_le_mul_of_nonneg_left hinv hcoef0
      _ = 16 * (delta k : ℝ) * Real.sqrt beta / eta ^ 2 := by ring
  have heps :
      ((delta k : ℝ) + 2) * beta / eta ^ 2 ≤
        ((delta k : ℝ) + 2) * Real.sqrt beta / eta ^ 2 := by
    gcongr
  have hpre :
      ∑ j : Fin t, min (rho j) (1 - rho j) ≤
        (17 * (delta k : ℝ) + 2) * Real.sqrt beta / eta ^ 2 := by
    have hmixed' :
        ∑ j : Fin t, min (rho j) (1 - rho j) ≤
          ((delta k : ℝ) + 2) * beta / eta ^ 2 +
            2 * theta * (t : ℝ) := by
      simpa using hmixed
    calc
      ∑ j : Fin t, min (rho j) (1 - rho j) ≤
          ((delta k : ℝ) + 2) * beta / eta ^ 2 +
            2 * theta * (t : ℝ) := hmixed'
      _ ≤ ((delta k : ℝ) + 2) * Real.sqrt beta / eta ^ 2 +
            16 * (delta k : ℝ) * Real.sqrt beta / eta ^ 2 :=
        add_le_add heps hthetaTerm
      _ = (17 * (delta k : ℝ) + 2) * Real.sqrt beta / eta ^ 2 := by ring
  have hDle : (delta k : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.sub_le k 2
  have hcoef : 17 * (delta k : ℝ) + 2 ≤ 20 * (k : ℝ) := by
    have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hscale : 0 ≤ Real.sqrt beta / eta ^ 2 := by positivity
  change ∑ j : Fin t, min (rho j) (1 - rho j) ≤ _
  calc
    ∑ j : Fin t, min (rho j) (1 - rho j) ≤
        (17 * (delta k : ℝ) + 2) * Real.sqrt beta / eta ^ 2 := hpre
    _ = (17 * (delta k : ℝ) + 2) * (Real.sqrt beta / eta ^ 2) := by ring
    _ ≤ (20 * (k : ℝ)) * (Real.sqrt beta / eta ^ 2) :=
      mul_le_mul_of_nonneg_right hcoef hscale
    _ = 20 * (k : ℝ) * Real.sqrt beta / eta ^ 2 := by ring

/-- The vertexwise red-profile mixed-mass estimate at the heart of the
between-cluster dominant-color lemma.

The high-red cluster bound is supplied by the finite transversal argument
above; the remaining estimates use only restricted degrees and the cluster
size hypotheses.

Paper: the vertexwise estimate in Lemma `lemma:vertex-level-mixed-mass`. -/
theorem vertexRedProfileMixedMass
    {n t k : ℕ} (hk : 3 ≤ k) (C : ColoredGraph (Fin n)) (hC : C ∈ Ck k n)
    (clusters : Fin t → Finset (Fin n)) (i : Fin t) (v : Fin n)
    (eta beta : ℝ)
    (hn : 0 < n) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (0 : ℝ) 1)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin t)) clusters)
    (hsize : ∀ j, eta * (n : ℝ) ≤ ((clusters j).card : ℝ))
    (hbalanced : ∀ a b,
      |((clusters a).card : ℝ) - ((clusters b).card : ℝ)| ≤ beta * (n : ℝ))
    (hblue : ∀ a b, a ≠ b →
      C.colorDensity .blue (clusters a) (clusters b) ≤ beta)
    (hv : v ∈ clusters i)
    (hownBlue : (1 - beta) * ((clusters i).card : ℝ) ≤
      (C.blueDegreeIn v (clusters i) : ℝ))
    (houtBlue :
      (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
        beta * (n : ℝ))
    (hweighted :
      |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
        beta * (n : ℝ)) :
    ∑ j : Fin t,
        min ((C.redDegreeIn v (clusters j) : ℝ) / ((clusters j).card : ℝ))
          (1 - (C.redDegreeIn v (clusters j) : ℝ) /
            ((clusters j).card : ℝ)) ≤
      20 * (k : ℝ) * Real.sqrt beta / eta ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnonempty (j : Fin t) : (clusters j).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hj
    have hjzero : ((clusters j).card : ℝ) = 0 := by simp [hj]
    have := hsize j
    rw [hjzero] at this
    nlinarith [mul_pos heta.1 hnR]
  have hhigh := highRedClusterIndices_card_le_delta k hk hbeta.1 hC
    clusters hdisj hnonempty hblue i v hv
  apply vertexRedProfileMixedMass_of_highCard hk C clusters i v eta beta hn heta hbeta
    hdisj hsize hbalanced hv hownBlue houtBlue hweighted
  change
    ({j : Fin t |
      j ≠ i ∧
        8 * (delta k : ℝ) * Real.sqrt beta ≤
          (C.redDegreeIn v (clusters j) : ℝ) /
            ((clusters j).card : ℝ)} : Finset (Fin t)).card ≤ delta k at hhigh
  exact hhigh

/-! ## Explicit constants for the paper-facing theorem -/





/-- A convenient explicit constant for the vertex-profile mixed-mass bound. -/
def mixedMassConstant (k : ℕ) : ℝ := 20 * k

/-- The constant exported by the between-cluster dominant-color estimate. -/
def dominantColorConstant (k : ℕ) : ℝ := 10 * mixedMassConstant k

/-- An explicit smallness threshold ensuring that the Stage II error is at
most `1 / 100`. -/
noncomputable def dominantColorBeta₀ (k : ℕ) (eta : ℝ) : ℝ :=
  min 1 ((eta ^ 2 / (100 * mixedMassConstant k)) ^ 2)

/-- The vertex-profile error at the scale used by Stage II. -/
noncomputable def mixedMassScale (k : ℕ) (eta beta : ℝ) : ℝ :=
  mixedMassConstant k * √beta / eta ^ 2

theorem mixedMassConstant_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < mixedMassConstant k := by
  rw [mixedMassConstant]
  positivity

theorem dominantColorBeta₀_pos {k : ℕ} {eta : ℝ} (hk : 3 ≤ k)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) :
    0 < dominantColorBeta₀ k eta := by
  rw [dominantColorBeta₀, lt_min_iff]
  constructor
  · norm_num
  · have hC : 0 < mixedMassConstant k := mixedMassConstant_pos hk
    have hquot : 0 < eta ^ 2 / (100 * mixedMassConstant k) := by
      exact div_pos (sq_pos_of_pos heta.1) (mul_pos (by norm_num) hC)
    positivity

theorem beta_lt_one_of_lt_dominantColorBeta₀ {k : ℕ} {eta beta : ℝ}
    (hbeta : beta < dominantColorBeta₀ k eta) : beta < 1 := by
  exact lt_of_lt_of_le hbeta (min_le_left _ _)

theorem mixedMassScale_pos {k : ℕ} {eta beta : ℝ} (hk : 3 ≤ k)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) (hbeta : 0 < beta) :
    0 < mixedMassScale k eta beta := by
  rw [mixedMassScale]
  have hC : 0 < mixedMassConstant k := mixedMassConstant_pos hk
  have hsqrt : 0 < √beta := Real.sqrt_pos.2 hbeta
  exact div_pos (mul_pos hC hsqrt) (sq_pos_of_pos heta.1)

theorem beta_le_mixedMassScale {k : ℕ} {eta beta : ℝ} (hk : 3 ≤ k)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) (hbeta0 : 0 < beta)
    (hbeta1 : beta < 1) :
    beta ≤ mixedMassScale k eta beta := by
  rw [mixedMassScale]
  have hC : 1 ≤ mixedMassConstant k := by
    have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rw [mixedMassConstant]
    push_cast
    nlinarith
  have hsqrt : beta ≤ √beta := by
    nlinarith [Real.sq_sqrt hbeta0.le, Real.sqrt_nonneg beta]
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta.1
  rw [le_div_iff₀ heta2]
  have hprod : 0 ≤ eta * (1 - eta) :=
    mul_nonneg heta.1.le (sub_nonneg.mpr heta.2.le)
  have heta2le : eta ^ 2 ≤ 1 := by nlinarith
  calc
    beta * eta ^ 2 ≤ beta * 1 :=
      mul_le_mul_of_nonneg_left heta2le hbeta0.le
    _ = beta := by ring
    _ ≤ √beta := hsqrt
    _ = 1 * √beta := by ring
    _ ≤ mixedMassConstant k * √beta :=
      mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg beta)

theorem mixedMassScale_le_one_hundredth {k : ℕ} {eta beta : ℝ}
    (hk : 3 ≤ k) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta0 : 0 ≤ beta) (hbeta : beta < dominantColorBeta₀ k eta) :
    mixedMassScale k eta beta ≤ 1 / 100 := by
  have hC : 0 < mixedMassConstant k := mixedMassConstant_pos hk
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta.1
  have hthreshold :
      beta < (eta ^ 2 / (100 * mixedMassConstant k)) ^ 2 :=
    lt_of_lt_of_le hbeta (min_le_right _ _)
  have hquot : 0 < eta ^ 2 / (100 * mixedMassConstant k) := by
    positivity
  have hsqrt : √beta < eta ^ 2 / (100 * mixedMassConstant k) :=
    (Real.sqrt_lt' hquot).2 hthreshold
  rw [mixedMassScale, div_le_iff₀ heta2]
  have hden : 0 < 100 * mixedMassConstant k := mul_pos (by norm_num) hC
  have hmul : √beta * (100 * mixedMassConstant k) < eta ^ 2 :=
    (lt_div_iff₀ hden).mp hsqrt
  norm_num at hmul ⊢
  nlinarith

theorem dominantColorConstant_ge_one {k : ℕ} (hk : 3 ≤ k) :
    1 ≤ dominantColorConstant k := by
  rw [dominantColorConstant, mixedMassConstant]
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  push_cast
  nlinarith

theorem ten_mul_mixedMassScale {k : ℕ} {eta beta : ℝ} :
    10 * mixedMassScale k eta beta =
      dominantColorConstant k * √beta / eta ^ 2 := by
  rw [mixedMassScale, dominantColorConstant]
  ring

/-- All scalar consequences of the explicit Stage II parameter choices. -/
theorem dominantColorParameterBounds {k : ℕ} {eta beta : ℝ}
    (hk : 3 ≤ k) (heta : eta ∈ Set.Ioo (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (0 : ℝ) (dominantColorBeta₀ k eta)) :
    beta < 1 ∧
      beta ≤ mixedMassScale k eta beta ∧
      0 < mixedMassScale k eta beta ∧
      mixedMassScale k eta beta ≤ 1 / 100 ∧
      0 < dominantColorBeta₀ k eta ∧
      1 ≤ dominantColorConstant k ∧
      10 * mixedMassScale k eta beta =
        dominantColorConstant k * √beta / eta ^ 2 := by
  have hbeta1 : beta < 1 :=
    beta_lt_one_of_lt_dominantColorBeta₀ hbeta.2
  exact ⟨hbeta1,
    beta_le_mixedMassScale hk heta hbeta.1 hbeta1,
    mixedMassScale_pos hk heta hbeta.1,
    mixedMassScale_le_one_hundredth hk heta hbeta.1.le hbeta.2,
    dominantColorBeta₀_pos hk heta,
    dominantColorConstant_ge_one hk,
    ten_mul_mixedMassScale⟩

/-- Explicit-constant form of the vertex-level mixed-mass lemma.  This is the
adapter used by later parameter hierarchies: the admissible interval is exactly
`dominantColorBeta₀ k eta`, the error constant is exactly
`dominantColorConstant k`, and the proof works with the uniform threshold
`n₀ = 1`.

Paper: Lemma `lemma:vertex-level-mixed-mass`. -/
theorem vertexLevelMixedMassExplicit (k : ℕ) (hk : 3 ≤ k) (eta : ℝ)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) (beta : ℝ)
    (hbeta : beta ∈ Set.Ioo (0 : ℝ) (dominantColorBeta₀ k eta)) :
    ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
        ∀ t : ℕ, k - 1 ≤ t →
          ∀ clusters : Fin t → Finset (Fin n),
            Set.PairwiseDisjoint (Set.univ : Set (Fin t)) clusters →
            (∀ i, eta * (n : ℝ) ≤ ((clusters i).card : ℝ)) →
            (∀ i j,
              |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| ≤
                beta * (n : ℝ)) →
            (∀ i j, i ≠ j →
              C.colorDensity .blue (clusters i) (clusters j) ≤ beta) →
            (∀ i v, v ∈ clusters i →
              (1 - beta) * ((clusters i).card : ℝ) ≤
                  (C.blueDegreeIn v (clusters i) : ℝ) ∧
              (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
                  beta * (n : ℝ) ∧
              |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
                  beta * (n : ℝ)) →
            ∀ i j, i ≠ j →
              1 - dominantColorConstant k * Real.sqrt beta / eta ^ 2 ≤
                max (C.colorDensity .red (clusters i) (clusters j))
                  (C.colorDensity .green (clusters i) (clusters j)) := by
  refine ⟨1, ?_⟩
  intro n hn C hC t _ht clusters hdisj hsize hbalanced hblue hvertex i j hij
  have hnpos : 0 < n := by omega
  obtain ⟨hbeta1, hbetaMu, hmu, _hmuSmall, _hbeta₀pos, _hK, hten⟩ :=
    dominantColorParameterBounds hk heta hbeta
  have hbeta' : beta ∈ Set.Ioo (0 : ℝ) 1 := ⟨hbeta.1, hbeta1⟩
  have hnonempty (a : Fin t) : (clusters a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro ha
    have hazero : ((clusters a).card : ℝ) = 0 := by simp [ha]
    have hs := hsize a
    rw [hazero] at hs
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    nlinarith [mul_pos heta.1 hnR]
  let mu := mixedMassScale k eta beta
  have hprofile (a : Fin t) (v : Fin n) (hv : v ∈ clusters a) :
      ∑ q : Fin t,
          min ((C.redDegreeIn v (clusters q) : ℝ) / ((clusters q).card : ℝ))
            (1 - (C.redDegreeIn v (clusters q) : ℝ) /
              ((clusters q).card : ℝ)) ≤ mu := by
    obtain ⟨hown, hout, hweighted⟩ := hvertex a v hv
    have h := vertexRedProfileMixedMass hk C hC clusters a v eta beta hnpos heta
      hbeta' hdisj hsize hbalanced hblue hv hown hout hweighted
    simpa [mu, mixedMassScale, mixedMassConstant] using h
  have hrowMixed (a b : Fin t) (v : Fin n) (hv : v ∈ clusters a) :
      min (C.colorDegreeRatio .red v (clusters b))
        (1 - C.colorDegreeRatio .red v (clusters b)) ≤ mu := by
    let f : Fin t → ℝ := fun q ↦
      min ((C.redDegreeIn v (clusters q) : ℝ) / ((clusters q).card : ℝ))
        (1 - (C.redDegreeIn v (clusters q) : ℝ) / ((clusters q).card : ℝ))
    have hf0 (q : Fin t) : 0 ≤ f q := by
      have hcardpos : 0 < ((clusters q).card : ℝ) := by
        exact_mod_cast (hnonempty q).card_pos
      have hrho0 : 0 ≤
          (C.redDegreeIn v (clusters q) : ℝ) / ((clusters q).card : ℝ) := by
        positivity
      have hrho1 :
          (C.redDegreeIn v (clusters q) : ℝ) / ((clusters q).card : ℝ) ≤ 1 := by
        rw [div_le_one hcardpos]
        exact_mod_cast degreeIn_le_card C .red v (clusters q)
      exact le_min hrho0 (sub_nonneg.mpr hrho1)
    have hsingle : f b ≤ ∑ q : Fin t, f q :=
      Finset.single_le_sum (fun q _ ↦ hf0 q) (Finset.mem_univ b)
    have hsum : ∑ q : Fin t, f q ≤ mu := by
      simpa [f] using hprofile a v hv
    simpa [f, colorDegreeRatio] using hsingle.trans hsum
  have hST : Disjoint (clusters i) (clusters j) :=
    hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  have hdom := colorDensity_dominant_of_vertexMixedMass C (clusters i) (clusters j)
    (hnonempty i) (hnonempty j) hST mu hmu
    ((hblue i j hij).trans hbetaMu)
    (fun v hv ↦ hrowMixed i j v hv)
    (fun v hv ↦ hrowMixed j i v hv)
  rw [hten] at hdom
  exact hdom

/-- Between any two distinct clusters, one of red and green has density close
to one.  The constants are explicit: `dominantColorConstant k = 200 * k`,
`dominantColorBeta₀ k eta` depends only on `k, eta`, and the proof works with
the uniform threshold `n₀ = 1`.

This existential paper-facing formulation is retained for compatibility;
`vertexLevelMixedMassExplicit` exposes its concrete witnesses directly.

Paper: Lemma `lemma:vertex-level-mixed-mass`. -/
theorem vertexLevelMixedMass (k : ℕ) (hk : 3 ≤ k) (eta : ℝ)
    (heta : eta ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ beta₀ K : ℝ, 0 < beta₀ ∧ 1 ≤ K ∧
      ∀ beta ∈ Set.Ioo (0 : ℝ) beta₀, ∃ n₀ : ℕ,
        ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
          ∀ t : ℕ, k - 1 ≤ t →
            ∀ clusters : Fin t → Finset (Fin n),
              Set.PairwiseDisjoint (Set.univ : Set (Fin t)) clusters →
              (∀ i, eta * (n : ℝ) ≤ ((clusters i).card : ℝ)) →
              (∀ i j,
                |((clusters i).card : ℝ) - ((clusters j).card : ℝ)| ≤
                  beta * (n : ℝ)) →
              (∀ i j, i ≠ j →
                C.colorDensity .blue (clusters i) (clusters j) ≤ beta) →
              (∀ i v, v ∈ clusters i →
                (1 - beta) * ((clusters i).card : ℝ) ≤
                    (C.blueDegreeIn v (clusters i) : ℝ) ∧
                (C.blueDegreeIn v (clusterUnion clusters \ clusters i) : ℝ) ≤
                    beta * (n : ℝ) ∧
                |(weightedDegreeIn k C v (clusterUnion clusters) : ℝ)| ≤
                    beta * (n : ℝ)) →
              ∀ i j, i ≠ j →
                1 - K * Real.sqrt beta / eta ^ 2 ≤
                  max (C.colorDensity .red (clusters i) (clusters j))
                    (C.colorDensity .green (clusters i) (clusters j)) := by
  refine ⟨dominantColorBeta₀ k eta, dominantColorConstant k,
    dominantColorBeta₀_pos hk heta, dominantColorConstant_ge_one hk, ?_⟩
  intro beta hbeta
  exact vertexLevelMixedMassExplicit k hk eta heta beta hbeta

end ColoredGraph

end InducedStars
