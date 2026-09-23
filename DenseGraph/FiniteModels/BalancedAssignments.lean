import DenseGraph.FiniteModels.BalancedPartition
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

/-!
# Balanced multipartite capacities and assignments

This file packages the elementary finite combinatorics of balanced ordered
partitions.  It is independent of the induced-star application.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DenseGraph

/-- Splitting unordered pairs across two disjoint blocks. -/
theorem choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
      change Nat.choose ((a + b) + 1) 2 =
        Nat.choose a 2 + a * (b + 1) + Nat.choose (b + 1) 2
      rw [Nat.choose_succ_succ, ih, Nat.choose_succ_succ]
      simp [Nat.choose_one_right, Nat.mul_succ] at *
      omega

/-- The number of cross pairs in a balanced ordered partition of `q` points
into `r` parts.  This is the Turán number, including Mathlib's harmless
`r = 0` convention. -/
def balancedMultipartiteCrossCapacity (r q : ℕ) : ℕ :=
  SimpleGraph.turanNumber q r

/-- The complementary within-part capacity of a balanced ordered partition. -/
def balancedMultipartiteInternalCapacity (r q : ℕ) : ℕ :=
  q.choose 2 - balancedMultipartiteCrossCapacity r q

@[simp] theorem balancedMultipartiteCrossCapacity_eq_turanNumber (r q : ℕ) :
    balancedMultipartiteCrossCapacity r q = SimpleGraph.turanNumber q r :=
  rfl

/-- Exact quotient/remainder formula for balanced cross capacity. -/
theorem balancedMultipartiteCrossCapacity_eq (r q : ℕ) :
    balancedMultipartiteCrossCapacity r q =
      (q ^ 2 - (q % r) ^ 2) * (r - 1) / (2 * r) +
        (q % r).choose 2 := by
  simpa [balancedMultipartiteCrossCapacity] using
    (SimpleGraph.turanNumber_eq (n := q) (r := r))

/-- Exact quotient/remainder formula for balanced internal capacity. -/
theorem balancedMultipartiteInternalCapacity_eq (r q : ℕ) :
    balancedMultipartiteInternalCapacity r q =
      q.choose 2 -
        ((q ^ 2 - (q % r) ^ 2) * (r - 1) / (2 * r) +
          (q % r).choose 2) := by
  rw [balancedMultipartiteInternalCapacity,
    balancedMultipartiteCrossCapacity_eq]

/-- Balanced cross and internal coordinates partition all unordered pairs. -/
theorem balancedCross_add_internal (r q : ℕ) :
    balancedMultipartiteCrossCapacity r q +
        balancedMultipartiteInternalCapacity r q = q.choose 2 := by
  unfold balancedMultipartiteInternalCapacity
  apply Nat.add_sub_of_le
  simpa [balancedMultipartiteCrossCapacity] using
    (SimpleGraph.card_edgeFinset_le_card_choose_two
      (G := SimpleGraph.turanGraph q r))

/-- Cross capacity of an ordered size vector.  Encoding the vector as a
complete multipartite graph makes the extremal comparison with the Turán
graph available without any choice of concrete vertex labels. -/
def multipartiteCrossCapacity {r : ℕ} (a : Fin r → ℕ) : ℕ :=
  #(SimpleGraph.completeMultipartiteGraph (fun i ↦ Fin (a i))).edgeFinset

/-- The explicit sum over unordered pairs of indices underlying
`multipartiteCrossCapacity`. -/
def multipartiteCrossPairSum {r : ℕ} (a : Fin r → ℕ) : ℕ :=
  ∑ p ∈ ((Finset.univ ×ˢ Finset.univ).filter
    fun p : Fin r × Fin r ↦ p.1 < p.2), a p.1 * a p.2

/-- Every ordered `r`-part size vector has at most the balanced cross
capacity for its total number of points. -/
theorem multipartiteCrossCapacity_le_balanced {r : ℕ} (a : Fin r → ℕ) :
    multipartiteCrossCapacity a ≤
      balancedMultipartiteCrossCapacity r (∑ i, a i) := by
  let G := SimpleGraph.completeMultipartiteGraph (fun i : Fin r ↦ Fin (a i))
  have hfree : G.CliqueFree (r + 1) :=
    SimpleGraph.cliqueFree_completeMultipartiteGraph
      (fun i : Fin r ↦ Fin (a i)) (by simp)
  have h := hfree.card_edgeFinset_le (r := r)
  simpa [G, multipartiteCrossCapacity,
    balancedMultipartiteCrossCapacity] using h

/-- Paper-facing formulation of balanced multipartite extremality. -/
theorem balancedMultipartiteCrossCapacity_max {r q : ℕ}
    (a : Fin r → ℕ) (hsum : ∑ i, a i = q) :
    multipartiteCrossCapacity a ≤ balancedMultipartiteCrossCapacity r q := by
  simpa [hsum] using multipartiteCrossCapacity_le_balanced a

private theorem degree_completeMultipartite_sizeVector {r : ℕ}
    (a : Fin r → ℕ) (v : Sigma fun i : Fin r ↦ Fin (a i)) :
    (SimpleGraph.completeMultipartiteGraph
      (fun i : Fin r ↦ Fin (a i))).degree v =
      ∑ j ∈ Finset.univ.filter (· ≠ v.1), a j := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rw [SimpleGraph.neighborFinset_eq_filter]
  simp only [SimpleGraph.comap_adj, SimpleGraph.top_adj]
  change ((Finset.univ : Finset (Sigma fun i : Fin r ↦ Fin (a i))).filter
      fun x ↦ v.1 ≠ x.1).card = _
  rw [← Finset.univ_sigma_univ, Finset.filter_sigma]
  rw [Finset.card_sigma]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hjv : j = v.1 <;> simp [hjv, ne_comm]

private theorem sum_degree_completeMultipartite_sizeVector {r : ℕ}
    (a : Fin r → ℕ) :
    (∑ v : Sigma fun i : Fin r ↦ Fin (a i),
        (SimpleGraph.completeMultipartiteGraph
          (fun i : Fin r ↦ Fin (a i))).degree v) =
      ∑ i : Fin r, a i * ∑ j ∈ Finset.univ.filter (· ≠ i), a j := by
  rw [Fintype.sum_sigma]
  simp_rw [degree_completeMultipartite_sizeVector]
  simp

private theorem sum_offDiag_sizeVector_eq_two_mul_crossPairSum {r : ℕ}
    (a : Fin r → ℕ) :
    (∑ i : Fin r, a i * ∑ j ∈ Finset.univ.filter (· ≠ i), a j) =
      2 * multipartiteCrossPairSum a := by
  let pairs : Finset (Fin r × Fin r) := Finset.univ ×ˢ Finset.univ
  let ltPairs : Finset (Fin r × Fin r) :=
    pairs.filter fun p ↦ p.1 < p.2
  let gtPairs : Finset (Fin r × Fin r) :=
    pairs.filter fun p ↦ p.2 < p.1
  have hordered :
      (∑ i : Fin r, a i * ∑ j ∈ Finset.univ.filter (· ≠ i), a j) =
        ∑ p ∈ pairs, if p.1 ≠ p.2 then a p.1 * a p.2 else 0 := by
    conv_lhs =>
      enter [2, i]
      rw [Finset.mul_sum]
    simp_rw [Finset.sum_filter]
    simpa [pairs, ne_comm] using
      (Fintype.sum_prod_type
        (fun p : Fin r × Fin r ↦
          if p.1 ≠ p.2 then a p.1 * a p.2 else 0)).symm
  have hsplit :
      (∑ p ∈ pairs, if p.1 ≠ p.2 then a p.1 * a p.2 else 0) =
        (∑ p ∈ ltPairs, a p.1 * a p.2) +
          ∑ p ∈ gtPairs, a p.1 * a p.2 := by
    simp only [ltPairs, gtPairs]
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · simp [hlt, ne_of_lt hlt, not_lt_of_ge hlt.le]
    · simp [heq]
    · simp [hgt, ne_of_gt hgt, not_lt_of_ge hgt.le]
  have hswap :
      (∑ p ∈ gtPairs, a p.1 * a p.2) =
        ∑ p ∈ ltPairs, a p.1 * a p.2 := by
    apply Finset.sum_bij (fun p _ ↦ (p.2, p.1))
    · intro p hp
      simp [ltPairs, gtPairs, pairs] at hp ⊢
      exact hp
    · intro p hp q hq hpq
      exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
    · intro p hp
      refine ⟨(p.2, p.1), ?_, Prod.ext rfl rfl⟩
      simpa [ltPairs, gtPairs, pairs] using hp
    · intro p _hp
      exact Nat.mul_comm _ _
  rw [hordered, hsplit, hswap]
  simp [multipartiteCrossPairSum, ltPairs, pairs, two_mul]

private theorem sum_sizeVector_mul_self {r : ℕ} (a : Fin r → ℕ) :
    (∑ i, a i) * (∑ j, a j) =
      (∑ i, a i * a i) + 2 * multipartiteCrossPairSum a := by
  let S := ∑ i, a i
  have hrow (i : Fin r) :
      a i * S = a i * a i +
        a i * ∑ j ∈ Finset.univ.filter (· ≠ i), a j := by
    have hsum : S = a i +
        ∑ j ∈ Finset.univ.filter (· ≠ i), a j := by
      rw [Finset.filter_ne']
      simpa [S, Nat.add_comm] using
        (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin r)))
          (f := a) (Finset.mem_univ i)).symm
    rw [hsum, Nat.mul_add]
  calc
    (∑ i, a i) * (∑ j, a j) = ∑ i, a i * S := by
      simp [S, Finset.sum_mul]
    _ = ∑ i, (a i * a i +
        a i * ∑ j ∈ Finset.univ.filter (· ≠ i), a j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hrow i
    _ = (∑ i, a i * a i) +
        ∑ i, a i * ∑ j ∈ Finset.univ.filter (· ≠ i), a j := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, a i * a i) + 2 * multipartiteCrossPairSum a := by
      rw [sum_offDiag_sizeVector_eq_two_mul_crossPairSum]

private theorem two_mul_choose_two (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.mul_comm 2, Nat.choose_two_right,
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]

/-- Every unordered pair drawn from a disjoint union is either internal to
one block or crosses one unordered pair of block indices. -/
theorem multipartiteCrossPairSum_add_sum_choose {r : ℕ} (a : Fin r → ℕ) :
    multipartiteCrossPairSum a + (∑ i, (a i).choose 2) =
      (∑ i, a i).choose 2 := by
  let S := ∑ i, a i
  have hsquare := sum_sizeVector_mul_self a
  have hinternal :
      2 * (∑ i, (a i).choose 2) =
        ∑ i, a i * (a i - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    exact two_mul_choose_two _
  have hdiag :
      (∑ i, a i * a i) =
        (∑ i, a i * (a i - 1)) + ∑ i, a i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rcases Nat.eq_zero_or_pos (a i) with hi | hi
    · simp [hi]
    · have hsub : a i - 1 + 1 = a i := by omega
      calc
        a i * a i = a i * (a i - 1 + 1) := by rw [hsub]
        _ = a i * (a i - 1) + a i := by
          rw [Nat.mul_add, Nat.mul_one]
  have hchoose := two_mul_choose_two S
  have hsquareSplit : S * S = S * (S - 1) + S := by
    rcases Nat.eq_zero_or_pos S with hS | hS
    · simp [hS]
    · have hsub : S - 1 + 1 = S := by omega
      calc
        S * S = S * (S - 1 + 1) := by rw [hsub]
        _ = S * (S - 1) + S := by rw [Nat.mul_add, Nat.mul_one]
  change S * S = _ at hsquare
  change multipartiteCrossPairSum a + (∑ i, (a i).choose 2) =
    S.choose 2
  have htwiceAdd :
      2 * (multipartiteCrossPairSum a + (∑ i, (a i).choose 2)) + S =
        2 * S.choose 2 + S := by
    calc
      2 * (multipartiteCrossPairSum a + (∑ i, (a i).choose 2)) + S =
          S * S := by rw [hsquare, hdiag, ← hinternal]; omega
      _ = S * (S - 1) + S := hsquareSplit
      _ = 2 * S.choose 2 + S := by rw [hchoose]
  omega

/-! ## The canonical balanced size vector -/

/-- The first `q % r` entries are large and all later entries are small. -/
def balancedPartSize (r q : ℕ) (i : Fin r) : ℕ :=
  q / r + if i.1 < q % r then 1 else 0

@[simp] theorem balancedPartSize_eq_card_balancedFinPartition
    {r q : ℕ} (hr : 0 < r) (i : Fin r) :
    balancedPartSize r q i = (balancedFinPartition r q i).card := by
  simp [balancedPartSize, card_balancedFinPartition hr]

theorem sum_balancedPartSize {r q : ℕ} (hr : 0 < r) :
    ∑ i, balancedPartSize r q i = q := by
  simp_rw [balancedPartSize_eq_card_balancedFinPartition hr]
  rw [← Finset.card_biUnion (by
    simpa using balancedFinPartition_pairwiseDisjoint r q),
    biUnion_balancedFinPartition hr, Finset.card_univ, Fintype.card_fin]

/-- Any statistic of the canonical balanced sizes splits into its large and
small values with the expected multiplicities. -/
theorem sum_comp_balancedPartSize {r q : ℕ} (hr : 0 < r) (F : ℕ → ℕ) :
    ∑ i : Fin r, F (balancedPartSize r q i) =
      (q % r) * F (q / r + 1) +
        (r - q % r) * F (q / r) := by
  classical
  let large : Fin r → Prop := fun i ↦ i.1 < q % r
  have hlarge : ((Finset.univ : Finset (Fin r)).filter large).card = q % r := by
    simp [large, Fin.card_filter_val_lt,
      Nat.min_eq_right (Nat.mod_lt q hr).le]
  have hsmall : ((Finset.univ : Finset (Fin r)).filter fun i ↦ ¬large i).card =
      r - q % r := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r))) (p := large)
    rw [hlarge, Finset.card_univ, Fintype.card_fin] at hsplit
    omega
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Fin r))) (p := large)]
  have hlargeSum :
      ∑ i ∈ (Finset.univ : Finset (Fin r)).filter large,
          F (balancedPartSize r q i) =
        (q % r) * F (q / r + 1) := by
    rw [Finset.sum_const_nat (m := F (q / r + 1))]
    · rw [hlarge]
    · intro i hi
      have hilarge := (Finset.mem_filter.mp hi).2
      unfold balancedPartSize
      rw [if_pos hilarge]
  have hsmallSum :
      ∑ i ∈ (Finset.univ : Finset (Fin r)).filter (fun i ↦ ¬large i),
          F (balancedPartSize r q i) =
        (r - q % r) * F (q / r) := by
    rw [Finset.sum_const_nat (m := F (q / r))]
    · rw [hsmall]
    · intro i hi
      have hismall := (Finset.mem_filter.mp hi).2
      unfold balancedPartSize
      rw [if_neg hismall]
      simp
  rw [hlargeSum, hsmallSum]

/-- On adding one point, the canonical balanced size vector increments the
coordinate indexed by the old remainder. -/
theorem balancedPartSize_succ {r q : ℕ} (hr : 0 < r) (i : Fin r) :
    balancedPartSize r (q + 1) i =
      balancedPartSize r q i + if i.1 = q % r then 1 else 0 := by
  have hslt : q % r < r := Nat.mod_lt q hr
  have hdecomp := Nat.mod_add_div q r
  have hdecomp' := Nat.mod_add_div (q + 1) r
  by_cases hd : r ∣ q + 1
  · have hmod' : (q + 1) % r = 0 := Nat.mod_eq_zero_of_dvd hd
    have hdiv' : (q + 1) / r = q / r + 1 := by simp [Nat.succ_div, hd]
    have hs : q % r + 1 = r := by
      rw [hmod', hdiv'] at hdecomp'
      simp only [Nat.mul_add, Nat.mul_one] at hdecomp'
      omega
    unfold balancedPartSize
    rw [hmod']
    simp only [Nat.not_lt_zero, ↓reduceIte, add_zero]
    split_ifs <;> omega
  · have hdiv' : (q + 1) / r = q / r := by simp [Nat.succ_div, hd]
    have hmod' : (q + 1) % r = q % r + 1 := by
      rw [hdiv'] at hdecomp'
      omega
    unfold balancedPartSize
    rw [hmod']
    split_ifs <;> omega

/-- The factorial product of the canonical size vector has the expected
one-step recurrence. -/
theorem prod_factorial_balancedPartSize_succ {r q : ℕ} (hr : 0 < r) :
    (∏ i : Fin r, (balancedPartSize r (q + 1) i).factorial) =
      (q / r + 1) * ∏ i : Fin r, (balancedPartSize r q i).factorial := by
  let j : Fin r := ⟨q % r, Nat.mod_lt q hr⟩
  have hj : balancedPartSize r q j = q / r := by
    simp [balancedPartSize, j]
  have hfun :
      (fun i : Fin r ↦ (balancedPartSize r (q + 1) i).factorial) =
        Function.update
          (fun i : Fin r ↦ (balancedPartSize r q i).factorial) j
          ((balancedPartSize r q j + 1).factorial) := by
    funext i
    rw [balancedPartSize_succ hr]
    by_cases hij : i = j
    · subst i
      simp [j]
    · have hval : i.1 ≠ q % r := by
        intro h
        apply hij
        exact Fin.ext h
      simp [hij, hval]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j),
    Nat.factorial_succ, hj]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
    (Finset.mem_univ j)]
  simp [hj, Nat.mul_assoc]

/-- Among nonnegative `r`-vectors with a fixed sum, the canonical balanced
vector minimizes the product of factorials.  This is the elementary
``method of types'' extremality step, proved by adding one point at a time. -/
theorem prod_factorial_balancedPartSize_le {r q : ℕ} (hr : 0 < r)
    (a : Fin r → ℕ) (hsum : ∑ i, a i = q) :
    (∏ i : Fin r, (balancedPartSize r q i).factorial) ≤
      ∏ i : Fin r, (a i).factorial := by
  induction q generalizing a with
  | zero =>
      have ha : a = 0 := by
        funext i
        have hai : a i ≤ ∑ j, a j :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        rw [hsum] at hai
        simp only [Pi.zero_apply]
        omega
      subst a
      simp [balancedPartSize]
  | succ q ih =>
      have hi : ∃ i : Fin r, q / r + 1 ≤ a i := by
        by_contra h
        push Not at h
        have hle : (∑ i, a i) ≤ ∑ _i : Fin r, q / r :=
          Finset.sum_le_sum fun i _hi ↦ Nat.le_of_lt_succ (h i)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul] at hle
        rw [hsum] at hle
        have hfloor : r * (q / r) ≤ q := Nat.mul_div_le q r
        exact (Nat.not_succ_le_self q) (hle.trans hfloor)
      obtain ⟨i, hi⟩ := hi
      have hai : 0 < a i := (Nat.zero_lt_succ _).trans_le hi
      let a' : Fin r → ℕ := Function.update a i (a i - 1)
      have hsum' : ∑ j, a' j = q := by
        rw [show (∑ j, a' j) =
            (a i - 1) + ∑ j ∈ ({i}ᶜ : Finset (Fin r)), a j by
          simp only [a', Finset.sum_update_of_mem (Finset.mem_univ i)]
          rfl]
        rw [Fintype.sum_eq_add_sum_compl i] at hsum
        omega
      have hih := ih a' hsum'
      rw [prod_factorial_balancedPartSize_succ hr]
      calc
        (q / r + 1) *
              ∏ j : Fin r, (balancedPartSize r q j).factorial ≤
            (q / r + 1) * ∏ j : Fin r, (a' j).factorial :=
          Nat.mul_le_mul_left _ hih
        _ ≤ ∏ j : Fin r, (a j).factorial := by
          have hfun :
              (fun j : Fin r ↦ (a' j).factorial) =
                Function.update (fun j : Fin r ↦ (a j).factorial) i
                  ((a i - 1).factorial) := by
            funext j
            by_cases hji : j = i
            · subst j
              simp [a']
            · simp [a', hji]
          rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i),
            Fintype.prod_eq_mul_prod_compl]
          have hfac : (a i).factorial =
              a i * (a i - 1).factorial := by
            conv_lhs => rw [show a i = (a i - 1) + 1 by omega]
            rw [Nat.factorial_succ]
            congr
            omega
          rw [hfac]
          have hcompl : ({i}ᶜ : Finset (Fin r)) =
              Finset.univ \ {i} := by
            ext j
            simp
          rw [hcompl]
          simpa [Nat.mul_assoc] using
            (Nat.mul_le_mul_right
              ((a i - 1).factorial *
                ∏ j ∈ Finset.univ \ {i}, (a j).factorial) hi)

/-- The multinomial coefficient is maximized by the canonical balanced size
vector. -/
theorem multinomial_le_balancedPartSize {r q : ℕ} (hr : 0 < r)
    (a : Fin r → ℕ) (hsum : ∑ i, a i = q) :
    Nat.multinomial Finset.univ a ≤
      Nat.multinomial Finset.univ (balancedPartSize r q) := by
  have hp := prod_factorial_balancedPartSize_le hr a hsum
  have haSpec :
      (∏ i : Fin r, (a i).factorial) *
          Nat.multinomial Finset.univ a = q.factorial := by
    simpa [hsum] using
      (Nat.multinomial_spec (Finset.univ : Finset (Fin r)) a)
  have hbSpec :
      (∏ i : Fin r, (balancedPartSize r q i).factorial) *
          Nat.multinomial Finset.univ (balancedPartSize r q) = q.factorial := by
    simpa [sum_balancedPartSize hr] using
      (Nat.multinomial_spec (Finset.univ : Finset (Fin r))
        (balancedPartSize r q))
  apply Nat.le_of_mul_le_mul_left (c :=
    ∏ i : Fin r, (balancedPartSize r q i).factorial)
  · calc
      (∏ i : Fin r, (balancedPartSize r q i).factorial) *
            Nat.multinomial Finset.univ a ≤
          (∏ i : Fin r, (a i).factorial) *
            Nat.multinomial Finset.univ a :=
        Nat.mul_le_mul_right _ hp
      _ = q.factorial := haSpec
      _ = (∏ i : Fin r, (balancedPartSize r q i).factorial) *
            Nat.multinomial Finset.univ (balancedPartSize r q) := hbSpec.symm
  · exact Nat.prod_factorial_pos Finset.univ (balancedPartSize r q)

/-- There are at most `(q+1)^r` weak `r`-part compositions of `q`.  We use
the intentionally crude box bound because it is exactly what the method of
types needs and avoids any asymptotic estimate. -/
theorem card_piAntidiag_le_succ_pow (r q : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin r)) q).card ≤
      (q + 1) ^ r := by
  let compositions :=
    Finset.piAntidiag (Finset.univ : Finset (Fin r)) q
  let toBounded : (↥compositions) → (Fin r → Fin (q + 1)) :=
    fun a i ↦ ⟨a.1 i, by
      have hsum := (Finset.mem_piAntidiag.mp a.2).1
      have hi : a.1 i ≤ ∑ j ∈ (Finset.univ : Finset (Fin r)), a.1 j :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      rw [hsum] at hi
      omega⟩
  have hinj : Function.Injective toBounded := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact Fin.mk.inj (congrFun hab i)
  have hcard := Fintype.card_le_of_injective toBounded hinj
  simpa [compositions] using hcard

/-- No-Stirling lower bound for the largest (hence balanced) multinomial
coefficient. -/
theorem pow_le_succ_pow_mul_multinomial_balancedPartSize
    {r q : ℕ} (hr : 0 < r) :
    r ^ q ≤ (q + 1) ^ r *
      Nat.multinomial Finset.univ (balancedPartSize r q) := by
  let compositions :=
    Finset.piAntidiag (Finset.univ : Finset (Fin r)) q
  have hexpand :
      r ^ q = ∑ a ∈ compositions, Nat.multinomial Finset.univ a := by
    have h := Finset.sum_pow_eq_sum_piAntidiag
      (Finset.univ : Finset (Fin r)) (fun _ ↦ (1 : ℕ)) q
    simpa [compositions] using h
  rw [hexpand]
  calc
    (∑ a ∈ compositions, Nat.multinomial Finset.univ a) ≤
        compositions.card •
          Nat.multinomial Finset.univ (balancedPartSize r q) := by
      apply Finset.sum_le_card_nsmul
      intro a ha
      apply multinomial_le_balancedPartSize hr
      have hsum := (Finset.mem_piAntidiag.mp ha).1
      simpa using hsum
    _ = compositions.card *
          Nat.multinomial Finset.univ (balancedPartSize r q) := by
      simp [nsmul_eq_mul]
    _ ≤ (q + 1) ^ r *
          Nat.multinomial Finset.univ (balancedPartSize r q) := by
      apply Nat.mul_le_mul_right
      simpa [compositions] using card_piAntidiag_le_succ_pow r q

/-! ## Assignments with prescribed fiber sizes -/

/-- Size of one fiber of a finite assignment. -/
def assignmentFiberSize {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (f : V → C) (c : C) : ℕ :=
  (Finset.univ.filter fun v ↦ f v = c).card

/-- A finite assignment has the prescribed labeled fiber sizes. -/
def HasAssignmentFiberSizes {V C : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq C] (a : C → ℕ) (f : V → C) : Prop :=
  ∀ c, assignmentFiberSize f c = a c

/-- The finite family of assignments with a fixed labeled size vector. -/
def assignmentsOfFiberSizes {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (a : C → ℕ) : Finset (V → C) :=
  by
    classical
    exact Finset.univ.filter (HasAssignmentFiberSizes a)

@[simp] theorem mem_assignmentsOfFiberSizes
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] {a : C → ℕ} {f : V → C} :
    f ∈ assignmentsOfFiberSizes a ↔ HasAssignmentFiberSizes a f := by
  simp [assignmentsOfFiberSizes]

private def zeroFiber {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (f : V → Fin (r + 1)) : Finset V :=
  Finset.univ.filter fun v ↦ f v = 0

private def combineZeroAssignment {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (a : Fin (r + 1) → ℕ) :
    (Σ S : {S : Finset V // S.card = a 0},
      {g : {v : V // v ∉ S.1} → Fin r //
        HasAssignmentFiberSizes (fun i ↦ a i.succ) g}) →
      {f : V → Fin (r + 1) // HasAssignmentFiberSizes a f} := by
  intro x
  rcases x with ⟨S, g⟩
  let f : V → Fin (r + 1) := fun v ↦
    if hv : v ∈ S.1 then 0 else (g.1 ⟨v, hv⟩).succ
  refine ⟨f, ?_⟩
  intro c
  induction c using Fin.cases with
  | zero =>
      change (Finset.univ.filter fun v ↦ f v = 0).card = a 0
      rw [show (Finset.univ.filter fun v ↦ f v = 0) = S.1 by
        ext v
        simp [f]]
      exact S.2
  | succ i =>
      change (Finset.univ.filter fun v ↦ f v = i.succ).card = a i.succ
      calc
        (Finset.univ.filter fun v ↦ f v = i.succ).card =
            ((Finset.univ : Finset {v : V // v ∉ S.1}).filter
              fun v ↦ g.1 v = i).card := by
          apply Finset.card_bij (fun v _hv ↦ (⟨v, by
            have hv := (Finset.mem_filter.mp _hv).2
            intro hvS
            have hz : f v = 0 := by simp [f, hvS]
            exact Fin.succ_ne_zero i (hz.symm.trans hv).symm⟩ :
              {v : V // v ∉ S.1}))
          · intro v hv
            have hvEq := (Finset.mem_filter.mp hv).2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hvNot : v ∉ S.1 := by
              intro hvS
              have hz : f v = 0 := by simp [f, hvS]
              exact Fin.succ_ne_zero i (hz.symm.trans hvEq).symm
            apply Fin.succ_inj.mp
            simpa [f, hvNot] using hvEq
          · intro v₁ hv₁ v₂ hv₂ heq
            exact congrArg Subtype.val heq
          · intro v hv
            have hvEq := (Finset.mem_filter.mp hv).2
            refine ⟨v.1, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            simp [f, v.2, hvEq]
        _ = a i.succ := g.2 i

private theorem combineZeroAssignment_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (a : Fin (r + 1) → ℕ) :
    Function.Injective (combineZeroAssignment (V := V) a) := by
  rintro ⟨S, g⟩ ⟨T, h⟩ heq
  have hfun :
      (combineZeroAssignment (V := V) a ⟨S, g⟩).1 =
        (combineZeroAssignment (V := V) a ⟨T, h⟩).1 :=
    congrArg Subtype.val heq
  have hST : S = T := by
    apply Subtype.ext
    ext v
    have hv := congrFun hfun v
    by_cases hvS : v ∈ S.1 <;> by_cases hvT : v ∈ T.1
    · simp [hvS, hvT]
    · exfalso
      have hz : (0 : Fin (r + 1)) = (h.1 ⟨v, hvT⟩).succ := by
        simpa [combineZeroAssignment, hvS, hvT] using hv
      exact Fin.succ_ne_zero _ hz.symm
    · exfalso
      have hz : (g.1 ⟨v, hvS⟩).succ = (0 : Fin (r + 1)) := by
        simpa [combineZeroAssignment, hvS, hvT] using hv
      exact Fin.succ_ne_zero _ hz
    · simp [hvS, hvT]
  subst T
  have hgh : g = h := by
    apply Subtype.ext
    funext v
    have hv := congrFun hfun v.1
    simp [combineZeroAssignment, v.2] at hv
    exact hv
  subst h
  rfl

/-- Recover the zero fiber and the residual assignment from an assignment
with prescribed fibers.  This is the inverse construction to
`combineZeroAssignment`. -/
private def splitZeroAssignment {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (a : Fin (r + 1) → ℕ) :
    {f : V → Fin (r + 1) // HasAssignmentFiberSizes a f} →
      (Σ S : {S : Finset V // S.card = a 0},
        {g : {v : V // v ∉ S.1} → Fin r //
          HasAssignmentFiberSizes (fun i ↦ a i.succ) g}) := by
  intro f
  let S : Finset V := zeroFiber f.1
  have hScard : S.card = a 0 := f.2 0
  let g : {v : V // v ∉ S} → Fin r := fun v ↦
    (f.1 v.1).pred (by
      intro hz
      apply v.2
      simp only [S, zeroFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz)
  refine ⟨⟨S, hScard⟩, ⟨g, ?_⟩⟩
  intro i
  change ((Finset.univ : Finset {v : V // v ∉ S}).filter
      fun v ↦ g v = i).card = a i.succ
  calc
    ((Finset.univ : Finset {v : V // v ∉ S}).filter
        fun v ↦ g v = i).card =
        ((Finset.univ : Finset V).filter fun v ↦ f.1 v = i.succ).card := by
      apply Finset.card_bij (fun v _hv ↦ v.1)
      · intro v hv
        have hvEq := (Finset.mem_filter.mp hv).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hvNonzero : f.1 v.1 ≠ 0 := by
          intro hz
          exact v.2 (by simp [S, zeroFiber, hz])
        exact (Fin.succ_pred (f.1 v.1) hvNonzero).symm.trans
          (congrArg Fin.succ hvEq)
      · intro v₁ _hv₁ v₂ _hv₂ hval
        exact Subtype.ext hval
      · intro v hv
        have hvEq := (Finset.mem_filter.mp hv).2
        have hvNot : v ∉ S := by
          intro hvS
          have hz : f.1 v = 0 := by simpa [S, zeroFiber] using hvS
          exact Fin.succ_ne_zero i (hvEq.symm.trans hz)
        refine ⟨⟨v, hvNot⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply Fin.succ_injective
        simpa [g, hvEq]
    _ = a i.succ := f.2 i.succ

private theorem combineZeroAssignment_splitZeroAssignment
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (a : Fin (r + 1) → ℕ)
    (f : {f : V → Fin (r + 1) // HasAssignmentFiberSizes a f}) :
    combineZeroAssignment a (splitZeroAssignment a f) = f := by
  apply Subtype.ext
  funext v
  by_cases hv : v ∈ zeroFiber f.1
  · have hz : f.1 v = 0 := (Finset.mem_filter.mp hv).2
    simpa [combineZeroAssignment, splitZeroAssignment, zeroFiber, hz]
  · have hnz : f.1 v ≠ 0 := by
      intro hz
      exact hv (by simp [zeroFiber, hz])
    simpa [combineZeroAssignment, splitZeroAssignment, zeroFiber, hnz] using
      Fin.succ_pred (f.1 v) hnz

private theorem combineZeroAssignment_surjective
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (a : Fin (r + 1) → ℕ) :
    Function.Surjective (combineZeroAssignment (V := V) a) := by
  intro f
  exact ⟨splitZeroAssignment a f,
    combineZeroAssignment_splitZeroAssignment a f⟩

private theorem multinomial_univ_fin_succ {r : ℕ}
    (a : Fin (r + 1) → ℕ) :
    Nat.multinomial Finset.univ a =
      (∑ i, a i).choose (a 0) *
        Nat.multinomial Finset.univ (fun i : Fin r ↦ a i.succ) := by
  let s : Finset (Fin (r + 1)) :=
    (Finset.univ : Finset (Fin r)).map (Fin.succEmb r)
  have hzero : (0 : Fin (r + 1)) ∉ s := by
    simp [s]
  have huniv : (Finset.univ : Finset (Fin (r + 1))) =
      Finset.cons 0 s hzero := by
    ext i
    induction i using Fin.cases <;> simp [s]
  rw [huniv, Nat.multinomial_cons]
  have hsum : a 0 + ∑ i ∈ s, a i = ∑ i, a i := by
    rw [Fin.sum_univ_succ]
    simp [s]
  rw [Finset.sum_cons]
  congr 1
  unfold Nat.multinomial
  simp [s]

/-- The multinomial coefficient injects into the family of assignments with
the corresponding labeled fiber sizes.  The proof recursively chooses the
zero fiber; only the lower bound is needed downstream, so no quotient by
within-fiber permutations is introduced. -/
theorem multinomial_le_card_assignmentsOfFiberSizes
    {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (a : Fin r → ℕ) (hsum : ∑ i, a i = Fintype.card V) :
    Nat.multinomial Finset.univ a ≤
      (assignmentsOfFiberSizes (V := V) a).card := by
  classical
  induction r generalizing V with
  | zero =>
      have hV : Fintype.card V = 0 := by
        simpa using hsum.symm
      letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      let f : V → Fin 0 := fun v ↦ isEmptyElim v
      have hf : HasAssignmentFiberSizes a f := by
        intro i
        exact Fin.elim0 i
      have hmem : f ∈ assignmentsOfFiberSizes a :=
        mem_assignmentsOfFiberSizes.mpr hf
      simpa using (Finset.card_pos.mpr ⟨f, hmem⟩)
  | succ r ih =>
      let choices :=
        Σ S : {S : Finset V // S.card = a 0},
          {g : {v : V // v ∉ S.1} → Fin r //
            HasAssignmentFiberSizes (fun i ↦ a i.succ) g}
      have hcardInj : Fintype.card choices ≤
          Fintype.card {f : V → Fin (r + 1) //
            HasAssignmentFiberSizes a f} :=
        Fintype.card_le_of_injective (combineZeroAssignment a)
          (combineZeroAssignment_injective a)
      have htailSum : ∑ i : Fin r, a i.succ =
          Fintype.card V - a 0 := by
        rw [Fin.sum_univ_succ] at hsum
        omega
      have hsource :
          (Fintype.card V).choose (a 0) *
              Nat.multinomial Finset.univ (fun i : Fin r ↦ a i.succ) ≤
            Fintype.card choices := by
        rw [Fintype.card_sigma]
        calc
          (Fintype.card V).choose (a 0) *
                Nat.multinomial Finset.univ (fun i : Fin r ↦ a i.succ) =
              Fintype.card {S : Finset V // S.card = a 0} *
                Nat.multinomial Finset.univ (fun i : Fin r ↦ a i.succ) := by
            rw [Fintype.card_finset_len]
          _ = ∑ S : {S : Finset V // S.card = a 0},
                Nat.multinomial Finset.univ (fun i : Fin r ↦ a i.succ) := by
            simp
          _ ≤ ∑ S : {S : Finset V // S.card = a 0},
                Fintype.card {g : {v : V // v ∉ S.1} → Fin r //
                  HasAssignmentFiberSizes (fun i ↦ a i.succ) g} := by
            apply Finset.sum_le_sum
            intro S _hS
            have hcompCard : Fintype.card {v : V // v ∉ S.1} =
                Fintype.card V - a 0 := by
              rw [Fintype.card_subtype_compl (fun v : V ↦ v ∈ S.1)]
              simp [S.2]
            have hih := ih (V := {v : V // v ∉ S.1})
              (fun i : Fin r ↦ a i.succ) (htailSum.trans hcompCard.symm)
            simpa [assignmentsOfFiberSizes, Fintype.card_subtype] using hih
      rw [multinomial_univ_fin_succ, hsum]
      calc
        (Fintype.card V).choose (a 0) *
              Nat.multinomial Finset.univ (fun i : Fin r ↦ a i.succ) ≤
            Fintype.card choices := hsource
        _ ≤ Fintype.card {f : V → Fin (r + 1) //
              HasAssignmentFiberSizes a f} := hcardInj
        _ = (assignmentsOfFiberSizes (V := V) a).card := by
          simp [assignmentsOfFiberSizes, Fintype.card_subtype]

/-- Exact cardinality of the family of labeled assignments with prescribed
fiber sizes.  This is the finite multinomial interpretation, stated for an
arbitrary finite domain. -/
theorem card_assignmentsOfFiberSizes_eq_multinomial
    {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (a : Fin r → ℕ) (hsum : ∑ i, a i = Fintype.card V) :
    (assignmentsOfFiberSizes (V := V) a).card =
      Nat.multinomial Finset.univ a := by
  classical
  induction r generalizing V with
  | zero =>
      have hV : Fintype.card V = 0 := by
        simpa using hsum.symm
      letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
      have hcard : (assignmentsOfFiberSizes (V := V) a).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨(fun v ↦ isEmptyElim v), ?_⟩
        ext f
        constructor
        · intro _hf
          simp only [Finset.mem_singleton]
          funext v
          exact isEmptyElim v
        · intro h
          simp only [Finset.mem_singleton] at h
          rw [h]
          simp only [mem_assignmentsOfFiberSizes]
          intro i
          exact Fin.elim0 i
      simpa [hcard]
  | succ r ih =>
      let choices :=
        Σ S : {S : Finset V // S.card = a 0},
          {g : {v : V // v ∉ S.1} → Fin r //
            HasAssignmentFiberSizes (fun i ↦ a i.succ) g}
      have hcardChoices : Fintype.card choices =
          Fintype.card {f : V → Fin (r + 1) //
            HasAssignmentFiberSizes a f} :=
        Fintype.card_of_bijective
          ⟨combineZeroAssignment_injective a,
            combineZeroAssignment_surjective a⟩
      have htailSum : ∑ i : Fin r, a i.succ =
          Fintype.card V - a 0 := by
        rw [Fin.sum_univ_succ] at hsum
        omega
      have hresidual (S : {S : Finset V // S.card = a 0}) :
          Fintype.card {g : {v : V // v ∉ S.1} → Fin r //
              HasAssignmentFiberSizes (fun i ↦ a i.succ) g} =
            Nat.multinomial Finset.univ (fun i : Fin r ↦ a i.succ) := by
        have hcompCard : Fintype.card {v : V // v ∉ S.1} =
            Fintype.card V - a 0 := by
          rw [Fintype.card_subtype_compl (fun v : V ↦ v ∈ S.1)]
          simp [S.2]
        have hih := ih (V := {v : V // v ∉ S.1})
          (fun i : Fin r ↦ a i.succ) (htailSum.trans hcompCard.symm)
        simpa [assignmentsOfFiberSizes, Fintype.card_subtype] using hih
      calc
        (assignmentsOfFiberSizes (V := V) a).card =
            Fintype.card {f : V → Fin (r + 1) //
              HasAssignmentFiberSizes a f} := by
          simp [assignmentsOfFiberSizes, Fintype.card_subtype]
        _ = Fintype.card choices := hcardChoices.symm
        _ = ∑ S : {S : Finset V // S.card = a 0},
              Fintype.card {g : {v : V // v ∉ S.1} → Fin r //
                HasAssignmentFiberSizes (fun i ↦ a i.succ) g} := by
          rw [Fintype.card_sigma]
        _ = Fintype.card {S : Finset V // S.card = a 0} *
              Nat.multinomial Finset.univ (fun i : Fin r ↦ a i.succ) := by
          simp_rw [hresidual]
          simp
        _ = (Fintype.card V).choose (a 0) *
              Nat.multinomial Finset.univ (fun i : Fin r ↦ a i.succ) := by
          rw [Fintype.card_finset_len]
        _ = Nat.multinomial Finset.univ a := by
          rw [multinomial_univ_fin_succ, hsum]

/-- A labeled assignment of `q` points to `r` parts is balanced when its
fiber sizes are the canonical quotient/remainder vector. -/
def IsBalancedAssignment (r q : ℕ) (f : Fin q → Fin r) : Prop :=
  HasAssignmentFiberSizes (balancedPartSize r q) f

/-- All assignments realizing the canonical balanced labeled part sizes. -/
def balancedAssignments (r q : ℕ) : Finset (Fin q → Fin r) :=
  assignmentsOfFiberSizes (balancedPartSize r q)

@[simp] theorem mem_balancedAssignments {r q : ℕ} {f : Fin q → Fin r} :
    f ∈ balancedAssignments r q ↔ IsBalancedAssignment r q f := by
  simp [balancedAssignments, IsBalancedAssignment]

theorem isBalancedAssignment_fiberSize {r q : ℕ} {f : Fin q → Fin r}
    (hf : IsBalancedAssignment r q f) (i : Fin r) :
    assignmentFiberSize f i = balancedPartSize r q i :=
  hf i

/-- The balanced assignment family contains at least the balanced
multinomial coefficient. -/
theorem multinomial_le_card_balancedAssignments
    {r q : ℕ} (hr : 0 < r) :
    Nat.multinomial Finset.univ (balancedPartSize r q) ≤
      (balancedAssignments r q).card := by
  simpa [balancedAssignments] using
    (multinomial_le_card_assignmentsOfFiberSizes
      (V := Fin q) (balancedPartSize r q) (by
        simpa using sum_balancedPartSize (r := r) (q := q) hr))

/-- Uniform no-Stirling lower bound for the number of canonical balanced
labeled assignments. -/
theorem pow_le_succ_pow_mul_card_balancedAssignments
    {r q : ℕ} (hr : 0 < r) :
    r ^ q ≤ (q + 1) ^ r * (balancedAssignments r q).card := by
  calc
    r ^ q ≤ (q + 1) ^ r *
        Nat.multinomial Finset.univ (balancedPartSize r q) :=
      pow_le_succ_pow_mul_multinomial_balancedPartSize hr
    _ ≤ (q + 1) ^ r * (balancedAssignments r q).card :=
      Nat.mul_le_mul_left _ (multinomial_le_card_balancedAssignments hr)

/-- The residue-class enumeration of a balanced size vector. -/
def balancedSizeVectorToFin {r q : ℕ} (hr : 0 < r) :
    (Sigma fun i : Fin r ↦ Fin (balancedPartSize r q i)) → Fin q :=
  fun x ↦ ⟨x.1.1 + r * x.2.1, by
    have hmod : q % r < r := Nat.mod_lt q hr
    have hdecomp := Nat.mod_add_div q r
    change x.1.1 + r * x.2.1 < q
    have hx := x.2.2
    change x.2.1 < q / r +
      (if x.1.1 < q % r then 1 else 0) at hx
    split_ifs at hx with hi
    · have hxle : x.2.1 ≤ q / r := by omega
      have hmul := Nat.mul_le_mul_left r hxle
      omega
    · have hxsucc : x.2.1 + 1 ≤ q / r := by omega
      have hmul := Nat.mul_le_mul_left r hxsucc
      rw [Nat.mul_add] at hmul
      omega⟩

theorem balancedSizeVectorToFin_injective {r q : ℕ} (hr : 0 < r) :
    Function.Injective (balancedSizeVectorToFin (r := r) (q := q) hr) := by
  intro x y hxy
  have hval : x.1.1 + r * x.2.1 = y.1.1 + r * y.2.1 :=
    Fin.mk.inj hxy
  have hindex : x.1 = y.1 := by
    apply Fin.ext
    have hmod := congrArg (fun z : ℕ ↦ z % r) hval
    simpa [Nat.add_mod, Nat.mod_eq_of_lt x.1.2,
      Nat.mod_eq_of_lt y.1.2] using hmod
  have hindexVal : x.1.1 = y.1.1 := congrArg Fin.val hindex
  have hmul : r * x.2.1 = r * y.2.1 := by omega
  have hsecond : x.2.1 = y.2.1 := Nat.eq_of_mul_eq_mul_left hr hmul
  exact Sigma.ext hindex
    ((Fin.heq_ext_iff (by rw [hindex])).mpr hsecond)

/-- Canonical equivalence between a balanced size-vector realization and
`Fin q`, preserving the part index modulo `r`. -/
def balancedSizeVectorEquiv {r q : ℕ} (hr : 0 < r) :
    (Sigma fun i : Fin r ↦ Fin (balancedPartSize r q i)) ≃ Fin q := by
  apply Equiv.ofBijective (balancedSizeVectorToFin hr)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨balancedSizeVectorToFin_injective hr, ?_⟩
  simp [sum_balancedPartSize hr]

@[simp] theorem balancedSizeVectorEquiv_apply {r q : ℕ} (hr : 0 < r)
    (x : Sigma fun i : Fin r ↦ Fin (balancedPartSize r q i)) :
    balancedSizeVectorEquiv hr x = balancedSizeVectorToFin hr x :=
  rfl

@[simp] theorem balancedSizeVectorToFin_mod {r q : ℕ} (hr : 0 < r)
    (x : Sigma fun i : Fin r ↦ Fin (balancedPartSize r q i)) :
    (balancedSizeVectorToFin hr x).1 % r = x.1.1 := by
  simp [balancedSizeVectorToFin, Nat.add_mod,
    Nat.mod_eq_of_lt x.1.2]

/-- A complete multipartite graph with the canonical balanced size vector
is the canonical Turán graph, up to the residue-class enumeration. -/
def balancedMultipartiteGraphIsoTuran {r q : ℕ} (hr : 0 < r) :
    SimpleGraph.completeMultipartiteGraph
        (fun i : Fin r ↦ Fin (balancedPartSize r q i)) ≃g
      SimpleGraph.turanGraph q r where
  toEquiv := balancedSizeVectorEquiv hr
  map_rel_iff' {v w} := by
    rw [SimpleGraph.turanGraph_adj]
    simp only [balancedSizeVectorEquiv_apply,
      balancedSizeVectorToFin_mod]
    change (v.1.1 ≠ w.1.1) ↔ (v.1 ≠ w.1)
    exact Fin.ext_iff.not.symm

theorem multipartiteCrossCapacity_balancedPartSize {r q : ℕ} (hr : 0 < r) :
    multipartiteCrossCapacity (balancedPartSize r q) =
      balancedMultipartiteCrossCapacity r q := by
  simpa [multipartiteCrossCapacity,
    balancedMultipartiteCrossCapacity] using
      (balancedMultipartiteGraphIsoTuran
        (r := r) (q := q) hr).card_edgeFinset_eq

/-- The graph encoding of a size vector has exactly the expected sum of
products over unordered pairs of parts. -/
theorem multipartiteCrossCapacity_eq_pairSum {r : ℕ} (a : Fin r → ℕ) :
    multipartiteCrossCapacity a = multipartiteCrossPairSum a := by
  rw [← Nat.mul_left_cancel_iff zero_lt_two]
  calc
    2 * multipartiteCrossCapacity a =
        ∑ v : Sigma fun i : Fin r ↦ Fin (a i),
          (SimpleGraph.completeMultipartiteGraph
            (fun i : Fin r ↦ Fin (a i))).degree v := by
      simpa [multipartiteCrossCapacity] using
        (SimpleGraph.sum_degrees_eq_twice_card_edges
          (G := SimpleGraph.completeMultipartiteGraph
            (fun i : Fin r ↦ Fin (a i)))).symm
    _ = ∑ i : Fin r,
          a i * ∑ j ∈ Finset.univ.filter (· ≠ i), a j :=
      sum_degree_completeMultipartite_sizeVector a
    _ = 2 * multipartiteCrossPairSum a :=
      sum_offDiag_sizeVector_eq_two_mul_crossPairSum a

theorem multipartiteCrossPairSum_balancedPartSize {r q : ℕ} (hr : 0 < r) :
    multipartiteCrossPairSum (balancedPartSize r q) =
      balancedMultipartiteCrossCapacity r q := by
  rw [← multipartiteCrossCapacity_eq_pairSum,
    multipartiteCrossCapacity_balancedPartSize hr]

/-- The balanced internal capacity is the sum of the clique capacities of
the canonical balanced parts. -/
theorem balancedMultipartiteInternalCapacity_eq_sum_choose
    {r q : ℕ} (hr : 0 < r) :
    balancedMultipartiteInternalCapacity r q =
      ∑ i : Fin r, (balancedFinPartition r q i).card.choose 2 := by
  have hpairs :=
    multipartiteCrossPairSum_add_sum_choose (balancedPartSize r q)
  rw [multipartiteCrossPairSum_balancedPartSize hr,
    sum_balancedPartSize hr] at hpairs
  have htotal := balancedCross_add_internal r q
  simp_rw [balancedPartSize_eq_card_balancedFinPartition hr] at hpairs
  omega

/-- Closed floor/ceiling formula for balanced internal capacity. -/
theorem balancedMultipartiteInternalCapacity_eq_floor_ceil
    {r q : ℕ} (hr : 0 < r) :
    balancedMultipartiteInternalCapacity r q =
      (q % r) * (q / r + 1).choose 2 +
        (r - q % r) * (q / r).choose 2 := by
  calc
    balancedMultipartiteInternalCapacity r q =
        ∑ i : Fin r, (balancedPartSize r q i).choose 2 := by
      rw [balancedMultipartiteInternalCapacity_eq_sum_choose hr]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [balancedPartSize_eq_card_balancedFinPartition hr]
    _ = _ := sum_comp_balancedPartSize hr (fun n ↦ n.choose 2)

theorem balancedMultipartiteInternalCapacity_cast_eq
    {r q : ℕ} (hr : 0 < r) :
    (balancedMultipartiteInternalCapacity r q : ℝ) =
      (q : ℝ) ^ 2 / (2 * (r : ℝ)) - (q : ℝ) / 2 +
        ((q % r : ℕ) : ℝ) * ((r : ℝ) - ((q % r : ℕ) : ℝ)) /
          (2 * (r : ℝ)) := by
  rw [balancedMultipartiteInternalCapacity_eq_floor_ceil hr]
  push_cast
  rw [Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  have hmodle : q % r ≤ r := (Nat.mod_lt q hr).le
  rw [Nat.cast_sub hmodle]
  have hdecompNat := Nat.mod_add_div q r
  have hdecomp : (q : ℝ) = ((q % r : ℕ) : ℝ) +
      (r : ℝ) * ((q / r : ℕ) : ℝ) := by
    exact_mod_cast hdecompNat.symm
  have hrR : (r : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

theorem balancedMultipartiteCrossCapacity_cast_eq
    {r q : ℕ} (hr : 0 < r) :
    (balancedMultipartiteCrossCapacity r q : ℝ) =
      ((r : ℝ) - 1) * (q : ℝ) ^ 2 / (2 * (r : ℝ)) -
        ((q % r : ℕ) : ℝ) * ((r : ℝ) - ((q % r : ℕ) : ℝ)) /
          (2 * (r : ℝ)) := by
  have htotal := congrArg (fun n : ℕ ↦ (n : ℝ))
    (balancedCross_add_internal r q)
  push_cast at htotal
  rw [Nat.cast_choose_two,
    balancedMultipartiteInternalCapacity_cast_eq hr] at htotal
  have hrR : (r : ℝ) ≠ 0 := by positivity
  field_simp at htotal ⊢
  nlinarith

/-- Uniform `O(r)` error in the balanced cross-capacity quadratic. -/
theorem balancedMultipartiteCrossCapacity_approx
    {r q : ℕ} (hr : 0 < r) :
    |(balancedMultipartiteCrossCapacity r q : ℝ) -
        ((r : ℝ) - 1) * (q : ℝ) ^ 2 / (2 * (r : ℝ))| ≤ (r : ℝ) := by
  rw [balancedMultipartiteCrossCapacity_cast_eq hr]
  have hrR : (0 : ℝ) < r := by positivity
  have hb0 : (0 : ℝ) ≤ ((q % r : ℕ) : ℝ) := by positivity
  have hbr : ((q % r : ℕ) : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (Nat.mod_lt q hr).le
  rw [show
    ((r : ℝ) - 1) * (q : ℝ) ^ 2 / (2 * (r : ℝ)) -
          ((q % r : ℕ) : ℝ) * ((r : ℝ) - ((q % r : ℕ) : ℝ)) /
            (2 * (r : ℝ)) -
        ((r : ℝ) - 1) * (q : ℝ) ^ 2 / (2 * (r : ℝ)) =
      -(((q % r : ℕ) : ℝ) * ((r : ℝ) - ((q % r : ℕ) : ℝ)) /
        (2 * (r : ℝ))) by ring]
  rw [abs_neg, abs_of_nonneg (div_nonneg
    (mul_nonneg hb0 (sub_nonneg.mpr hbr)) (by positivity))]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * r)).2
  nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hbr)]

/-- Uniform `O(r)` error for the complementary internal capacity after its
linear term is retained. -/
theorem balancedMultipartiteInternalCapacity_approx
    {r q : ℕ} (hr : 0 < r) :
    |(balancedMultipartiteInternalCapacity r q : ℝ) -
        ((q : ℝ) ^ 2 / (2 * (r : ℝ)) - (q : ℝ) / 2)| ≤ (r : ℝ) := by
  rw [balancedMultipartiteInternalCapacity_cast_eq hr]
  have hrR : (0 : ℝ) < r := by positivity
  have hb0 : (0 : ℝ) ≤ ((q % r : ℕ) : ℝ) := by positivity
  have hbr : ((q % r : ℕ) : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (Nat.mod_lt q hr).le
  rw [show
    (q : ℝ) ^ 2 / (2 * (r : ℝ)) - (q : ℝ) / 2 +
          ((q % r : ℕ) : ℝ) * ((r : ℝ) - ((q % r : ℕ) : ℝ)) /
            (2 * (r : ℝ)) -
        ((q : ℝ) ^ 2 / (2 * (r : ℝ)) - (q : ℝ) / 2) =
      ((q % r : ℕ) : ℝ) * ((r : ℝ) - ((q % r : ℕ) : ℝ)) /
        (2 * (r : ℝ)) by ring]
  rw [abs_of_nonneg (div_nonneg
    (mul_nonneg hb0 (sub_nonneg.mpr hbr)) (by positivity))]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * r)).2
  nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hbr)]

/-- Explicit sum-over-parts version of balanced multipartite extremality. -/
theorem balancedMultipartiteCrossCapacity_max_parts
    {r : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (parts : Fin r → Finset V)
    (hcover : Finset.univ.biUnion parts = Finset.univ)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts) :
    multipartiteCrossPairSum (fun i ↦ (parts i).card) ≤
      balancedMultipartiteCrossCapacity r (Fintype.card V) := by
  have hsum : ∑ i, (parts i).card = Fintype.card V := by
    rw [← Finset.card_biUnion (by simpa using hdisjoint), hcover,
      Finset.card_univ]
  rw [← multipartiteCrossCapacity_eq_pairSum]
  exact balancedMultipartiteCrossCapacity_max
    (fun i ↦ (parts i).card) hsum

end DenseGraph
