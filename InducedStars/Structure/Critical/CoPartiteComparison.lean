import InducedStars.Structure.Critical.FineBalanceCanonical
import InducedStars.Structure.Critical.Reference
import InducedStars.Structure.Supercritical.CoverReindexing

/-!
# Uniform constant-factor co-partite counting

The upper comparison sums all finite imbalance shells against a summable
Gaussian. The lower comparison uses exactly balanced ordered covers and
the existing uniform near-critical cover-multiplicity estimate. Neither
comparison asserts the sharp lattice prefactor of the introductory formula.
-/

noncomputable section
open Finset Set Filter
open scoped BigOperators Topology Classical

namespace InducedStars

/-- The balanced ordered-cover reference at an arbitrary exact edge count. -/
def coPartiteBalancedReferenceMass (k n m : ℕ) : ℝ :=
  (Nat.multinomial Finset.univ
    (DenseGraph.balancedPartSize (k - 1) n) : ℝ) *
    (Nat.choose (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n)
      (m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) : ℝ)

/-- Uniform Gaussian suppression of an arbitrary multipartite size vector.
The harmless factor exp(eta/9) includes ranges zero and one. -/
theorem coPartite_choose_le_gaussian
    {r n z : ℕ} (hr : 0 < r) {eta : ℝ} (heta : 0 < eta)
    (hB : 0 < DenseGraph.balancedMultipartiteCrossCapacity r n)
    (hz : eta * (DenseGraph.balancedMultipartiteCrossCapacity r n : ℝ) ≤ z)
    (a : Fin r → ℕ) (hsum : ∑ i, a i = n) :
    (Nat.choose (DenseGraph.multipartiteCrossCapacity a) z : ℝ) ≤
      (Nat.choose (DenseGraph.balancedMultipartiteCrossCapacity r n) z : ℝ) *
        Real.exp (eta / 9 - (eta / 9) *
          (DenseGraph.sizeVectorRange hr a : ℝ) ^ 2) := by
  let A := DenseGraph.multipartiteCrossCapacity a
  let B := DenseGraph.balancedMultipartiteCrossCapacity r n
  let d := DenseGraph.sizeVectorRange hr a
  have hAB : A ≤ B := by
    simpa [A, B, hsum] using DenseGraph.multipartiteCrossCapacity_le_balanced a
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  by_cases hrange : 2 ≤ d
  · by_cases hzA : z ≤ A
    · have hbin := DenseGraph.choose_le_choose_add_mul_exp_neg
        (N := A) (Q := B - A) (m := z) hzA (by omega)
      have hsumAB : A + (B - A) = B := Nat.add_sub_of_le hAB
      rw [hsumAB] at hbin
      have hsumReal : (A : ℝ) + (B - A : ℕ) = (B : ℝ) := by
        exact_mod_cast hsumAB
      rw [hsumReal] at hbin
      have hgapNat := DenseGraph.sizeVectorRange_sq_le_nine_mul_balancedCross_gap
        hr a hsum hrange
      have hgap : (d : ℝ) ^ 2 ≤ 9 * (B - A : ℕ) := by
        exact_mod_cast hgapNat
      have hratio : eta * (B - A : ℕ) ≤
          (z : ℝ) * (B - A : ℕ) / B := by
        apply (le_div_iff₀ hBreal).2
        have hmul := mul_le_mul_of_nonneg_right hz
          (show (0 : ℝ) ≤ (B - A : ℕ) by positivity)
        dsimp [B] at hmul ⊢
        nlinarith
      have hscaled := mul_le_mul_of_nonneg_left hgap heta.le
      have hexp :
          Real.exp (-((z : ℝ) * (B - A : ℕ) / B)) ≤
            Real.exp (eta / 9 - (eta / 9) * (d : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      exact hbin.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hzA), Nat.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  · have hd : d ≤ 1 := by omega
    have hdreal : (d : ℝ) ≤ 1 := by exact_mod_cast hd
    have hdz : (0 : ℝ) ≤ d := by positivity
    have hexp : (1 : ℝ) ≤ Real.exp
        (eta / 9 - (eta / 9) * (d : ℝ) ^ 2) := by
      apply Real.one_le_exp_iff.mpr
      have hd2 : (d : ℝ) ^ 2 ≤ 1 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hd2
        (show 0 ≤ eta / 9 by positivity)
      linarith
    calc
      (Nat.choose A z : ℝ) ≤ Nat.choose B z := by
        exact_mod_cast Nat.choose_le_choose z hAB
      _ ≤ (Nat.choose B z : ℝ) *
          Real.exp (eta / 9 - (eta / 9) * (d : ℝ) ^ 2) := by
        simpa using mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg (Nat.choose B z))

/-- One range shell has a bound independent of the total order. -/
theorem coPartite_sizeVectorShell_le
    {r n z : ℕ} (hr : 0 < r) {eta : ℝ} (heta : 0 < eta)
    (hB : 0 < DenseGraph.balancedMultipartiteCrossCapacity r n)
    (hz : eta * (DenseGraph.balancedMultipartiteCrossCapacity r n : ℝ) ≤ z)
    (d : ℕ) :
    (∑ a ∈ DenseGraph.sizeVectorsWithSumAndRange r n hr d,
      (Nat.multinomial Finset.univ a : ℝ) *
        (Nat.choose (DenseGraph.multipartiteCrossCapacity a) z : ℝ)) ≤
      ((Nat.multinomial Finset.univ (DenseGraph.balancedPartSize r n) : ℝ) *
        (Nat.choose (DenseGraph.balancedMultipartiteCrossCapacity r n) z : ℝ)) *
        Real.exp (eta / 9) * DenseGraph.gaussianLatticeWeight r (eta / 9) d := by
  let M : ℝ := Nat.multinomial Finset.univ (DenseGraph.balancedPartSize r n)
  let B : ℝ := Nat.choose (DenseGraph.balancedMultipartiteCrossCapacity r n) z
  let E := Real.exp (eta / 9 - (eta / 9) * (d : ℝ) ^ 2)
  have hpoint : ∀ a ∈ DenseGraph.sizeVectorsWithSumAndRange r n hr d,
      (Nat.multinomial Finset.univ a : ℝ) *
        (Nat.choose (DenseGraph.multipartiteCrossCapacity a) z : ℝ) ≤ M * (B * E) := by
    intro a ha
    obtain ⟨hsum, hd⟩ := DenseGraph.mem_sizeVectorsWithSumAndRange.mp ha
    have hmult : (Nat.multinomial Finset.univ a : ℝ) ≤ M := by
      dsimp only [M]
      exact_mod_cast DenseGraph.multinomial_le_balancedPartSize hr a hsum
    have hchoose := coPartite_choose_le_gaussian hr heta hB hz a hsum
    rw [hd] at hchoose
    exact mul_le_mul hmult hchoose (by positivity) (by dsimp [M]; positivity)
  have hcard : ((DenseGraph.sizeVectorsWithSumAndRange r n hr d).card : ℝ) ≤
      ((d + 1 : ℕ) : ℝ) ^ r := by
    exact_mod_cast DenseGraph.card_sizeVectorsWithSumAndRange_le r n hr d
  calc
    _ ≤ ∑ _a ∈ DenseGraph.sizeVectorsWithSumAndRange r n hr d, M * (B * E) :=
      Finset.sum_le_sum hpoint
    _ = ((DenseGraph.sizeVectorsWithSumAndRange r n hr d).card : ℝ) *
        (M * (B * E)) := by simp
    _ ≤ (((d + 1 : ℕ) : ℝ) ^ r) * (M * (B * E)) :=
      mul_le_mul_of_nonneg_right hcard (by dsimp [M, B, E]; positivity)
    _ = _ := by
      dsimp [M, B, E, DenseGraph.gaussianLatticeWeight]
      rw [show eta / 9 - (eta / 9) * (d : ℝ) ^ 2 =
        eta / 9 + (-(eta / 9) * (d : ℝ) ^ 2) by ring, Real.exp_add]
      ring

/-- Exactly balanced divisions supply the multinomial reference mass inside
the permanent balanced-cover family at every sufficiently large order. -/
theorem eventually_balancedReferenceMass_le_coverPairs
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤ m →
      coPartiteBalancedReferenceMass k n m ≤
        (balancedCoMultipartiteCoverPairFinset k n m
          (supercriticalCoverBalanceRadius k)).card := by
  filter_upwards [eventually_exactlyBalanced_isBalancedFullDivision hk,
    eventually_ge_atTop (k - 1)] with n hbal hn m hm
  have hmult :
      Nat.multinomial Finset.univ (DenseGraph.balancedPartSize (k - 1) n) ≤
        (exactlyBalancedFullSupercriticalDivisions k n).card :=
    (DenseGraph.multinomial_le_card_balancedAssignments (by omega)).trans
      (card_balancedAssignments_le_exactlyBalancedDivisions hk hn)
  have hsubset : exactlyBalancedFullSupercriticalDivisions k n ⊆
      balancedFullSupercriticalDivisions k n (supercriticalCoverBalanceRadius k) := by
    intro D hD
    exact mem_balancedFullSupercriticalDivisions.mpr
      (hbal D (mem_exactlyBalancedFullSupercriticalDivisions.mp hD))
  have hfiber : ∀ D ∈ exactlyBalancedFullSupercriticalDivisions k n,
      (supercriticalCoPartiteFiber D m).card =
        Nat.choose (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n)
          (m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) := by
    intro D hD
    have hD' := mem_exactlyBalancedFullSupercriticalDivisions.mp hD
    rw [card_supercriticalCoPartiteFiber D hD'.1,
      exactlyBalancedDivision_internalCapacity_eq hk hD',
      exactlyBalancedDivision_crossCapacity_eq hk hD', ite_eq_left hm]
  have hnat :
      Nat.multinomial Finset.univ (DenseGraph.balancedPartSize (k - 1) n) *
          Nat.choose (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n)
            (m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) ≤
        (balancedCoMultipartiteCoverPairFinset k n m
          (supercriticalCoverBalanceRadius k)).card := by
    rw [card_balancedCoMultipartiteCoverPairFinset]
    calc
      _ ≤ (exactlyBalancedFullSupercriticalDivisions k n).card *
          Nat.choose (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n)
            (m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) :=
        Nat.mul_le_mul_right _ hmult
      _ = ∑ D ∈ exactlyBalancedFullSupercriticalDivisions k n,
          (supercriticalCoPartiteFiber D m).card := by
        simp_rw [Finset.sum_congr rfl hfiber]
        simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intros; omega)
  unfold coPartiteBalancedReferenceMass
  exact_mod_cast hnat

/-- Uniform lower comparison on a fixed total-density window containing the
critical density. The only loss is twice the ordered-cover factorial. -/
theorem eventually_coPartiteBalancedReferenceMass_le_count
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤ m →
      |(m : ℝ) / (completeEdgeCount n : ℝ) - criticalCoverComparisonDensity k| <
        supercriticalCoverDensityTolerance (criticalCoverComparisonDensity k) →
      coPartiteBalancedReferenceMass k n m ≤
        (2 * (k - 1).factorial : ℕ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n m : ℝ) := by
  filter_upwards [eventually_balancedReferenceMass_le_coverPairs k hk,
    eventually_card_balancedCoMultipartiteCoverPairFinset_le hk
      (criticalCoverComparisonDensity k)
      (criticalCoverComparisonDensity_mem_Ioo hk)] with n href hcover m hm hwindow
  exact (href m hm).trans (hcover m hwindow)


/-- A positive constant depending only on the number of parts and the
missing-edge density reserve. -/
def coPartiteComparisonConstant (r : ℕ) (eta : ℝ) : ℝ :=
  1 + Real.exp (eta / 9) *
    ∑' d : ℕ, DenseGraph.gaussianLatticeWeight r (eta / 9) d

theorem coPartiteComparisonConstant_pos (r : ℕ) (eta : ℝ) :
    0 < coPartiteComparisonConstant r eta := by
  have hsum : 0 ≤ ∑' d : ℕ, DenseGraph.gaussianLatticeWeight r (eta / 9) d :=
    tsum_nonneg (fun d ↦ DenseGraph.gaussianLatticeWeight_nonneg r (eta / 9) d)
  unfold coPartiteComparisonConstant
  positivity

/-- Summing all ordered size vectors incurs only a constant factor. -/
theorem coPartite_sizeVectorSum_le
    {r n z : ℕ} (hr : 0 < r) {eta : ℝ} (heta : 0 < eta)
    (hB : 0 < DenseGraph.balancedMultipartiteCrossCapacity r n)
    (hz : eta * (DenseGraph.balancedMultipartiteCrossCapacity r n : ℝ) ≤ z) :
    (∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) n,
      (Nat.multinomial Finset.univ a : ℝ) *
        (Nat.choose (DenseGraph.multipartiteCrossCapacity a) z : ℝ)) ≤
      coPartiteComparisonConstant r eta *
        ((Nat.multinomial Finset.univ (DenseGraph.balancedPartSize r n) : ℝ) *
          (Nat.choose (DenseGraph.balancedMultipartiteCrossCapacity r n) z : ℝ)) := by
  let vectors := Finset.piAntidiag (Finset.univ : Finset (Fin r)) n
  let M : ℝ := (Nat.multinomial Finset.univ (DenseGraph.balancedPartSize r n) : ℝ) *
    (Nat.choose (DenseGraph.balancedMultipartiteCrossCapacity r n) z : ℝ)
  let f := fun a : Fin r → ℕ ↦ (Nat.multinomial Finset.univ a : ℝ) *
    (Nat.choose (DenseGraph.multipartiteCrossCapacity a) z : ℝ)
  have hmap : ∀ a ∈ vectors, DenseGraph.sizeVectorRange hr a ∈ Finset.Icc 0 n := by
    intro a ha
    have hsum : ∑ i, a i = n := (Finset.mem_piAntidiag.mp ha).1
    obtain ⟨i, hi⟩ := DenseGraph.exists_eq_sizeVectorMax hr a
    have hle : a i ≤ ∑ j : Fin r, a j :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hmax : DenseGraph.sizeVectorMax hr a ≤ n := by omega
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,
      (Nat.sub_le _ _).trans hmax⟩
  have heq :
      (∑ a ∈ vectors, f a) =
        ∑ d ∈ Finset.Icc 0 n,
          ∑ a ∈ DenseGraph.sizeVectorsWithSumAndRange r n hr d, f a := by
    symm
    simpa [DenseGraph.sizeVectorsWithSumAndRange, vectors] using
      Finset.sum_fiberwise_of_maps_to hmap f
  have hsum := DenseGraph.summable_gaussianLatticeWeight r
    (show 0 < eta / 9 by positivity)
  have hfinite :
      (∑ d ∈ Finset.Icc 0 n, DenseGraph.gaussianLatticeWeight r (eta / 9) d) ≤
        ∑' d : ℕ, DenseGraph.gaussianLatticeWeight r (eta / 9) d :=
    Summable.sum_le_tsum _ (fun d _ ↦
      DenseGraph.gaussianLatticeWeight_nonneg r (eta / 9) d) hsum
  have hM : 0 ≤ M := by dsimp [M]; positivity
  calc
    _ = ∑ d ∈ Finset.Icc 0 n,
        ∑ a ∈ DenseGraph.sizeVectorsWithSumAndRange r n hr d, f a := heq
    _ ≤ ∑ d ∈ Finset.Icc 0 n,
        M * Real.exp (eta / 9) * DenseGraph.gaussianLatticeWeight r (eta / 9) d := by
      exact Finset.sum_le_sum fun d _ ↦ coPartite_sizeVectorShell_le hr heta hB hz d
    _ = M * Real.exp (eta / 9) *
        ∑ d ∈ Finset.Icc 0 n, DenseGraph.gaussianLatticeWeight r (eta / 9) d := by
      rw [Finset.mul_sum]
    _ ≤ M * Real.exp (eta / 9) *
        ∑' d : ℕ, DenseGraph.gaussianLatticeWeight r (eta / 9) d :=
      mul_le_mul_of_nonneg_left hfinite (mul_nonneg hM (Real.exp_pos _).le)
    _ ≤ coPartiteComparisonConstant r eta * M := by
      unfold coPartiteComparisonConstant
      nlinarith

/-- Any prescribed full division is counted by its missing cross-edge slice. -/
theorem card_coPartiteFiber_le_choose_missing
    {k n m : ℕ} (D : SupercriticalDivision k (Fin n)) (hD : D.IsFull)
    (hm : m ≤ n.choose 2) :
    (supercriticalCoPartiteFiber D m).card ≤
      Nat.choose (DenseGraph.multipartiteCrossCapacity (criticalMainPartSizeVector D))
        (n.choose 2 - m) := by
  have htotal := supercriticalTotalCrossCapacity_add_internal D
  rw [D.support_eq_univ hD] at htotal
  simp only [Finset.card_univ, Fintype.card_fin] at htotal
  have hcross : supercriticalTotalCrossCapacity D =
      DenseGraph.multipartiteCrossCapacity (criticalMainPartSizeVector D) := by
    exact supercriticalTotalCrossCapacity_eq_multipartiteCrossCapacity D
  rw [card_supercriticalCoPartiteFiber D hD]
  split_ifs with hlo
  · have hsel : m - divisionInternalCliqueCapacity D ≤
        supercriticalTotalCrossCapacity D := by omega
    have hz : supercriticalTotalCrossCapacity D -
        (m - divisionInternalCliqueCapacity D) = n.choose 2 - m := by omega
    rw [← Nat.choose_symm hsel, hz, hcross]
  · exact Nat.zero_le _

/-- The global co-partite family is bounded by the sum over ordered size
vectors. Nonempty refinement ensures all covers are represented. -/
theorem coPartiteCount_le_sizeVectorSum
    {k n m : ℕ} (_hk : 3 ≤ k) (hn : k - 1 ≤ n) (hm : m ≤ n.choose 2) :
    (coMultipartiteGraphCountWithEdges (k - 1) n m : ℝ) ≤
      ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (k - 1))) n,
        (Nat.multinomial Finset.univ a : ℝ) *
          (Nat.choose (DenseGraph.multipartiteCrossCapacity a) (n.choose 2 - m) : ℝ) := by
  let vectors := Finset.piAntidiag (Finset.univ : Finset (Fin (k - 1))) n
  let divisions := fun a : Fin (k - 1) → ℕ ↦
    criticalFixedSparseSizeVectorDivisions k n ∅ a
  have hsub : coMultipartiteGraphFinsetWithEdges (k - 1) n m ⊆
      vectors.biUnion (fun a ↦ (divisions a).biUnion (fun D ↦ supercriticalCoPartiteFiber D m)) := by
    intro G hG
    obtain ⟨⟨C⟩, hcard⟩ := mem_coMultipartiteGraphFinsetWithEdges.mp hG
    obtain ⟨C', hnonempty⟩ := C.exists_nonempty_refinement (by simpa using hn)
    let D := SupercriticalDivision.ofCoMultipartiteWitness C' hnonempty
    have hD : D.IsFull := by simp [D, SupercriticalDivision.IsFull]
    let a := criticalMainPartSizeVector D
    have hsum : ∑ i, a i = n := by
      have h := D.card_support
      rw [D.support_eq_univ hD] at h
      simpa [a, criticalMainPartSizeVector] using h.symm
    have ha : a ∈ vectors := by simp [vectors, hsum]
    have hdiv : D ∈ divisions a :=
      mem_criticalFixedSparseSizeVectorDivisions.mpr ⟨hD, rfl⟩
    have hfiber : G ∈ supercriticalCoPartiteFiber D m := by
      apply mem_supercriticalCoPartiteFiber_iff_isFull_card_isClique.mpr
      exact ⟨hD, by simpa [finiteGraphEdges_card_eq_edgeFinset_card] using hcard,
        C'.isClique⟩
    exact Finset.mem_biUnion.mpr ⟨a, ha,
      Finset.mem_biUnion.mpr ⟨D, hdiv, hfiber⟩⟩
  have hnat : coMultipartiteGraphCountWithEdges (k - 1) n m ≤
      ∑ a ∈ vectors, Nat.multinomial Finset.univ a *
        Nat.choose (DenseGraph.multipartiteCrossCapacity a) (n.choose 2 - m) := by
    calc
      _ ≤ (vectors.biUnion (fun a ↦ (divisions a).biUnion
          (fun D ↦ supercriticalCoPartiteFiber D m))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ a ∈ vectors, ((divisions a).biUnion
          (fun D ↦ supercriticalCoPartiteFiber D m)).card := Finset.card_biUnion_le
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a ha
        have hsum : ∑ i, a i = n := (Finset.mem_piAntidiag.mp ha).1
        calc
          _ ≤ ∑ D ∈ divisions a, (supercriticalCoPartiteFiber D m).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _D ∈ divisions a,
              Nat.choose (DenseGraph.multipartiteCrossCapacity a) (n.choose 2 - m) := by
            apply Finset.sum_le_sum
            intro D hD
            obtain ⟨hfull, hsize⟩ := mem_criticalFixedSparseSizeVectorDivisions.mp hD
            simpa [hsize] using card_coPartiteFiber_le_choose_missing D hfull hm
          _ = (divisions a).card *
              Nat.choose (DenseGraph.multipartiteCrossCapacity a) (n.choose 2 - m) := by simp
          _ ≤ _ := Nat.mul_le_mul_right _
            (card_criticalFixedSparseSizeVectorDivisions_le_multinomial
              (∅ : Finset (Fin n)) a (by simpa using hsum))
  exact_mod_cast hnat

/-- Uniform finite upper comparison in any band with positive missing-edge
density. The lower feasibility guard is necessary for the selected slice. -/
theorem coPartiteCount_le_balancedReferenceMass
    {k n m : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) {eta : ℝ} (heta : 0 < eta)
    (hA : 0 < DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n)
    (hlo : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤ m)
    (hhi : m ≤ n.choose 2)
    (hmissing : eta * (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n : ℝ) ≤
      (n.choose 2 - m : ℕ)) :
    (coMultipartiteGraphCountWithEdges (k - 1) n m : ℝ) ≤
      coPartiteComparisonConstant (k - 1) eta * coPartiteBalancedReferenceMass k n m := by
  have hupper := (coPartiteCount_le_sizeVectorSum hk hn hhi).trans
    (coPartite_sizeVectorSum_le (by omega) heta hA hmissing)
  have htotal := DenseGraph.balancedCross_add_internal (k - 1) n
  have hsel : m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
      DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n := by omega
  have hz : n.choose 2 - m =
      DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n -
        (m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) := by omega
  rw [hz, Nat.choose_symm hsel] at hupper
  exact hupper


/-- Selected-density form of the upper comparison, with the exact balanced
capacity and selected-count quotient retained in the hypothesis. -/
theorem coPartiteCount_le_balancedReferenceMass_of_selectedDensity
    {k n m : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) {eta : ℝ} (heta : 0 < eta)
    (hA : 0 < DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n)
    (hlo : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤ m)
    (hp : ((m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n : ℕ) : ℝ) /
      (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n : ℝ) ≤ 1 - eta) :
    (coMultipartiteGraphCountWithEdges (k - 1) n m : ℝ) ≤
      coPartiteComparisonConstant (k - 1) eta * coPartiteBalancedReferenceMass k n m := by
  let A := DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n
  let C := DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hbound : ((m - C : ℕ) : ℝ) ≤ (1 - eta) * A :=
    (div_le_iff₀ hAr).mp hp
  have hselReal : ((m - C : ℕ) : ℝ) ≤ A := by
    nlinarith
  have hsel : m - C ≤ A := by exact_mod_cast hselReal
  have htotal : A + C = n.choose 2 :=
    DenseGraph.balancedCross_add_internal (k - 1) n
  have hhi : m ≤ n.choose 2 := by omega
  have hmissing : eta * (A : ℝ) ≤ (n.choose 2 - m : ℕ) := by
    rw [Nat.cast_sub hhi, Nat.cast_sub hlo] at *
    have htotalReal : (A : ℝ) + C = n.choose 2 := by exact_mod_cast htotal
    nlinarith
  exact coPartiteCount_le_balancedReferenceMass hk hn heta hA hlo hhi hmissing

/-- Two-sided constant-factor enumeration, uniform in the exact edge count
throughout a fixed window containing the critical density. -/
theorem exists_coPartiteBalancedComparison
    (k : ℕ) (hk : 3 ≤ k) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      0 < DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n →
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤ m →
      ((m - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n : ℕ) : ℝ) /
        (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n : ℝ) ≤ 1 - eta →
      |(m : ℝ) / (completeEdgeCount n : ℝ) - criticalCoverComparisonDensity k| <
        supercriticalCoverDensityTolerance (criticalCoverComparisonDensity k) →
      C⁻¹ * coPartiteBalancedReferenceMass k n m ≤
          (coMultipartiteGraphCountWithEdges (k - 1) n m : ℝ) ∧
        (coMultipartiteGraphCountWithEdges (k - 1) n m : ℝ) ≤
          C * coPartiteBalancedReferenceMass k n m := by
  let F : ℝ := (2 * (k - 1).factorial : ℕ)
  let U := coPartiteComparisonConstant (k - 1) eta
  let C := F + U
  have hF : 0 < F := by dsimp [F]; positivity
  have hU : 0 < U := coPartiteComparisonConstant_pos _ _
  have hC : 0 < C := add_pos hF hU
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_coPartiteBalancedReferenceMass_le_count k hk,
    eventually_ge_atTop (k - 1)] with n hlower hn m hA hlo hp hw
  have hmass : 0 ≤ coPartiteBalancedReferenceMass k n m := by
    unfold coPartiteBalancedReferenceMass
    positivity
  have hcount : (0 : ℝ) ≤ coMultipartiteGraphCountWithEdges (k - 1) n m :=
    Nat.cast_nonneg _
  have hFC : F ≤ C := by dsimp [C]; linarith
  have hUC : U ≤ C := by dsimp [C]; linarith
  constructor
  · have hlow := (hlower m hlo hw).trans
      (mul_le_mul_of_nonneg_right hFC hcount)
    have hdiv := (div_le_iff₀ hC).mpr (by simpa [mul_comm] using hlow)
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  · exact (coPartiteCount_le_balancedReferenceMass_of_selectedDensity
      hk hn heta hA hlo hp).trans (mul_le_mul_of_nonneg_right hUC hmass)

end InducedStars
