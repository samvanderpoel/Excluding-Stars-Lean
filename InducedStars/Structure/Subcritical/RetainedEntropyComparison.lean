import InducedStars.Structure.Subcritical.RetainedProfileFunctionals
import DenseGraph.Combinatorics.BinomialEntropyPerturbation

/-!
# Entropy comparison for exact retained vectors

Paper: `lemma:clean-retained-comparison-K1k`, in retained-key form and natural exponential units. All finite estimates use the
actual edge count `m-b`, never a rate of convergence for an edge-density
sequence. The diagonal correction contributes only an explicit linear
error. No Stirling assumption is used.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

/-- Natural-logarithm slope of the subcritical entropy branch. -/
def subcriticalRetainedEntropySlope (k : ℕ) : ℝ :=
  ((k - 2 : ℕ) : ℝ) * Real.binEntropy (pK k) /
    (1 + ((k - 2 : ℕ) : ℝ) * pK k)

theorem subcriticalRetainedEntropySlope_nonneg {k : ℕ} (hk : 3 ≤ k) :
    0 ≤ subcriticalRetainedEntropySlope k := by
  have hp := pK_pos (by omega : 2 ≤ k)
  have hh := Real.binEntropy_nonneg hp.le (pK_lt_one (by omega : 2 ≤ k)).le
  unfold subcriticalRetainedEntropySlope
  positivity

theorem logTwo_mul_entropyDensityLower (k : ℕ) (gamma : ℝ) :
    Real.log 2 * entropyDensityLower k gamma = subcriticalRetainedEntropySlope k * gamma := by
  unfold entropyDensityLower subcriticalRetainedEntropySlope binaryEntropy
  have hl := realLogTwo_pos.ne'
  field_simp
  <;> ring

section Upper
variable {k n : ℕ}

/-- Exact-vector upper bound. The only finite reserve is that its actual
weighted graphon lies on the subcritical entropy branch. -/
theorem retainedEdgeCountMultiplicity_le_exp_subcriticalEntropy
    (hk : 3 ≤ k) (hn : 0 < n) (D : SubcriticalDivision k (Fin n))
    (v : RetainedEdgeCountVector D 0 (Fintype.card (Fin n)))
    (hpos : 0 < retainedCliqueCapacity D 0 (Fintype.card (Fin n)) + retainedEdgeCountTotal v)
    (hcap : 2 * ((retainedCliqueCapacity D 0 (Fintype.card (Fin n)) : ℝ) +
        retainedEdgeCountTotal v) + D.support.card ≤ gammaK k * (n : ℝ)^2) :
    (retainedEdgeCountMultiplicity v : ℝ) ≤
      Real.exp (subcriticalRetainedEntropySlope k *
        ((retainedCliqueCapacity D 0 (Fintype.card (Fin n)) : ℝ) +
          retainedEdgeCountTotal v) + subcriticalRetainedEntropySlope k / 2 * D.support.card) := by
  let g := graphonEdgeDensity (retainedProfileGraphon D v)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (0 : ℝ) < (retainedCliqueCapacity D 0 (Fintype.card (Fin n)) : ℝ) +
      retainedEdgeCountTotal v := by exact_mod_cast hpos
  have hgpos : 0 < g := by
    dsimp [g]
    rw [retainedProfileGraphon_edgeDensity hn]
    apply div_pos _ (sq_pos_of_pos hnR)
    have hs : (0 : ℝ) ≤ D.support.card := by positivity
    linarith
  have hgle : g ≤ gammaK k := by
    dsimp [g]
    rw [retainedProfileGraphon_edgeDensity hn]
    apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
    linarith
  have hg : g ∈ Ioo (0 : ℝ) 1 := ⟨hgpos, hgle.trans_lt (gammaK_lt_one hk)⟩
  have hbound := graphonEntropy_le_entropyDensity k hk g hg (retainedProfileGraphon D v)
    ⟨retainedProfileGraphon_inducedStar_free hk hn D v, rfl⟩
  rw [entropyDensity_of_le hgle] at hbound
  apply (retainedEdgeCountMultiplicity_le_exp_profileEntropy v).trans
  apply Real.exp_le_exp.mpr
  rw [retainedProfileEntropyNat_eq_graphonEntropy hn]
  have hmul := mul_le_mul_of_nonneg_left hbound
    (by positivity : 0 ≤ Real.log 2 * (n : ℝ)^2 / 2)
  calc
    _ ≤ Real.log 2 * (n : ℝ)^2 / 2 * entropyDensityLower k g := hmul
    _ = (n : ℝ)^2 / 2 * (Real.log 2 * entropyDensityLower k g) := by ring
    _ = (n : ℝ)^2 / 2 * (subcriticalRetainedEntropySlope k * g) := by
      rw [logTwo_mul_entropyDensityLower]
    _ = _ := by
      dsimp [g]
      rw [retainedProfileGraphon_edgeDensity hn]
      field_simp
      <;> ring

/-- A key's nonempty division carries exactly the same finite count vector
as its full-retained presentation. -/
def retainedKeySomeVector (D : SubcriticalDivision k (Fin n))
    (v : RetainedKeyEdgeCountVector (some D)) :
    RetainedEdgeCountVector D 0 (Fintype.card (Fin n)) where
  count e := (v e).val
  count_le_capacity e := by
    have h := Nat.lt_succ_iff.mp (v e).isLt
    simpa only [SubcriticalRetainedKey.activeCapacity,
      SubcriticalRetainedKey.activeEdges, retainedActivePotentialEdges_card] using h

@[simp] theorem retainedKeySomeVector_total (D : SubcriticalDivision k (Fin n))
    (v : RetainedKeyEdgeCountVector (some D)) :
    retainedEdgeCountTotal (retainedKeySomeVector D v) = retainedKeyEdgeCountTotal v := rfl

@[simp] theorem retainedKeySomeVector_multiplicity (D : SubcriticalDivision k (Fin n))
    (v : RetainedKeyEdgeCountVector (some D)) :
    retainedEdgeCountMultiplicity (retainedKeySomeVector D v) = retainedKeyEdgeCountMultiplicity v := by
  simp only [retainedEdgeCountMultiplicity, retainedKeyEdgeCountMultiplicity,
    retainedKeySomeVector, SubcriticalRetainedKey.activeCapacity,
    SubcriticalRetainedKey.activeEdges]
  apply Finset.prod_congr rfl
  intro e he
  congr 1
  exact (retainedActivePotentialEdges_card D 0 (Fintype.card (Fin n)) e).symm

/-- Uniform exact-vector estimate over every key. Positive retained edge
count makes the empty-key case impossible, rather than dropping that case. -/
theorem retainedKeyEdgeCountMultiplicity_le_exp_subcriticalEntropy
    (hk : 3 ≤ k) (hn : 0 < n) (K : SubcriticalRetainedKey k (Fin n))
    {m b : ℕ} (hbm : b < m)
    (hcap : 2 * ((m : ℝ) - b) + n ≤ gammaK k * (n : ℝ)^2)
    (v : RetainedKeyEdgeCountVector K)
    (hv : K.cliqueCapacity + retainedKeyEdgeCountTotal v + b = m) :
    (retainedKeyEdgeCountMultiplicity v : ℝ) ≤
      Real.exp (subcriticalRetainedEntropySlope k * ((m : ℝ) - b) +
        subcriticalRetainedEntropySlope k / 2 * n) := by
  cases K with
  | none =>
    have hz : retainedKeyEdgeCountTotal v = 0 := by
      change (∑ e : Empty, (v e).val) = 0
      exact Finset.sum_eq_zero (fun e _ ↦ Empty.elim e)
    have hc : SubcriticalRetainedKey.cliqueCapacity (none : SubcriticalRetainedKey k (Fin n)) = 0 := rfl
    omega
  | some D =>
    have hc : SubcriticalRetainedKey.cliqueCapacity (some D : SubcriticalRetainedKey k (Fin n)) =
        retainedCliqueCapacity D 0 (Fintype.card (Fin n)) := by
      exact retainedCliquePotentialEdges_card D 0 _
    rw [hc] at hv
    have hid : (retainedCliqueCapacity D 0 (Fintype.card (Fin n)) : ℝ) +
        retainedKeyEdgeCountTotal v = (m : ℝ) - b := by
      have hreal : (retainedCliqueCapacity D 0 (Fintype.card (Fin n)) : ℝ) +
          retainedKeyEdgeCountTotal v + b = m := by exact_mod_cast hv
      linarith
    have hs : (D.support.card : ℝ) ≤ n := by
      exact_mod_cast (show D.support.card ≤ n by simpa using Finset.card_le_univ D.support)
    have hb := retainedEdgeCountMultiplicity_le_exp_subcriticalEntropy hk hn D
      (retainedKeySomeVector D v) (by simp only [retainedKeySomeVector_total]; omega)
      (by rw [retainedKeySomeVector_total, hid]; linarith)
    rw [retainedKeySomeVector_multiplicity, retainedKeySomeVector_total, hid] at hb
    apply hb.trans
    apply Real.exp_le_exp.mpr
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hs (show 0 ≤ subcriticalRetainedEntropySlope k / 2 from
        div_nonneg (subcriticalRetainedEntropySlope_nonneg hk) (by norm_num)))

end Upper

section PartitionFunction
variable {k n : ℕ}

theorem retainedKey_activeCapacity_le_sq (K : SubcriticalRetainedKey k (Fin n))
    (e : K.ActiveIndex) : K.activeCapacity e ≤ n ^ 2 := by
  cases K with
  | none => exact Empty.elim e
  | some D =>
    change RetainedActivePair D 0 (Fintype.card (Fin n)) at e
    change (retainedActivePotentialEdges D 0 (Fintype.card (Fin n)) e).card ≤ n^2
    calc
      _ = retainedActiveCapacity D 0 (Fintype.card (Fin n)) e :=
        retainedActivePotentialEdges_card D 0 (Fintype.card (Fin n)) e
      _ ≤ n^2 := by
        rw [retainedActiveCapacity, pow_two]
        exact Nat.mul_le_mul (by simpa using Finset.card_le_univ (D.part e.leftPart))
          (by simpa using Finset.card_le_univ (D.part e.rightPart))

theorem retainedKeyEdgeCountVector_card_le (K : SubcriticalRetainedKey k (Fin n)) :
    Fintype.card (RetainedKeyEdgeCountVector K) ≤
      (n + 1) ^ (2 * Fintype.card K.ActiveIndex) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ e : K.ActiveIndex, (n + 1)^2 := by
      apply Finset.prod_le_prod (fun e he ↦ Nat.zero_le _)
      intro e he
      have h := retainedKey_activeCapacity_le_sq K e
      calc
        _ ≤ n^2 + 1 := Nat.add_le_add_right h 1
        _ ≤ n^2 + 2*n + 1 := by omega
        _ = (n+1)^2 := by ring
    _ = _ := by simp [← pow_mul]

/-- Finite partition-function entropy bound, uniform in the retained key.
The active-index bound is a geometric cardinal bound, not a counting
estimate supplied as a hypothesis. -/
theorem retainedKeyPartitionFunction_le_exp_entropy
    (hk : 3 ≤ k) (hn : 0 < n) (K : SubcriticalRetainedKey k (Fin n))
    {m b Q : ℕ} (hbm : b < m)
    (hcap : 2 * ((m : ℝ) - b) + n ≤ gammaK k * (n : ℝ)^2)
    (hQ : Fintype.card K.ActiveIndex ≤ Q) (delta : ℝ) :
    (retainedKeyPartitionFunction K m delta (b : ℤ) : ℝ) ≤
      Real.exp (subcriticalRetainedEntropySlope k * ((m : ℝ) - b) +
        subcriticalRetainedEntropySlope k / 2 * n +
          (2 * Q : ℕ) * Real.log ((n : ℝ) + 1)) := by
  let E := subcriticalRetainedEntropySlope k * ((m : ℝ) - b) +
    subcriticalRetainedEntropySlope k / 2 * n
  have hcard : (retainedKeyEdgeCountLevel K m delta (b : ℤ)).card ≤ (n + 1)^(2*Q) :=
    (Finset.card_le_univ _).trans ((retainedKeyEdgeCountVector_card_le K).trans
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hQ)))
  have hmain : (retainedKeyPartitionFunction K m delta (b : ℤ) : ℝ) ≤
      ((n : ℝ) + 1)^(2*Q) * Real.exp E := by
    rw [retainedKeyPartitionFunction, Nat.cast_sum]
    calc
      _ ≤ ∑ v ∈ retainedKeyEdgeCountLevel K m delta (b : ℤ), Real.exp E := by
        apply Finset.sum_le_sum
        intro v hv
        have hid := (Finset.mem_filter.mp hv).2.1
        have hnat : K.cliqueCapacity + retainedKeyEdgeCountTotal v + b = m := by omega
        exact retainedKeyEdgeCountMultiplicity_le_exp_subcriticalEntropy hk hn K hbm hcap v hnat
      _ = ((retainedKeyEdgeCountLevel K m delta (b : ℤ)).card : ℝ) * Real.exp E := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos _).le
  apply hmain.trans_eq
  rw [show ((n : ℝ) + 1)^(2*Q) =
      Real.exp ((2*Q : ℕ) * Real.log ((n : ℝ) + 1)) by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]]
  rw [← Real.exp_add]
  congr 1
  dsimp [E]
  ring

end PartitionFunction
end InducedStars
