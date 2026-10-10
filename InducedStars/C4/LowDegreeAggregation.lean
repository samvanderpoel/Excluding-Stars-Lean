import InducedStars.C4.LowDegreeSums
import InducedStars.C4.MatchingUniform

/-!
# Actual low-degree matching-defect aggregation

Paper: `eqn:c4-fmat-sum`. The matching penalty is applied to the actual
induced-C4-free fibers. Impossible internal-edge quotas contribute zero;
the remaining signed shifts and supported patterns are summed by the
axiom-free low-degree counting bounds.
-/

noncomputable section
open Finset Filter
open scoped Classical Topology
namespace InducedStars

theorem c4FixedDefectFreeFiber_le_fullFiber_mul_of_choose_bound
    {n m : ℕ} (D : C4Division (Fin n)) (T : SimpleGraph (Fin n))
    (hT : C4DefectSupported D T) {a : ℝ}
    (h : ((c4FixedDefectFreeFiber D T m).card : ℝ) ≤
      (Nat.choose (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) : ℝ) * a) :
    ((c4FixedDefectFreeFiber D T m).card : ℝ) ≤
      ((c4FixedDefectFiber D T m).card : ℝ) * a := by
  by_cases hforced : c4FixedDefectInternalCount D T ≤ m
  · simpa only [card_c4FixedDefectFiber D T hT, if_pos hforced,
      card_c4CrossPotentialEdges] using h
  · have hempty : (c4FixedDefectFiber D T m).card = 0 := by
      rw [card_c4FixedDefectFiber D T hT, if_neg hforced]
    have hle : (c4FixedDefectFreeFiber D T m).card ≤ (c4FixedDefectFiber D T m).card :=
      card_le_card (filter_subset _ _)
    have hzero : (c4FixedDefectFreeFiber D T m).card = 0 := by omega
    simp [hempty, hzero]

def c4LowDegreeFreeTotal {n : ℕ} (D : C4Division (Fin n))
    (m : ℕ) (alpha epsilon : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 n,
    ∑ T ∈ (c4LowDegreeDefectPatternFinset D alpha k).filter
      (fun T ↦ ((finiteGraphEdges T).card : ℝ) ≤ epsilon * (n : ℝ) ^ 2),
        ((c4FixedDefectFreeFiber D T m).card : ℝ)

theorem c4ReferenceBand_of_samplingBounds {n m : ℕ} (D : C4Division (Fin n))
    {beta : ℝ} (h : C4NondegenerateSamplingBounds n m D.cliquePart.card 0 0 beta) :
    D.cliquePart.card.choose 2 ≤ m ∧
      m - D.cliquePart.card.choose 2 ≤ D.independentPart.card * D.cliquePart.card ∧
      beta * (D.independentPart.card * D.cliquePart.card : ℕ) ≤
        (m - D.cliquePart.card.choose 2 : ℕ) ∧
      ((m - D.cliquePart.card.choose 2 : ℕ) : ℝ) ≤
        (1 - beta) * (D.independentPart.card * D.cliquePart.card : ℕ) := by
  have hparts := D.card_add
  simp only [Fintype.card_fin] at hparts
  have hA : n - D.cliquePart.card = D.independentPart.card := by omega
  have hbaseR : (D.cliquePart.card.choose 2 : ℝ) ≤ m := by
    have hp := h.selected_pos
    simp only [Int.cast_zero, sub_zero] at hp
    linarith
  have hbase : D.cliquePart.card.choose 2 ≤ m := by exact_mod_cast hbaseR
  have hcap : 0 < ((D.independentPart.card * D.cliquePart.card : ℕ) : ℝ) := by
    have hp := h.capacity_pos
    simpa only [Nat.cast_zero, sub_zero, hA, Nat.mul_comm] using hp
  have hqcast : ((m - D.cliquePart.card.choose 2 : ℕ) : ℝ) =
      (m : ℝ) - (D.cliquePart.card.choose 2 : ℝ) := Nat.cast_sub hbase
  have hqcap : ((m - D.cliquePart.card.choose 2 : ℕ) : ℝ) ≤
      (D.independentPart.card * D.cliquePart.card : ℕ) := by
    rw [hqcast]
    simpa only [Int.cast_zero, sub_zero, Nat.cast_zero, hA, Nat.mul_comm]
      using h.selected_lt_capacity.le
  have hrat : ((m - D.cliquePart.card.choose 2 : ℕ) : ℝ) /
      (D.independentPart.card * D.cliquePart.card : ℕ) ∈ Set.Icc beta (1 - beta) := by
    rw [hqcast]
    simpa only [Int.cast_zero, sub_zero, Nat.cast_zero, hA, Nat.mul_comm] using h.ratio_mem
  exact ⟨hbase, by exact_mod_cast hqcap, (le_div_iff₀ hcap).mp hrat.1,
    (div_le_iff₀ hcap).mp hrat.2⟩

/-- The final low-degree sum is exponentially smaller than the split fiber
on the same division. All constants precede the arbitrary edge sequence;
smaller degree and defect thresholds remain admissible. -/
theorem inducedC4LowDegreeMatchingTotal {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    ∃ zeta > 0, ∃ epsilon > 0, ∃ alpha0 > 0, alpha0 ≤ 1 / 2 ∧ ∃ c > 0,
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
          |(D.cliquePart.card : ℝ) / n - c4Lambda gamma| ≤ zeta →
          ∀ alpha ∈ Set.Icc (0 : ℝ) alpha0, ∀ eps ≤ epsilon,
            c4LowDegreeFreeTotal D (m n) alpha eps ≤
              (Nat.choose (D.independentPart.card * D.cliquePart.card)
                (m n - D.cliquePart.card.choose 2) : ℝ) * Real.exp (-c * n) := by
  obtain ⟨zm, hzm, epsilon, hepsilon, c, hc, hmatching⟩ := inducedC4MatchingPenalty hgamma
  obtain ⟨zb, hzb, eb, heb, beta, hbeta, hhalf, hband⟩ :=
    exists_c4NondegenerateSamplingBand hgamma
  obtain ⟨alpha0, ha0, hahalf, hsum⟩ := exists_alpha0_c4LowDegree_matching_sum hbeta hhalf hc
  refine ⟨min zm zb, lt_min hzm hzb, epsilon, hepsilon,
    alpha0, ha0, hahalf, c / 4, by positivity, ?_⟩
  intro m hm
  filter_upwards [hmatching m hm, hband m hm, hsum] with n hmatching hband hsum
  intro D hclose alpha ha eps heps
  have hparts := D.card_add
  simp only [Fintype.card_fin] at hparts
  have hb : D.cliquePart.card ≤ n := by omega
  have hsamp := hband.2 D.cliquePart.card hb (hclose.trans (min_le_right _ _))
    0 (by simp; positivity) 0 (Nat.zero_le n)
  obtain ⟨hbase, href, hlo, hhi⟩ := c4ReferenceBand_of_samplingBounds D hsamp
  refine le_trans ?_ (hsum alpha ha D (m n) hbase href hlo hhi)
  unfold c4LowDegreeFreeTotal
  apply sum_le_sum
  intro k hk
  have hkpos : 1 ≤ k := (mem_Icc.mp hk).1
  calc
    _ ≤ ∑ T ∈ (c4LowDegreeDefectPatternFinset D alpha k).filter
        (fun T ↦ ((finiteGraphEdges T).card : ℝ) ≤ eps * (n : ℝ) ^ 2),
          Real.exp (-c * k * n) * ((c4FixedDefectFiber D T (m n)).card : ℝ) := by
      apply sum_le_sum
      intro T hT
      obtain ⟨hpattern, hsmall⟩ := mem_filter.mp hT
      obtain ⟨hsupported, hindex, hdegree⟩ := mem_c4LowDegreeDefectPatternFinset.mp hpattern
      have hsmall' : ((finiteGraphEdges T).card : ℝ) ≤ epsilon * (n : ℝ) ^ 2 :=
        hsmall.trans (mul_le_mul_of_nonneg_right heps (sq_nonneg _))
      have hpenalty := hmatching D (hclose.trans (min_le_left _ _)) T hsmall' k hkpos
        (c4SideMatchingNumber_eq_imp_matching D T hindex)
      simpa only [mul_comm] using
        c4FixedDefectFreeFiber_le_fullFiber_mul_of_choose_bound D T hsupported hpenalty
    _ ≤ ∑ T ∈ c4LowDegreeDefectPatternFinset D alpha k,
        Real.exp (-c * k * n) * ((c4FixedDefectFiber D T (m n)).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ by positivity)
    _ = _ := (mul_sum _ _ _).symm

end InducedStars
