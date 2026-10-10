import InducedStars.Structure.Supercritical.GlobalAggregation
import Mathlib.Tactic

/-!
# Two-scale algebra for the final supercritical bound

This file contains only the last numerical consolidation.  It turns the two
linear good-family errors and the two quadratic errors into one positive rate
of each scale.  The combinatorial estimates themselves remain in the
aggregation modules.
-/

noncomputable section

open Filter Set

namespace InducedStars

/-- Two linear errors relative to the co-multipartite family and two
quadratic errors (one relative to each ambient family) can be consolidated
into the two-scale form used by the final limit argument. -/
theorem eventually_supercriticalGlobalExceptional_two_term_of_four_term
    (k : ℕ) (hk : 3 ≤ k) (m : ℕ → ℕ)
    (cClean cFixed cMedium cFar : ℝ)
    (hcClean : 0 < cClean) (hcFixed : 0 < cFixed)
    (hcMedium : 0 < cMedium) (hcFar : 0 < cFar)
    (hfour : ∀ᶠ n : ℕ in atTop,
      ((supercriticalNonCoMultipartiteGraphFinset k n (m n)).card : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
          (Real.exp (-cClean * (n : ℝ)) +
            Real.exp (-cFixed * (n : ℝ)) +
            Real.exp (-cMedium * (n : ℝ) ^ 2)) +
        (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
          Real.exp (-cFar * (n : ℝ) ^ 2)) :
    ∀ᶠ n : ℕ in atTop,
      ((supercriticalNonCoMultipartiteGraphFinset k n (m n)).card : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
          Real.exp (-((min cClean cFixed / 2) * (n : ℝ))) +
        (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
          Real.exp (-((min cMedium cFar / 2) * (n : ℝ) ^ 2)) := by
  have hcLinear : 0 < min cClean cFixed := lt_min hcClean hcFixed
  have hcQuadratic : 0 < min cMedium cFar := lt_min hcMedium hcFar
  filter_upwards [hfour,
      eventually_two_mul_exp_neg_linear_le hcLinear,
      eventually_two_mul_exp_neg_quadratic_le hcQuadratic]
      with n hn hlinear hquadratic
  let good : ℝ := coMultipartiteGraphCountWithEdges (k - 1) n (m n)
  let total : ℝ := inducedStarFreeGraphCountWithEdges k n (m n)
  have hgood0 : 0 ≤ good := by positivity
  have htotal0 : 0 ≤ total := by positivity
  have hgoodTotal : good ≤ total := by
    have hdecomp :=
      inducedStarFreeGraphCountWithEdges_eq_coMultipartite_add_nonCoMultipartite
        (k := k) (n := n) (m := m n) (by omega)
    dsimp [good, total]
    exact_mod_cast (show coMultipartiteGraphCountWithEdges (k - 1) n (m n) ≤
        inducedStarFreeGraphCountWithEdges k n (m n) by omega)
  have hcleanExp : Real.exp (-cClean * (n : ℝ)) ≤
      Real.exp (-(min cClean cFixed * (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith [min_le_left cClean cFixed]
  have hfixedExp : Real.exp (-cFixed * (n : ℝ)) ≤
      Real.exp (-(min cClean cFixed * (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith [min_le_right cClean cFixed]
  have hmediumExp : Real.exp (-cMedium * (n : ℝ) ^ 2) ≤
      Real.exp (-(min cMedium cFar * (n : ℝ) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    nlinarith [min_le_left cMedium cFar]
  have hfarExp : Real.exp (-cFar * (n : ℝ) ^ 2) ≤
      Real.exp (-(min cMedium cFar * (n : ℝ) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    nlinarith [min_le_right cMedium cFar]
  have hlinearSum :
      Real.exp (-cClean * (n : ℝ)) +
          Real.exp (-cFixed * (n : ℝ)) ≤
        2 * Real.exp (-(min cClean cFixed * (n : ℝ))) := by
    linarith
  have hquadraticSum :
      Real.exp (-cMedium * (n : ℝ) ^ 2) +
          Real.exp (-cFar * (n : ℝ) ^ 2) ≤
        2 * Real.exp (-(min cMedium cFar * (n : ℝ) ^ 2)) := by
    linarith
  change ((supercriticalNonCoMultipartiteGraphFinset k n (m n)).card : ℝ) ≤
    good * Real.exp (-((min cClean cFixed / 2) * (n : ℝ))) +
      total * Real.exp (-((min cMedium cFar / 2) * (n : ℝ) ^ 2))
  calc
    ((supercriticalNonCoMultipartiteGraphFinset k n (m n)).card : ℝ) ≤
        good * (Real.exp (-cClean * (n : ℝ)) +
          Real.exp (-cFixed * (n : ℝ)) +
          Real.exp (-cMedium * (n : ℝ) ^ 2)) +
        total * Real.exp (-cFar * (n : ℝ) ^ 2) := by
      simpa [good, total] using hn
    _ = good * (Real.exp (-cClean * (n : ℝ)) +
          Real.exp (-cFixed * (n : ℝ))) +
        (good * Real.exp (-cMedium * (n : ℝ) ^ 2) +
          total * Real.exp (-cFar * (n : ℝ) ^ 2)) := by ring
    _ ≤ good * (2 * Real.exp (-(min cClean cFixed * (n : ℝ)))) +
        total * (Real.exp (-cMedium * (n : ℝ) ^ 2) +
          Real.exp (-cFar * (n : ℝ) ^ 2)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hlinearSum hgood0
      · exact add_le_add
          (mul_le_mul_of_nonneg_right hgoodTotal (Real.exp_nonneg _)) le_rfl
          |>.trans_eq (by ring)
    _ ≤ good * (2 * Real.exp (-(min cClean cFixed * (n : ℝ)))) +
        total * (2 * Real.exp (-(min cMedium cFar * (n : ℝ) ^ 2))) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hquadraticSum htotal0)
    _ ≤ good * Real.exp (-((min cClean cFixed / 2) * (n : ℝ))) +
        total * Real.exp (-((min cMedium cFar / 2) * (n : ℝ) ^ 2)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlinear hgood0)
        (mul_le_mul_of_nonneg_left hquadratic htotal0)

theorem supercriticalGlobalLinearRate_pos
    {cClean cFixed : ℝ} (hcClean : 0 < cClean) (hcFixed : 0 < cFixed) :
    0 < min cClean cFixed / 2 := half_pos (lt_min hcClean hcFixed)

theorem supercriticalGlobalQuadraticRate_pos
    {cMedium cFar : ℝ} (hcMedium : 0 < cMedium) (hcFar : 0 < cFar) :
    0 < min cMedium cFar / 2 := half_pos (lt_min hcMedium hcFar)

end InducedStars
