import InducedStars.C4.GlobalCounting
import InducedStars.C4.MatchingUniform

/-!
# Absorption of the final C4 counting overheads

The exact split-cover loss is polynomial. It is absorbed into the linear
residual-matching penalty; the two quadratic bad-family probabilities are
kept as a separate term relative to the entire induced-free family.
-/

noncomputable section
open Filter
open scoped Topology
namespace InducedStars

private theorem eventually_c4_three_cover_loss_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 3*((n : ℝ)+1)^2 ≤ Real.exp (c*n) := by
  have hlittle : (fun x : ℝ ↦ 12*x^2) =o[atTop] (fun x ↦ Real.exp (c*x)) :=
    (isLittleO_pow_exp_pos_mul_atTop 2 hc).const_mul_left 12
  filter_upwards [(hlittle.bound (c := 1) zero_lt_one).natCast_atTop,
    eventually_ge_atTop 1] with n h hn
  have hR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h' : 12*(n : ℝ)^2 ≤ Real.exp (c*n) := by
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (by positivity :
      0 ≤ 12*(n : ℝ)^2), abs_of_pos (Real.exp_pos _)] using h
  nlinarith [sq_nonneg ((n : ℝ)-1)]

theorem eventually_c4_local_penalties_absorb_cover {a b l : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hl : 0 < l) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop,
      ((n : ℝ)+1)^2*(Real.exp (-a*(n : ℝ)^2)+Real.exp (-b*(n : ℝ)^2)+
        Real.exp (-l*n)) ≤ Real.exp (-c*n) := by
  let r := min a (min b l)
  have hr : 0 < r := lt_min ha (lt_min hb hl)
  refine ⟨r/2, half_pos hr, ?_⟩
  filter_upwards [eventually_c4_three_cover_loss_le (half_pos hr),
    eventually_ge_atTop 1] with n hcover hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hA : Real.exp (-a*(n : ℝ)^2) ≤ Real.exp (-r*n) := by
    apply Real.exp_le_exp.mpr
    have hle := mul_le_mul_of_nonneg_right (min_le_left a (min b l)) (sq_nonneg (n : ℝ))
    have hle' := mul_le_mul_of_nonneg_left hs hr.le
    dsimp only [r] at hle'
    nlinarith
  have hB : Real.exp (-b*(n : ℝ)^2) ≤ Real.exp (-r*n) := by
    apply Real.exp_le_exp.mpr
    have hle := mul_le_mul_of_nonneg_right
      ((min_le_right a (min b l)).trans (min_le_left b l)) (sq_nonneg (n : ℝ))
    have hle' := mul_le_mul_of_nonneg_left hs hr.le
    dsimp only [r] at hle'
    nlinarith
  have hL : Real.exp (-l*n) ≤ Real.exp (-r*n) := by
    apply Real.exp_le_exp.mpr
    have hle := mul_le_mul_of_nonneg_right
      ((min_le_right a (min b l)).trans (min_le_right b l)) (Nat.cast_nonneg (α := ℝ) n)
    dsimp only [r]
    linarith
  calc
    _ ≤ 3*((n : ℝ)+1)^2*Real.exp (-r*n) := by
      have hsum := add_le_add (add_le_add hA hB) hL
      nlinarith only [mul_le_mul_of_nonneg_left hsum (sq_nonneg ((n : ℝ)+1))]
    _ ≤ Real.exp (r/2*n)*Real.exp (-r*n) :=
      mul_le_mul_of_nonneg_right hcover (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventually_c4_quadratic_penalties_combine {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop,
      Real.exp (-a*(n : ℝ)^2)+Real.exp (-b*(n : ℝ)^2) ≤ Real.exp (-c*(n : ℝ)^2) := by
  let r := min a b
  have hr : 0 < r := lt_min ha hb
  refine ⟨r/2, half_pos hr, ?_⟩
  filter_upwards [eventually_c4Polynomial_le_linearExp (half_pos hr),
    eventually_ge_atTop 1] with n hpoly hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have htwo : 2 ≤ Real.exp (r/2*(n : ℝ)^2) := by
    apply (show (2 : ℝ) ≤ (n : ℝ)^2+1 by nlinarith).trans
    apply hpoly.trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs (half_pos hr).le)
  have hA : Real.exp (-a*(n : ℝ)^2) ≤ Real.exp (-r*(n : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg (n : ℝ))]
  have hB : Real.exp (-b*(n : ℝ)^2) ≤ Real.exp (-r*(n : ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg (n : ℝ))]
  calc
    _ ≤ 2*Real.exp (-r*(n : ℝ)^2) := by linarith
    _ ≤ Real.exp (r/2*(n : ℝ)^2)*Real.exp (-r*(n : ℝ)^2) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Final counting algebra from the five independently established bounds.
This lemma has only their explicit finite inequalities as inputs; the
paper-facing result chooses parameters and discharges all five inputs. -/
theorem eventually_c4_count_bound_of_five_penalties
    {gamma epsilon zeta alpha a b l f g : ℝ} {m : ℕ → ℕ}
    (halpha : 0 ≤ alpha) (ha : 0 < a) (hb : 0 < b) (hl : 0 < l)
    (hf : 0 < f) (hg : 0 < g)
    (hA : ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
      ((c4HighIndependentGraphFinset n (m n) gamma epsilon zeta alpha D).card : ℝ) ≤
        (c4SplitFiber D (m n)).card*Real.exp (-a*(n : ℝ)^2))
    (hB : ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
      ((c4HighCliqueGraphFinset n (m n) gamma epsilon zeta alpha D).card : ℝ) ≤
        (c4SplitFiber D (m n)).card*Real.exp (-b*(n : ℝ)^2))
    (hL : ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
      (∑ q ∈ Finset.Icc 1 n,
        ((c4LowDegreeMatchingGraphFinset n (m n) gamma epsilon zeta alpha D q).card : ℝ)) ≤
        (c4SplitFiber D (m n)).card*Real.exp (-l*n))
    (hF : ∀ᶠ n in atTop, ((c4FarGraphFinset n (m n) epsilon).card : ℝ) ≤
      Real.exp (-f*(n : ℝ)^2)*(inducedC4FreeGraphCountWithEdges n (m n) : ℝ))
    (hG : ∀ᶠ n in atTop,
      ((c4CloseDegenerateGraphFinset n (m n) gamma epsilon zeta).card : ℝ) ≤
        Real.exp (-g*(n : ℝ)^2)*(inducedC4FreeGraphCountWithEdges n (m n) : ℝ)) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ᶠ n in atTop,
      (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) ≤
        (1+Real.exp (-c*n))*(splitGraphCountWithEdges n (m n) : ℝ)+
          Real.exp (-d*(n : ℝ)^2)*(inducedC4FreeGraphCountWithEdges n (m n) : ℝ) := by
  obtain ⟨c, hc, hlocal⟩ := eventually_c4_local_penalties_absorb_cover ha hb hl
  obtain ⟨d, hd, hglobal⟩ := eventually_c4_quadratic_penalties_combine hf hg
  refine ⟨c, d, hc, hd, ?_⟩
  filter_upwards [hA,hB,hL,hF,hG,hlocal,hglobal] with n hA hB hL hF hG hlocal hglobal
  have hraw := c4Nonsplit_card_le_weighted_reference n (m n) gamma epsilon zeta alpha halpha
    (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le hA hB hL
  have hsum := congrArg (fun t : ℕ ↦ (t : ℝ)) (splitGraphCount_add_c4NonsplitCount n (m n))
  push_cast at hsum
  have hlocal' := mul_le_mul_of_nonneg_right hlocal
    (Nat.cast_nonneg (α := ℝ) (splitGraphCountWithEdges n (m n)))
  have hglobal' := mul_le_mul_of_nonneg_right hglobal
    (Nat.cast_nonneg (α := ℝ) (inducedC4FreeGraphCountWithEdges n (m n)))
  nlinarith only [hraw,hsum,hF,hG,hlocal',hglobal']

end InducedStars
