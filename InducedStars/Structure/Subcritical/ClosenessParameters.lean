import InducedStars.Structure.Subcritical.RealizedCells

/-!
# Explicit parameters for subcritical component alignment

The source proof chooses several small constants successively.  This module
packages one completely explicit nested-minimum choice.  Every inequality is
finite and independent of the candidate representation, graph order, and
input graph.
-/

noncomputable section

open Set

namespace InducedStars

/-- The lower relative size used for the visible-subset density estimate. -/
def subcriticalVisibleScale (alpha theta : ℝ) : ℝ :=
  alpha * theta / 4

/-- Numerical data sufficient for the finite cell/component alignment
argument.  The alignment error is definitionally `(B + 3) * zeta`. -/
structure SubcriticalClosenessParameters
    (k R₀ : ℕ) (omega eta theta alpha delta epsilon : ℝ) where
  t : ℝ
  B : ℕ
  zeta : ℝ
  beta : ℝ
  epsilonWork : ℝ

  t_pos : 0 < t
  t_le_theta : t ≤ theta
  t_le_one : t ≤ 1
  t_le_eta : t ≤ eta / (8 * (R₀ : ℝ) ^ 2)

  R₀_le_B : R₀ ≤ B
  four_div_t_le_B : 4 / t ≤ (B : ℝ)

  zeta_pos : 0 < zeta
  beta_pos : 0 < beta
  epsilonWork_mem : epsilonWork ∈ Set.Ioo (0 : ℝ) 1
  epsilonWork_le : epsilonWork ≤ epsilon

  degree_reserve :
    2 * (((k - 1 : ℕ) : ℝ)) * zeta ≤ t / 4
  cell_error_reserve :
    (((B + 3 : ℕ) : ℝ)) * zeta ≤ t / 8
  bounded_balance_reserve :
    2 * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤
      min alpha (omega / (4 * (R₀ : ℝ))) *
        (eta / (4 * (R₀ : ℝ)))
  bounded_lower_reserve :
    2 * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤
      (eta / (4 * (R₀ : ℝ))) / (2 * (R₀ : ℝ))
  component_delta_reserve :
    (R₀ : ℝ) * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤ delta
  component_eta_reserve :
    (R₀ : ℝ) * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤ eta / 2
  visible_ratio_reserve :
    2 * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤ omega * theta / 2
  density_reserve :
    beta / (subcriticalVisibleScale alpha theta) ^ 2 +
      2 * ((((B + 3 : ℕ) : ℝ)) * zeta) /
        subcriticalVisibleScale alpha theta ≤ delta
  contradiction_reserve :
    2 * epsilonWork + beta < subcriticalPaletteGap k * zeta ^ 2

namespace SubcriticalClosenessParameters

variable {k R₀ : ℕ} {omega eta theta alpha delta epsilon : ℝ}

/-- The total per-cell alignment loss used by downstream statements. -/
def alignmentError
    (P : SubcriticalClosenessParameters k R₀ omega eta theta alpha delta epsilon) :
    ℝ := (((P.B + 3 : ℕ) : ℝ)) * P.zeta

theorem alignmentError_pos
    (P : SubcriticalClosenessParameters k R₀ omega eta theta alpha delta epsilon) :
    0 < P.alignmentError := by
  unfold alignmentError
  positivity [P.zeta_pos]

theorem alignmentError_le_t_div_eight
    (P : SubcriticalClosenessParameters k R₀ omega eta theta alpha delta epsilon) :
    P.alignmentError ≤ P.t / 8 := P.cell_error_reserve

end SubcriticalClosenessParameters

/-! ## Explicit existence -/

set_option maxHeartbeats 800000 in
/-- The complete alignment parameter package is inhabited whenever the six
paper parameters are positive and `R₀ ≥ 1`. -/
theorem exists_subcriticalClosenessParameters
    (k R₀ : ℕ) (hk : 3 ≤ k) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    Nonempty
      (SubcriticalClosenessParameters
        k R₀ omega eta theta alpha delta epsilon) := by
  have hRℝ : 0 < (R₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR₀)
  have hkℝ : 0 < (((k - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  let t := min theta (min 1 (eta / (8 * (R₀ : ℝ) ^ 2)))
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min htheta (lt_min (by norm_num) (by positivity))
  have htTheta : t ≤ theta := by dsimp [t]; exact min_le_left _ _
  have htOne : t ≤ 1 := by
    dsimp [t]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have htEta : t ≤ eta / (8 * (R₀ : ℝ) ^ 2) := by
    dsimp [t]
    exact (min_le_right _ _).trans (min_le_right _ _)

  let B : ℕ := R₀ + Nat.ceil (4 / t)
  have hR₀B : R₀ ≤ B := by dsimp [B]; omega
  have hfourB : 4 / t ≤ (B : ℝ) := by
    calc
      4 / t ≤ (Nat.ceil (4 / t) : ℝ) := Nat.le_ceil _
      _ ≤ (B : ℝ) := by exact_mod_cast (Nat.le_add_left _ R₀)
  have hBthree : 0 < (((B + 3 : ℕ) : ℝ)) := by positivity
  let a := subcriticalVisibleScale alpha theta
  have ha : 0 < a := by dsimp [a, subcriticalVisibleScale]; positivity
  have hminBalance : 0 < min alpha (omega / (4 * (R₀ : ℝ))) := by
    exact lt_min halpha (by positivity)

  let b₁ := t / (8 * (((k - 1 : ℕ) : ℝ)))
  let b₂ := t / (8 * (((B + 3 : ℕ) : ℝ)))
  let b₃ :=
    (min alpha (omega / (4 * (R₀ : ℝ))) *
      (eta / (4 * (R₀ : ℝ)))) /
        (2 * (((B + 3 : ℕ) : ℝ)))
  let b₄ :=
    ((eta / (4 * (R₀ : ℝ))) / (2 * (R₀ : ℝ))) /
      (2 * (((B + 3 : ℕ) : ℝ)))
  let b₅ := delta / ((R₀ : ℝ) * (((B + 3 : ℕ) : ℝ)))
  let b₆ := (eta / 2) / ((R₀ : ℝ) * (((B + 3 : ℕ) : ℝ)))
  let b₇ := (omega * theta / 2) / (2 * (((B + 3 : ℕ) : ℝ)))
  let b₈ := (delta * a / 4) / (((B + 3 : ℕ) : ℝ))
  have hb₁ : 0 < b₁ := by dsimp [b₁]; positivity
  have hb₂ : 0 < b₂ := by dsimp [b₂]; positivity
  have hb₃ : 0 < b₃ := by dsimp [b₃]; positivity
  have hb₄ : 0 < b₄ := by dsimp [b₄]; positivity
  have hb₅ : 0 < b₅ := by dsimp [b₅]; positivity
  have hb₆ : 0 < b₆ := by dsimp [b₆]; positivity
  have hb₇ : 0 < b₇ := by dsimp [b₇]; positivity
  have hb₈ : 0 < b₈ := by dsimp [b₈]; positivity
  let zetaCap := min b₁ (min b₂ (min b₃ (min b₄
    (min b₅ (min b₆ (min b₇ b₈))))))
  have hzetaCap : 0 < zetaCap := by
    dsimp [zetaCap]
    exact lt_min hb₁ (lt_min hb₂ (lt_min hb₃ (lt_min hb₄
      (lt_min hb₅ (lt_min hb₆ (lt_min hb₇ hb₈))))))
  let zeta := zetaCap / 2
  have hzeta : 0 < zeta := by dsimp [zeta]; positivity
  have hzetaLeCap : zeta ≤ zetaCap := by dsimp [zeta]; linarith
  have hzeta₁ : zeta ≤ b₁ := hzetaLeCap.trans (by dsimp [zetaCap]; simp)
  have hzeta₂ : zeta ≤ b₂ := hzetaLeCap.trans (by dsimp [zetaCap]; simp)
  have hzeta₃ : zeta ≤ b₃ := hzetaLeCap.trans (by dsimp [zetaCap]; simp)
  have hzeta₄ : zeta ≤ b₄ := hzetaLeCap.trans (by dsimp [zetaCap]; simp)
  have hzeta₅ : zeta ≤ b₅ := hzetaLeCap.trans (by dsimp [zetaCap]; simp)
  have hzeta₆ : zeta ≤ b₆ := hzetaLeCap.trans (by dsimp [zetaCap]; simp)
  have hzeta₇ : zeta ≤ b₇ := hzetaLeCap.trans (by dsimp [zetaCap]; simp)
  have hzeta₈ : zeta ≤ b₈ := hzetaLeCap.trans (by dsimp [zetaCap]; simp)

  have hdegree : 2 * (((k - 1 : ℕ) : ℝ)) * zeta ≤ t / 4 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) hkℝ)).mp
      (show zeta ≤ t / (8 * (((k - 1 : ℕ) : ℝ))) by exact hzeta₁)
    nlinarith
  have hcell : (((B + 3 : ℕ) : ℝ)) * zeta ≤ t / 8 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) hBthree)).mp
      (show zeta ≤ t / (8 * (((B + 3 : ℕ) : ℝ))) by exact hzeta₂)
    nlinarith
  have hbalance : 2 * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤
      min alpha (omega / (4 * (R₀ : ℝ))) *
        (eta / (4 * (R₀ : ℝ))) := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) hBthree)).mp
      (show zeta ≤ b₃ by exact hzeta₃)
    nlinarith
  have hlower : 2 * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤
      (eta / (4 * (R₀ : ℝ))) / (2 * (R₀ : ℝ)) := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) hBthree)).mp
      (show zeta ≤ b₄ by exact hzeta₄)
    nlinarith
  have hdeltaComp : (R₀ : ℝ) * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤ delta := by
    have h := (le_div_iff₀ (mul_pos hRℝ hBthree)).mp
      (show zeta ≤ b₅ by exact hzeta₅)
    nlinarith
  have hetaComp : (R₀ : ℝ) * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤ eta / 2 := by
    have h := (le_div_iff₀ (mul_pos hRℝ hBthree)).mp
      (show zeta ≤ b₆ by exact hzeta₆)
    nlinarith
  have hvisible : 2 * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤ omega * theta / 2 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num) hBthree)).mp
      (show zeta ≤ b₇ by exact hzeta₇)
    nlinarith
  have herrorDensity : (((B + 3 : ℕ) : ℝ)) * zeta ≤ delta * a / 4 := by
    have h := (le_div_iff₀ hBthree).mp
      (show zeta ≤ b₈ by exact hzeta₈)
    nlinarith

  let palette := subcriticalPaletteGap k
  have hpalette : 0 < palette := by
    dsimp [palette]
    exact subcriticalPaletteGap_pos hk
  let beta := min (delta * a ^ 2 / 4) (palette * zeta ^ 2 / 4)
  have hbeta : 0 < beta := by
    dsimp [beta]
    exact lt_min (by positivity) (by positivity)
  have hbetaDensity : beta ≤ delta * a ^ 2 / 4 := by
    dsimp [beta]
    exact min_le_left _ _
  have hbetaPalette : beta ≤ palette * zeta ^ 2 / 4 := by
    dsimp [beta]
    exact min_le_right _ _
  let epsilonWork := min (epsilon / 2)
    (min (1 / 2) (palette * zeta ^ 2 / 8))
  have heWork : 0 < epsilonWork := by
    dsimp [epsilonWork]
    exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have heWorkOne : epsilonWork < 1 := by
    have hle : epsilonWork ≤ 1 / 2 := by
      dsimp [epsilonWork]
      exact (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have heWorkEpsilon : epsilonWork ≤ epsilon := by
    have hle : epsilonWork ≤ epsilon / 2 := by
      dsimp [epsilonWork]
      exact min_le_left _ _
    linarith
  have heWorkPalette : epsilonWork ≤ palette * zeta ^ 2 / 8 := by
    dsimp [epsilonWork]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hdensity : beta / (subcriticalVisibleScale alpha theta) ^ 2 +
      2 * ((((B + 3 : ℕ) : ℝ)) * zeta) /
        subcriticalVisibleScale alpha theta ≤ delta := by
    have hbetaDiv : beta / a ^ 2 ≤ delta / 4 := by
      apply (div_le_iff₀ (sq_pos_of_pos ha)).2
      calc
        beta ≤ delta * a ^ 2 / 4 := hbetaDensity
        _ = (delta / 4) * a ^ 2 := by ring
    have herrDiv : 2 * ((((B + 3 : ℕ) : ℝ)) * zeta) / a ≤ delta / 2 := by
      apply (div_le_iff₀ ha).2
      calc
        2 * ((((B + 3 : ℕ) : ℝ)) * zeta) ≤ 2 * (delta * a / 4) := by gcongr
        _ = (delta / 2) * a := by ring
    simpa [a] using (show beta / a ^ 2 +
      2 * ((((B + 3 : ℕ) : ℝ)) * zeta) / a ≤ delta by linarith)
  have hcontradiction : 2 * epsilonWork + beta < palette * zeta ^ 2 := by
    have hpos : 0 < palette * zeta ^ 2 := by positivity
    calc
      2 * epsilonWork + beta ≤
          2 * (palette * zeta ^ 2 / 8) + palette * zeta ^ 2 / 4 := by gcongr
      _ = palette * zeta ^ 2 / 2 := by ring
      _ < palette * zeta ^ 2 := by linarith
  exact ⟨{
    t := t
    B := B
    zeta := zeta
    beta := beta
    epsilonWork := epsilonWork
    t_pos := ht
    t_le_theta := htTheta
    t_le_one := htOne
    t_le_eta := htEta
    R₀_le_B := hR₀B
    four_div_t_le_B := hfourB
    zeta_pos := hzeta
    beta_pos := hbeta
    epsilonWork_mem := ⟨heWork, heWorkOne⟩
    epsilonWork_le := heWorkEpsilon
    degree_reserve := hdegree
    cell_error_reserve := hcell
    bounded_balance_reserve := hbalance
    bounded_lower_reserve := hlower
    component_delta_reserve := hdeltaComp
    component_eta_reserve := hetaComp
    visible_ratio_reserve := hvisible
    density_reserve := hdensity
    contradiction_reserve := by simpa [palette] using hcontradiction }⟩

end InducedStars
