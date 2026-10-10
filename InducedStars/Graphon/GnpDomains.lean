import InducedStars.Asymptotics.FixedDensityTransfer
import InducedStars.Graphon.RelativeEntropy

/-!
# Variational domains for induced-free `G(n,p)` transfer

This module records the full induced-free graphon domain and its
positive-random subdomain.  The project uses positive binary relative entropy,
so the corresponding probability exponent is the negative of the infimum
defined here.
-/

noncomputable section

open Set

namespace InducedStars

/-- Graphons with zero induced density of `H`. -/
def inducedFreeGraphons {h : ℕ}
    (H : SimpleGraph (Fin h)) : Set Graphon :=
  {W | graphonInducedDensity H W = 0}

@[simp] theorem mem_inducedFreeGraphons {h : ℕ}
    {H : SimpleGraph (Fin h)} {W : Graphon} :
    W ∈ inducedFreeGraphons H ↔ graphonInducedDensity H W = 0 :=
  Iff.rfl

/-- Induced-`H`-free graphons with a genuinely random region of positive
measure. -/
def positiveRandomInducedFreeGraphons {h : ℕ}
    (H : SimpleGraph (Fin h)) : Set Graphon :=
  {W | graphonInducedDensity H W = 0 ∧ 0 < graphonRandomMass W}

@[simp] theorem mem_positiveRandomInducedFreeGraphons {h : ℕ}
    {H : SimpleGraph (Fin h)} {W : Graphon} :
    W ∈ positiveRandomInducedFreeGraphons H ↔
      graphonInducedDensity H W = 0 ∧ 0 < graphonRandomMass W :=
  Iff.rfl

/-- The closed fixed-density induced-free domain.  Unlike
`positiveRandomFixedDensityGraphons`, this includes deterministic graphons. -/
def inducedFreeFixedDensityGraphons {h : ℕ}
    (H : SimpleGraph (Fin h)) (γ : ℝ) : Set Graphon :=
  {W | graphonEdgeDensity W = γ ∧ graphonInducedDensity H W = 0}

@[simp] theorem mem_inducedFreeFixedDensityGraphons {h : ℕ}
    {H : SimpleGraph (Fin h)} {γ : ℝ} {W : Graphon} :
    W ∈ inducedFreeFixedDensityGraphons H γ ↔
      graphonEdgeDensity W = γ ∧ graphonInducedDensity H W = 0 :=
  Iff.rfl

theorem positiveRandomInducedFreeGraphons_subset {h : ℕ}
    (H : SimpleGraph (Fin h)) :
    positiveRandomInducedFreeGraphons H ⊆ inducedFreeGraphons H := by
  intro W hW
  exact hW.1

/-- The positive-KL infimum over all induced-`H`-free graphons. -/
noncomputable def inducedFreeGraphonRateValue {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ) : ℝ :=
  sInf (graphonRelativeEntropy p '' inducedFreeGraphons H)

/-- The positive-KL infimum over the positive-random induced-free domain. -/
noncomputable def positiveRandomInducedFreeRateValue {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ) : ℝ :=
  sInf (graphonRelativeEntropy p '' positiveRandomInducedFreeGraphons H)

/-- Entropy supremum over the full (closed) fixed-density induced-free
domain. -/
noncomputable def inducedFreeFixedDensityEntropyValue {h : ℕ}
    (H : SimpleGraph (Fin h)) (γ : ℝ) : ℝ :=
  sSup (graphonEntropy '' inducedFreeFixedDensityGraphons H γ)

/-- Entropy of any nonempty graphon family contained in the closed
fixed-density induced-free domain is bounded by the full-domain value. -/
theorem graphonEntropy_sSup_le_inducedFreeFixedDensityEntropyValue
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ) (S : Set Graphon)
    (hne : S.Nonempty) (hS : S ⊆ inducedFreeFixedDensityGraphons H γ) :
    sSup (graphonEntropy '' S) ≤
      inducedFreeFixedDensityEntropyValue H γ := by
  apply csSup_le (hne.image graphonEntropy)
  rintro z ⟨W, hW, rfl⟩
  exact le_csSup (bddAbove_graphonEntropy_image _)
    ⟨W, hS hW, rfl⟩

/-- Whenever the positive-random fixed-density domain is nonempty, its
entropy value equals the entropy supremum over the full closed domain. -/
theorem inducedFreeFixedDensityEntropyValue_eq_positiveRandom
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ)
    (hne : (positiveRandomFixedDensityGraphons H γ).Nonempty) :
    inducedFreeFixedDensityEntropyValue H γ =
      positiveRandomFixedDensityEntropyValue H γ := by
  exact graphonEntropy_sSup_limitSet_eq_positiveRandom H γ
    (inducedFreeFixedDensityGraphons H γ) hne
    (by
      rintro W ⟨hedge, hfree, _hrandom⟩
      exact ⟨hedge, hfree⟩)
    (by
      intro W hW
      exact hW)

theorem inducedFreeGraphonRateValues_bddBelow {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    BddBelow (graphonRelativeEntropy p '' inducedFreeGraphons H) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨W, _hW, rfl⟩
  exact graphonRelativeEntropy_nonneg hp W

theorem positiveRandomInducedFreeRateValues_bddBelow {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    BddBelow
      (graphonRelativeEntropy p '' positiveRandomInducedFreeGraphons H) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨W, _hW, rfl⟩
  exact graphonRelativeEntropy_nonneg hp W

theorem inducedFreeGraphonRateValues_nonempty {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ)
    (hne : (inducedFreeGraphons H).Nonempty) :
    (graphonRelativeEntropy p '' inducedFreeGraphons H).Nonempty :=
  hne.image (graphonRelativeEntropy p)

theorem positiveRandomInducedFreeRateValues_nonempty {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ)
    (hne : (positiveRandomInducedFreeGraphons H).Nonempty) :
    (graphonRelativeEntropy p ''
      positiveRandomInducedFreeGraphons H).Nonempty :=
  hne.image (graphonRelativeEntropy p)

theorem inducedFreeGraphonRateValue_nonneg {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hne : (inducedFreeGraphons H).Nonempty) :
    0 ≤ inducedFreeGraphonRateValue H p := by
  apply le_csInf (inducedFreeGraphonRateValues_nonempty H p hne)
  rintro _ ⟨W, _hW, rfl⟩
  exact graphonRelativeEntropy_nonneg hp W

theorem positiveRandomInducedFreeRateValue_nonneg {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hne : (positiveRandomInducedFreeGraphons H).Nonempty) :
    0 ≤ positiveRandomInducedFreeRateValue H p := by
  apply le_csInf (positiveRandomInducedFreeRateValues_nonempty H p hne)
  rintro _ ⟨W, _hW, rfl⟩
  exact graphonRelativeEntropy_nonneg hp W

theorem inducedFreeGraphonRateValue_le {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ inducedFreeGraphons H) :
    inducedFreeGraphonRateValue H p ≤ graphonRelativeEntropy p W := by
  exact csInf_le (inducedFreeGraphonRateValues_bddBelow H p hp)
    ⟨W, hW, rfl⟩

theorem positiveRandomInducedFreeRateValue_le {h : ℕ}
    (H : SimpleGraph (Fin h)) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ positiveRandomInducedFreeGraphons H) :
    positiveRandomInducedFreeRateValue H p ≤
      graphonRelativeEntropy p W := by
  exact csInf_le (positiveRandomInducedFreeRateValues_bddBelow H p hp)
    ⟨W, hW, rfl⟩

/-- Positive random mass rules out both endpoint edge densities. -/
theorem graphonEdgeDensity_mem_Ioo_of_randomMass_pos
    (W : Graphon) (hrandom : 0 < graphonRandomMass W) :
    graphonEdgeDensity W ∈ Ioo (0 : ℝ) 1 := by
  have hentropy : 0 < graphonEntropy W :=
    graphonEntropy_pos_of_graphonRandomMass_pos W hrandom
  have hcc := graphonEdgeDensity_mem_Icc W
  constructor
  · apply lt_of_le_of_ne hcc.1
    intro hzero
    have hW : W = zeroGraphon :=
      (graphonEdgeDensity_eq_zero_iff W).mp hzero.symm
    rw [hW, graphonEntropy_zero] at hentropy
    exact hentropy.false
  · apply lt_of_le_of_ne hcc.2
    intro hone
    have hW : W = oneGraphon :=
      (graphonEdgeDensity_eq_one_iff W).mp hone
    rw [hW, graphonEntropy_one] at hentropy
    exact hentropy.false

/-- The general full-domain value specializes definitionally to the existing
induced-star variational value. -/
theorem inducedFreeGraphonRateValue_inducedStar_eq
    (k : ℕ) (p : ℝ) :
    inducedFreeGraphonRateValue (inducedStar k) p =
      gnpGraphonVariationalValue k p := by
  rfl

end InducedStars
