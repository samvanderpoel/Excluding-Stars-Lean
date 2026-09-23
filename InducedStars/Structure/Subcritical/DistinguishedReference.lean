import InducedStars.Graphon.EntropyUpperBound

/-!
# The distinguished subcritical one-block optimizer

The paper's subcritical W* has a single complete regular core and a zero
remainder. This separate name does not extend or alter the existing Wstar,
whose density domain is the critical and supercritical interval.
-/

noncomputable section
open Set
namespace InducedStars

/-- The existing one-block length is exactly sqrt(gamma/gammaK), with
the finite-star normalization unchanged. -/
theorem subcriticalOneBlockLength_eq_sqrt_div_gammaK
    {k : ℕ} (hk : 3 ≤ k) (gamma : ℝ) :
    subcriticalOneBlockLength k gamma = Real.sqrt (gamma / gammaK k) := by
  unfold subcriticalOneBlockLength gammaK
  congr 1
  rw [div_div_eq_mul_div]
  congr 1
  ring

/-- Explicit complete-core candidate representation of the distinguished
subcritical optimizer. Only block zero has positive length. -/
def subcriticalDistinguishedBlockSequence (k : ℕ) (hk : 3 ≤ k)
    (gamma : ℝ) (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    AdmissibleBlockSequence k :=
  oneBlockSequence k hk (subcriticalOneBlockLength k gamma)
    (subcriticalOneBlockLength_pos hk hgamma.1)
    (subcriticalOneBlockLength_lt_one hk hgamma.2).le

/-- The paper's W* in the subcritical chapter, not the historical Wstar. -/
def subcriticalDistinguishedGraphon (k : ℕ) (hk : 3 ≤ k)
    (gamma : ℝ) (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) : Graphon :=
  WLambda hk (subcriticalDistinguishedBlockSequence k hk gamma hgamma)

theorem subcriticalDistinguishedBlockSequence_isCandidate
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    IsSubcriticalCandidate k gamma (subcriticalDistinguishedBlockSequence k hk gamma hgamma) :=
  subcriticalOneBlockSequence_isCandidate hk hgamma.1 hgamma.2

@[simp] theorem subcriticalDistinguishedBlockSequence_alpha
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (i : ℕ) :
    (subcriticalDistinguishedBlockSequence k hk gamma hgamma).alpha i =
      if i = 0 then subcriticalOneBlockLength k gamma else 0 := rfl

@[simp] theorem subcriticalDistinguishedBlockSequence_core
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (i : ℕ) :
    (subcriticalDistinguishedBlockSequence k hk gamma hgamma).core i =
      RegularBlockCore.complete k hk := rfl

theorem subcriticalDistinguishedGraphon_mem_candidateOptimizerFamily
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    subcriticalDistinguishedGraphon k hk gamma hgamma ∈ candidateOptimizerFamily k gamma := by
  rw [candidateOptimizerFamily_of_lt hk
    ⟨hgamma.1, hgamma.2.trans (gammaK_lt_one hk)⟩ hgamma.2]
  exact ⟨_, subcriticalDistinguishedBlockSequence_isCandidate k hk gamma hgamma, rfl⟩

theorem subcriticalDistinguishedGraphon_mem_fixedDensityOptimizers
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    subcriticalDistinguishedGraphon k hk gamma hgamma ∈ fixedDensityOptimizers k gamma :=
  candidate_mem_fixedDensityOptimizers k hk gamma
    ⟨hgamma.1, hgamma.2.trans (gammaK_lt_one hk)⟩
    (subcriticalDistinguishedGraphon_mem_candidateOptimizerFamily k hk gamma hgamma)

theorem subcriticalDistinguishedGraphon_edgeDensity
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    graphonEdgeDensity (subcriticalDistinguishedGraphon k hk gamma hgamma) = gamma :=
  graphonEdgeDensity_WLambda_of_isSubcriticalCandidate hk
    (subcriticalDistinguishedBlockSequence_isCandidate k hk gamma hgamma)

theorem subcriticalDistinguishedGraphon_entropy
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    graphonEntropy (subcriticalDistinguishedGraphon k hk gamma hgamma) = entropyDensity k gamma :=
  graphonEntropy_WLambda_of_isSubcriticalCandidate hk hgamma.2
    (subcriticalDistinguishedBlockSequence_isCandidate k hk gamma hgamma)

/-- Exact quadratic mass identity underlying the retained-mass comparison;
it makes no claim about the total length of omitted blocks. -/
theorem IsSubcriticalCandidate.mass_eq_oneBlockLength_sq
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    {L : AdmissibleBlockSequence k} (hL : IsSubcriticalCandidate k gamma L) :
    blockSequenceMass L = subcriticalOneBlockLength k gamma ^ 2 / (k - 1 : ℕ) := by
  have hsingle := subcriticalDistinguishedBlockSequence_isCandidate k hk gamma hgamma
  change blockSequenceMass L = _ at hL
  change blockSequenceMass (subcriticalDistinguishedBlockSequence k hk gamma hgamma) = _ at hsingle
  rw [hL, ← hsingle]
  exact blockSequenceMass_oneBlockSequence k hk _ _ _

end InducedStars
