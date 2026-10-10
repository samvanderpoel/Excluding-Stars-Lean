import InducedStars.Structure.Supercritical.MediumModels
import Mathlib.Tactic

/-!
# Adjusted densities in the supercritical medium model

The fixed-cardinality comparison removes at most the distinguished witness
from one main part.  This file identifies its Bernoulli parameter with the
edge density on the resulting sampled block and records the elementary
density perturbation and orientation bounds used by the medium-degree
Janson argument.
-/

noncomputable section

open Finset Set

namespace InducedStars

noncomputable local instance mediumDensityDecidableRel
    {n : ℕ} (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

/-! ## The adjusted Bernoulli parameter is a sampled-block density -/

/-- Every tagged coordinate in an adjusted block has Bernoulli parameter
equal to the graph density of that sampled pair.  No division hypothesis is
needed: both definitions use Lean's total real division convention. -/
@[simp] theorem supercriticalMediumBernoulliModel_probability_eq_graphDensity
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (c : (supercriticalMediumFixedModel w).Coordinate) :
    (supercriticalMediumBernoulliModel w).probability c =
      Regularity.graphDensity G
        (supercriticalMediumSampledPart w c.1.left)
        (supercriticalMediumSampledPart w c.1.right) := by
  rcases c with ⟨e, xy⟩
  simp only [supercriticalMediumBernoulliModel]
  rw [DenseGraph.FixedCardinalityBlockModel.associatedBernoulli_probability]
  simp only [supercriticalMediumFixedModel,
    DenseGraph.FixedCardinalityBlockModel.quotaParameter,
    supercriticalMediumAdjustedQuota,
    card_supercriticalMediumCrossBlock,
    Regularity.graphDensity_eq]
  rw [Nat.cast_mul]

/-! ## Removing the distinguished witness changes little density -/

/-- Every sampled main part retains a `1 - δ / 2` proportion once its
original part is large enough that `δ |V_i| ≥ 2`.  The proof includes both
the unchanged case and the sole possible one-vertex deletion. -/
theorem supercriticalMediumSampledPart_card_lower
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α δ : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (hδ : 0 ≤ δ)
    (hlarge : ∀ i : Fin (k - 1),
      2 ≤ δ * ((D.parts i).card : ℝ))
    (i : Fin (k - 1)) :
    (1 - δ / 2) * ((D.parts i).card : ℝ) ≤
      ((supercriticalMediumSampledPart w i).card : ℝ) := by
  classical
  by_cases hi : i = w.part
  · subst i
    by_cases hv : w.vertex ∈ D.parts w.part
    · have hcardPos : 0 < (D.parts w.part).card :=
        (D.parts_nonempty w.part).card_pos
      have hcast :
          (((D.parts w.part).card - 1 : ℕ) : ℝ) =
            ((D.parts w.part).card : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ (D.parts w.part).card)]
        norm_num
      rw [supercriticalMediumSampledPart_distinguished, if_pos hv,
        Finset.card_erase_of_mem hv, hcast]
      have h := hlarge w.part
      nlinarith
    · rw [supercriticalMediumSampledPart_distinguished, if_neg hv]
      have hcardNonneg : 0 ≤ ((D.parts w.part).card : ℝ) := by positivity
      nlinarith
  · rw [supercriticalMediumSampledPart_of_ne w hi]
    have hcardNonneg : 0 ≤ ((D.parts i).card : ℝ) := by positivity
    nlinarith

/-- The direct size condition above follows from a balanced-part lower bound
and the natural `n`-threshold `4(k-1) ≤ δ n`. -/
theorem two_le_delta_mul_partCard_of_balanced
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)} {δ : ℝ}
    (hk : 3 ≤ k) (hδ : 0 < δ)
    (hbalanced : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ))
    (hn : 4 * ((k - 1 : ℕ) : ℝ) ≤ δ * (n : ℝ)) :
    ∀ i : Fin (k - 1), 2 ≤ δ * ((D.parts i).card : ℝ) := by
  intro i
  have hr : 0 < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hfraction :
      2 ≤ δ * ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) := by
    rw [show δ * ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) =
        (δ * (n : ℝ)) / (2 * ((k - 1 : ℕ) : ℝ)) by ring]
    exact (le_div_iff₀ (mul_pos (by norm_num) hr)).2 (by nlinarith)
  exact hfraction.trans
    (mul_le_mul_of_nonneg_left (hbalanced i) hδ.le)

/-- The usual absolute-error formulation of balancedness implies the
half-average lower bound used above. -/
theorem half_average_le_partCard_of_abs_close
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)} {ζ : ℝ}
    (hk : 3 ≤ k)
    (hζ : ζ ≤ 1 / (2 * ((k - 1 : ℕ) : ℝ)))
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ ζ * (n : ℝ)) :
    ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ) := by
  intro i
  have hr : 0 < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hscaled := mul_le_mul_of_nonneg_right hζ
    (show 0 ≤ (n : ℝ) by positivity)
  have hlower := (abs_le.mp (hclose i)).1
  have hid :
      (n : ℝ) / ((k - 1 : ℕ) : ℝ) -
          (1 / (2 * ((k - 1 : ℕ) : ℝ))) * (n : ℝ) =
        (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) := by
    field_simp
    ring
  rw [← hid]
  linarith

/-- Removing at most the witness from the two sides of a cross block changes
its density by at most `δ`. -/
theorem supercriticalMediumSampled_density_sub_full_le
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α δ : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (hδ : 0 ≤ δ)
    (hlarge : ∀ i : Fin (k - 1),
      2 ≤ δ * ((D.parts i).card : ℝ))
    (e : SupercriticalPartPair k) :
    |Regularity.graphDensity G
          (supercriticalMediumSampledPart w e.left)
          (supercriticalMediumSampledPart w e.right) -
        Regularity.graphDensity G (D.parts e.left) (D.parts e.right)| ≤ δ := by
  have hperturb := Regularity.abs_graphDensity_sub_graphDensity_le_two_mul
    G (supercriticalMediumSampledPart_subset w e.left)
      (supercriticalMediumSampledPart_subset w e.right)
      (show 0 ≤ δ / 2 by positivity)
      (supercriticalMediumSampledPart_card_lower w hδ hlarge e.left)
      (supercriticalMediumSampledPart_card_lower w hδ hlarge e.right)
  convert hperturb using 1 <;> ring

/-- If every full cross pair is within `δ` of `ρ`, every adjusted
Bernoulli parameter is within `2δ` of `ρ`. -/
theorem supercriticalMediumBernoulliModel_probability_close
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α δ ρ : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (hδ : 0 ≤ δ)
    (hlarge : ∀ i : Fin (k - 1),
      2 ≤ δ * ((D.parts i).card : ℝ))
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) - ρ| ≤ δ)
    (c : (supercriticalMediumFixedModel w).Coordinate) :
    |(supercriticalMediumBernoulliModel w).probability c - ρ| ≤ 2 * δ := by
  rw [supercriticalMediumBernoulliModel_probability_eq_graphDensity]
  calc
    |Regularity.graphDensity G
          (supercriticalMediumSampledPart w c.1.left)
          (supercriticalMediumSampledPart w c.1.right) - ρ| ≤
        |Regularity.graphDensity G
            (supercriticalMediumSampledPart w c.1.left)
            (supercriticalMediumSampledPart w c.1.right) -
          Regularity.graphDensity G (D.parts c.1.left) (D.parts c.1.right)| +
        |Regularity.graphDensity G (D.parts c.1.left) (D.parts c.1.right) - ρ| :=
      abs_sub_le _ _ _
    _ ≤ δ + δ := add_le_add
      (supercriticalMediumSampled_density_sub_full_le w hδ hlarge c.1)
      (hfull c.1)
    _ = 2 * δ := by ring

/-- Balanced parts and the explicit linear threshold imply the adjusted
`2δ`-density band without an intermediate size hypothesis. -/
theorem supercriticalMediumBernoulliModel_probability_close_of_balanced
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α δ ρ : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (hk : 3 ≤ k) (w : SupercriticalMediumWitness G α D)
    (hδ : 0 < δ)
    (hbalanced : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ))
    (hn : 4 * ((k - 1 : ℕ) : ℝ) ≤ δ * (n : ℝ))
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) - ρ| ≤ δ)
    (c : (supercriticalMediumFixedModel w).Coordinate) :
    |(supercriticalMediumBernoulliModel w).probability c - ρ| ≤ 2 * δ :=
  supercriticalMediumBernoulliModel_probability_close w hδ.le
    (two_le_delta_mul_partCard_of_balanced hk hδ hbalanced hn) hfull c

/-! ## The single global orientation and its uniform floor -/

/-- Pull the global success orientation back to one tagged block
coordinate.  This is one predicate on the entire coordinate space, not a
candidate-dependent orientation. -/
def supercriticalMediumTaggedSuccessPresent
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (c : (supercriticalMediumFixedModel w).Coordinate) : Prop :=
  mediumSuccessPresent w s(c.2.1.1, c.2.1.2)

/-- Success probability of a tagged coordinate after applying the one
global complementation. -/
noncomputable def supercriticalMediumOrientedCoordinateProbability
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (c : (supercriticalMediumFixedModel w).Coordinate) : ℝ :=
  by
    classical
    exact if supercriticalMediumTaggedSuccessPresent w c then
      (supercriticalMediumBernoulliModel w).probability c
    else 1 - (supercriticalMediumBernoulliModel w).probability c

@[simp] theorem supercriticalMediumOrientedCoordinateProbability_of_present
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (c : (supercriticalMediumFixedModel w).Coordinate)
    (hc : supercriticalMediumTaggedSuccessPresent w c) :
    supercriticalMediumOrientedCoordinateProbability w c =
      (supercriticalMediumBernoulliModel w).probability c := by
  classical
  simp [supercriticalMediumOrientedCoordinateProbability, hc]

@[simp] theorem supercriticalMediumOrientedCoordinateProbability_of_absent
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (c : (supercriticalMediumFixedModel w).Coordinate)
    (hc : ¬supercriticalMediumTaggedSuccessPresent w c) :
    supercriticalMediumOrientedCoordinateProbability w c =
      1 - (supercriticalMediumBernoulliModel w).probability c := by
  classical
  simp [supercriticalMediumOrientedCoordinateProbability, hc]

/-- A scalar within error `η` of the supercritical off-diagonal density has
both oriented outcomes above the half-minimum floor whenever `η` is at most
that floor.  This formulation exposes the exact constant needed downstream. -/
theorem mediumSuccessProbabilityFloor_le_if_of_close
    {k : ℕ} {γ q η : ℝ}
    (hq : |q - supercriticalOffDiagonal k γ| ≤ η)
    (hη : η ≤
      min (supercriticalOffDiagonal k γ)
        (1 - supercriticalOffDiagonal k γ) / 2)
    (successPresent : Prop) [Decidable successPresent] :
    mediumSuccessProbabilityFloor k γ ≤
      if successPresent then q else 1 - q := by
  rw [abs_le] at hq
  by_cases hs : successPresent
  · rw [if_pos hs]
    unfold mediumSuccessProbabilityFloor
    have hmin := min_le_left (supercriticalOffDiagonal k γ)
      (1 - supercriticalOffDiagonal k γ)
    nlinarith
  · rw [if_neg hs]
    unfold mediumSuccessProbabilityFloor
    have hmin := min_le_right (supercriticalOffDiagonal k γ)
      (1 - supercriticalOffDiagonal k γ)
    nlinarith

/-- In particular, an adjusted parameter within `δ` has the desired floor
under the explicit smallness condition `δ < min(ρ,1-ρ)/2`. -/
theorem mediumSuccessProbabilityFloor_le_if_of_close_lt_half_min
    {k : ℕ} {γ q δ : ℝ}
    (hq : |q - supercriticalOffDiagonal k γ| ≤ δ)
    (hδ : δ <
      min (supercriticalOffDiagonal k γ)
        (1 - supercriticalOffDiagonal k γ) / 2)
    (successPresent : Prop) [Decidable successPresent] :
    mediumSuccessProbabilityFloor k γ ≤
      if successPresent then q else 1 - q :=
  mediumSuccessProbabilityFloor_le_if_of_close hq hδ.le successPresent

/-- The concrete adjusted model therefore has a uniform oriented success
floor.  Since its error is `2δ`, the exact hypothesis is that `2δ` is below
half of `min(ρ,1-ρ)`.  The proof is valid at `γ = gammaK k`; it uses only
the closed endpoint density estimate, not strict supercriticality. -/
theorem supercriticalMediumOrientedCoordinateProbability_lower
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α δ γ : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (hδ : 0 ≤ δ)
    (hlarge : ∀ i : Fin (k - 1),
      2 ≤ δ * ((D.parts i).card : ℝ))
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) -
        supercriticalOffDiagonal k γ| ≤ δ)
    (hsmall : 2 * δ <
      min (supercriticalOffDiagonal k γ)
        (1 - supercriticalOffDiagonal k γ) / 2)
    (c : (supercriticalMediumFixedModel w).Coordinate) :
    mediumSuccessProbabilityFloor k γ ≤
      supercriticalMediumOrientedCoordinateProbability w c := by
  classical
  unfold supercriticalMediumOrientedCoordinateProbability
  exact mediumSuccessProbabilityFloor_le_if_of_close_lt_half_min
    (supercriticalMediumBernoulliModel_probability_close
      w hδ hlarge hfull c)
    hsmall (supercriticalMediumTaggedSuccessPresent w c)

/-- Balanced-part convenience form of the globally oriented probability
floor, again including the phase-boundary endpoint. -/
theorem supercriticalMediumOrientedCoordinateProbability_lower_of_balanced
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α δ γ : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (hk : 3 ≤ k) (w : SupercriticalMediumWitness G α D)
    (hδ : 0 < δ)
    (hbalanced : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ))
    (hn : 4 * ((k - 1 : ℕ) : ℝ) ≤ δ * (n : ℝ))
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) -
        supercriticalOffDiagonal k γ| ≤ δ)
    (hsmall : 2 * δ <
      min (supercriticalOffDiagonal k γ)
        (1 - supercriticalOffDiagonal k γ) / 2)
    (c : (supercriticalMediumFixedModel w).Coordinate) :
    mediumSuccessProbabilityFloor k γ ≤
      supercriticalMediumOrientedCoordinateProbability w c :=
  supercriticalMediumOrientedCoordinateProbability_lower w hδ.le
    (two_le_delta_mul_partCard_of_balanced hk hδ hbalanced hn)
    hfull hsmall c

end InducedStars
