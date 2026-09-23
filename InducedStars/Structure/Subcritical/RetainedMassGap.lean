import InducedStars.Structure.Subcritical.RetainedMassNearEquality
import InducedStars.Structure.Subcritical.RetainedMassAlignment
import InducedStars.Structure.Subcritical.RetainedMassCompatibility
import InducedStars.Structure.Subcritical.RetainedKeyFamilies

/-!
# Retained mass gap away from the distinguished subcritical candidate

Paper: Lemma `lemma:sub-retained-mass-gap-K1k`.
The proof controls omitted normalized
quadratic mass outside the retained set, never its total vertex length.
The positive separation modulus is chosen before the candidate and division.
-/

noncomputable section
open Set
namespace InducedStars

/-- A uniform positive retained-length gap for every candidate separated
from the distinguished one-block optimizer. No false linear modulus or
bound on the total length of unretained blocks is asserted. -/
theorem subcriticalCandidateRetainedMassGap
    (k : ℕ) (hk : 3 ≤ k) {gamma separation : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hsep : 0 < separation) :
    ∃ gap : ℝ, 0 < gap ∧ gap < 1 ∧
      ∀ (eta : ℝ) (R₀ : ℕ), 0 < eta → eta ≤ gap / 4 → Nat.ceil (2 / gap) ≤ R₀ →
      ∀ L : AdmissibleBlockSequence k, IsSubcriticalCandidate k gamma L →
        separation ≤ cutDist (WLambda hk L)
          (subcriticalDistinguishedGraphon k hk gamma hgamma) →
        subcriticalOneBlockLength k gamma + gap < subcriticalRetainedBlockLength L eta R₀ := by
  let mu := subcriticalOneBlockLength k gamma
  have hmu : 0 < mu := subcriticalOneBlockLength_pos hk hgamma.1
  have hmuOne : mu ≤ 1 := (subcriticalOneBlockLength_lt_one hk hgamma.2).le
  obtain ⟨t, ht, htOne, hsmall, horder, herror⟩ :=
    exists_subcriticalRetainedMassTolerance hk hmu hsep
  refine ⟨t, ht, htOne, ?_⟩
  intro eta R₀ heta hetaSmall hR L hL hdist
  by_contra hlength
  have hlength' : subcriticalRetainedBlockLength L eta R₀ ≤ mu + t := le_of_not_gt hlength
  have hmass : L.mass = mu ^ 2 / (k - 1 : ℕ) := by
    simpa only [blockSequenceMass_eq_mass] using hL.mass_eq_oneBlockLength_sq hk hgamma
  obtain ⟨j, hj, hcore, herr⟩ := subcriticalRetainedMass_nearEquality_complete hk L
    heta hmu ht hmass hetaSmall hR hsmall horder hlength'
  have hB : 0 ≤ subcriticalRetainedMassLengthError k mu t := by
    unfold subcriticalRetainedMassLengthError
    positivity
  have halign := cutDist_WLambda_subcriticalDistinguished_le hk gamma hgamma L j hj hcore
  have hbudget := subcriticalCompleteBlock_alignmentBudget_le hk L hmu.le hmuOne
    hB hmass hcore herr
  exact (not_lt_of_ge hdist) ((halign.trans hbudget).trans_lt herror)

/-- Finite compatible divisions of a separated candidate must retain a
strictly larger linear support than the distinguished candidate. This is
the paper-facing retained-mass gap, with all parameter reserves explicit. -/
theorem subcriticalRetainedMassGap
    (k : ℕ) (hk : 3 ≤ k) {gamma separation : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hsep : 0 < separation) :
    ∃ gap : ℝ, 0 < gap ∧ gap < 1 ∧
      ∀ (eta delta : ℝ) (R₀ : ℕ),
        0 < eta → eta ≤ gap / 4 → Nat.ceil (2 / gap) ≤ R₀ →
        0 ≤ delta → delta ≤ eta → delta ≤ eta * gap →
      ∀ (L : AdmissibleBlockSequence k), IsSubcriticalCandidate k gamma L →
        separation ≤ cutDist (WLambda hk L)
          (subcriticalDistinguishedGraphon k hk gamma hgamma) →
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (D : SubcriticalDivision k V),
        D.CandidateCompatibility L eta delta R₀ →
        (subcriticalOneBlockLength k gamma + gap / 2) * Fintype.card V ≤
          (D.retainedVertices eta R₀).card := by
  obtain ⟨gap, hgap, hgapOne, hlength⟩ :=
    subcriticalCandidateRetainedMassGap k hk hgamma hsep
  refine ⟨gap, hgap, hgapOne, ?_⟩
  intro eta delta R₀ heta hetaSmall hR hdelta0 hdelta hreserve L hL hdist V _ _ D C
  exact C.retained_mass_gap heta hdelta0 hdelta hreserve
    (hlength eta R₀ heta hetaSmall hR L hL hdist).le

/-- The retained-key version forgets the entire nonretained completion.
Every key in the compatible image has the same uniform support gain. -/
theorem subcriticalCompatibleRetainedKeyMassGap
    (k : ℕ) (hk : 3 ≤ k) {gamma separation : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hsep : 0 < separation) :
    ∃ gap : ℝ, 0 < gap ∧ gap < 1 ∧
      ∀ (eta delta : ℝ) (R₀ : ℕ),
        0 < eta → eta ≤ gap / 4 → Nat.ceil (2 / gap) ≤ R₀ →
        0 ≤ delta → delta ≤ eta → delta ≤ eta * gap →
      ∀ (L : AdmissibleBlockSequence k), IsSubcriticalCandidate k gamma L →
        separation ≤ cutDist (WLambda hk L)
          (subcriticalDistinguishedGraphon k hk gamma hgamma) →
      ∀ (n : ℕ) (K : SubcriticalRetainedKey k (Fin n)),
        K ∈ compatibleRetainedKeys k n L eta delta R₀ →
        (subcriticalOneBlockLength k gamma + gap / 2) * n ≤ K.support.card := by
  classical
  obtain ⟨gap, hgap, hgapOne, hmain⟩ := subcriticalRetainedMassGap k hk hgamma hsep
  refine ⟨gap, hgap, hgapOne, ?_⟩
  intro eta delta R₀ heta hetaSmall hR hdelta0 hdelta hreserve L hL hdist n K hK
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hK
  have hC := ((mem_subcriticalCompatibleDivisions D).mp hD).2
  rw [retainedKey_support]
  simpa only [Fintype.card_fin] using
    hmain eta delta R₀ heta hetaSmall hR hdelta0 hdelta hreserve L hL hdist (Fin n) D hC.some

end InducedStars
