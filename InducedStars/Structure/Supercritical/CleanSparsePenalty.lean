import InducedStars.Structure.Supercritical.CleanSparseEncoding
import InducedStars.Structure.Supercritical.CleanSparseBounds
import InducedStars.Structure.Supercritical.Closeness
import Mathlib.Tactic

/-!
# The supercritical clean sparse-set penalty

The finite theorem in this file combines the exact clean-fiber encoding with
the cross-cell capacity gained by absorbing the sparse set into a smallest
main part.  The arbitrary graph on the sparse set costs only a quadratic
entropy term, which is absorbed into half of that gain.  The paper-facing
wrapper obtains the required geometry from the synchronized close-structure
theorem.
-/

noncomputable section

open Finset Set

namespace InducedStars

/-! ## Finite clean sparse-set penalty -/

/-- The clean sparse-set penalty under the explicit geometric conclusions of
close structure.  This is the finite core of `superFStar`; in particular, it
uses no project-specific axiom.  The feasibility hypothesis on `t` is retained
in the interface because it is part of the paper's profile range, although the
exact encoding makes infeasible fibers empty automatically. -/
theorem supercriticalCleanSparsePenalty_of_geometry
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdeltaSmall : delta < supercriticalSparseDeltaBound k gamma)
    {m t : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n))
    (_hsparseNonempty : D.sparse.Nonempty)
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2)
    (profile : SupercriticalEdgeProfile D)
    (hdensity : ∀ e,
      supercriticalOffDiagonal k gamma - delta ≤
          profileDensity profile e ∧
        profileDensity profile e ≤
          supercriticalOffDiagonal k gamma + delta)
    (hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) delta (t : ℤ) profile)
    (_ht : t ≤ Nat.choose D.sparse.card 2) :
    ((supercriticalCleanDivisionProfileGraphFinset
        k hk gamma ⟨le_of_lt hgamma.1, hgamma.2⟩
        m n tau hn D profile).card : ℝ) ≤
      (supercriticalProfileMultiplicity
          (supercriticalAbsorbSparseProfile hk D profile) : ℝ) *
        Real.exp (-(supercriticalSparsePenaltyConstant k gamma *
          (D.sparse.card : ℝ) * (n : ℝ))) := by
  obtain ⟨hdeltaRho, hdeltaBalance, hdeltaEntropy⟩ :=
    supercriticalSparseDeltaBound_spec hdeltaSmall
  have hcapacity := supercriticalSparseCapacityExponent_lower
    hk hgamma D profile hdelta0 hdeltaRho.le hdeltaBalance.le hbalanced
      (fun e ↦ (hdensity e).1)
  have hmultiplicity :=
    supercriticalProfileMultiplicity_le_absorbed_mul_exp hk D profile
  have hentropy := two_pow_choose_two_le_exp_sparsePenalty
    D hdelta0 hdeltaEntropy.le hsparse
  have hencodingNat :=
    card_supercriticalCleanDivisionProfileGraphFinset_le_mul_two_pow
      (hk := hk) (hgamma := ⟨le_of_lt hgamma.1, hgamma.2⟩)
      (tau := tau) (hn := hn) hprofile
  have hencoding :
      ((supercriticalCleanDivisionProfileGraphFinset
          k hk gamma ⟨le_of_lt hgamma.1, hgamma.2⟩
          m n tau hn D profile).card : ℝ) ≤
        (supercriticalProfileMultiplicity profile : ℝ) *
          (2 : ℝ) ^ Nat.choose D.sparse.card 2 := by
    exact_mod_cast hencodingNat
  let cCap := supercriticalSparseCapacityConstant k gamma
  let nu := supercriticalSparsePenaltyConstant k gamma
  let X := (D.sparse.card : ℝ) /
      ((D.parts (supercriticalSmallestPartIndex hk D)).card +
        D.sparse.card : ℕ) *
      (supercriticalIncidentProfileCount hk D profile : ℝ)
  let MStar : ℝ := supercriticalProfileMultiplicity
    (supercriticalAbsorbSparseProfile hk D profile)
  have hcapacity' : cCap * (D.sparse.card : ℝ) * n ≤ X := by
    simpa [cCap, X] using hcapacity
  have hmultiplicity' :
      (supercriticalProfileMultiplicity profile : ℝ) ≤
        MStar * Real.exp (-X) := by
    simpa [MStar, X] using hmultiplicity
  have hentropy' :
      ((2 : ℝ) ^ Nat.choose D.sparse.card 2) ≤
        Real.exp (nu * (D.sparse.card : ℝ) * n) := by
    simpa [nu] using hentropy
  have hX : -X ≤ -(cCap * (D.sparse.card : ℝ) * n) := by
    linarith
  have hMStar : 0 ≤ MStar := by
    dsimp [MStar]
    positivity
  calc
    ((supercriticalCleanDivisionProfileGraphFinset
        k hk gamma ⟨le_of_lt hgamma.1, hgamma.2⟩
        m n tau hn D profile).card : ℝ) ≤
        (supercriticalProfileMultiplicity profile : ℝ) *
          (2 : ℝ) ^ Nat.choose D.sparse.card 2 := hencoding
    _ ≤ (MStar * Real.exp (-X)) *
          Real.exp (nu * (D.sparse.card : ℝ) * n) := by
      gcongr
    _ ≤ (MStar * Real.exp
          (-(cCap * (D.sparse.card : ℝ) * n))) *
          Real.exp (nu * (D.sparse.card : ℝ) * n) := by
      gcongr
    _ = MStar * Real.exp (-(nu * (D.sparse.card : ℝ) * n)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [nu, cCap, supercriticalSparsePenaltyConstant]
      ring
    _ = (supercriticalProfileMultiplicity
          (supercriticalAbsorbSparseProfile hk D profile) : ℝ) *
        Real.exp (-(supercriticalSparsePenaltyConstant k gamma *
          (D.sparse.card : ℝ) * (n : ℝ))) := by
      rfl

/-! ## Paper-facing parameter hierarchy -/

/-- Paper: Lemma `lemma:super-Fstar`.

For every strict supercritical density there is a positive constant depending
only on `k` and `gamma` which penalizes every nonempty-sparse clean profile
fiber by `exp (-nu |S| n)`.  The only project-specific input is the BCLSV
finite alignment used by `superCloseStructureK1k` to recover the explicit
geometry for a witness from a nonempty fiber. -/
theorem superFStar
    (k : ℕ) (hk : 3 ≤ k)
    (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    ∃ nu : ℝ, 0 < nu ∧
      ∀ alpha : ℝ,
        alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * (k : ℝ))) →
        ∃ delta0 : ℝ, 0 < delta0 ∧
          ∀ delta : ℝ,
            0 < delta → delta < delta0 →
            ∀ epsilon : ℝ, 0 < epsilon →
              ∃ tau : ℝ, 0 < tau ∧
                ∃ n0 : ℕ,
                  ∀ n : ℕ, n0 ≤ n →
                  ∀ (m : ℕ)
                    (hn : k - 1 ≤ n)
                    (D : SupercriticalDivision k (Fin n)),
                    D.sparse.Nonempty →
                    ∀ (t : ℕ),
                      t ≤ Nat.choose D.sparse.card 2 →
                    ∀ profile : SupercriticalEdgeProfile D,
                      SupercriticalProfileAtShift D m
                        (supercriticalOffDiagonal k gamma)
                        delta (t : ℤ) profile →
                      ((supercriticalCleanDivisionProfileGraphFinset
                        k hk gamma
                        ⟨le_of_lt hgamma.1, hgamma.2⟩
                        m n tau hn D profile).card : ℝ) ≤
                      (supercriticalProfileMultiplicity
                        (supercriticalAbsorbSparseProfile
                          hk D profile) : ℝ) *
                      Real.exp (-(nu *
                        (D.sparse.card : ℝ) * (n : ℝ))) := by
  classical
  let nu := supercriticalSparsePenaltyConstant k gamma
  have hnu : 0 < nu := supercriticalSparsePenaltyConstant_pos hk hgamma
  refine ⟨nu, hnu, ?_⟩
  intro alpha halpha
  let delta0 := supercriticalCleanSparseDeltaBound k gamma alpha
  have hdelta0 : 0 < delta0 :=
    supercriticalCleanSparseDeltaBound_pos hk hgamma halpha.1
  refine ⟨delta0, hdelta0, ?_⟩
  intro delta hdelta hdeltaLt epsilon hepsilon
  obtain ⟨hdeltaAlpha, hrhoLower, hrhoUpper,
      hdeltaRho, hdeltaBalance, hdeltaEntropy⟩ :=
    supercriticalCleanSparseDeltaBound_spec hk hgamma hdeltaLt
  let hgammaIco : gamma ∈ Set.Ico (gammaK k) 1 :=
    ⟨le_of_lt hgamma.1, hgamma.2⟩
  let tau := supercriticalCloseStructureCutRadius k hk gamma hgammaIco alpha
    halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon
  have htau : 0 < tau := by
    dsimp [tau]
    exact supercriticalCloseStructureCutRadius_pos k hk gamma hgammaIco alpha
      halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon
  refine ⟨tau, htau, ?_⟩
  let n0 := supercriticalCloseStructureVertexThreshold k hk gamma hgammaIco
    alpha halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon
  refine ⟨n0, ?_⟩
  intro n hnLarge m hn D hsparseNonempty t ht profile hprofile
  let F := supercriticalCleanDivisionProfileGraphFinset
    k hk gamma hgammaIco m n tau hn D profile
  by_cases hF : F = ∅
  · change ((F.card : ℕ) : ℝ) ≤ _
    rw [hF]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨G, hG⟩ := hFne
    have hGprofile : G ∈ supercriticalCleanDivisionProfileGraphFinset
        k hk gamma hgammaIco m n tau hn D profile := by
      simpa [F] using hG
    have hGclean :=
      (mem_supercriticalCleanDivisionProfileGraphFinset.mp hGprofile).1
    have hGclose :=
      (mem_supercriticalCleanDivisionGraphFinset.mp hGclean).1
    have hfamily : G ∈
        inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
          supercriticalFarGraphFinset k hk gamma hgammaIco m n tau := by
      rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
      exact hGclose
    obtain ⟨R⟩ := superCloseStructureK1k k hk gamma hgammaIco alpha
      halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon
      m hnLarge G (by simpa [tau] using hfamily)
    have hdivision :=
      canonicalSupercriticalDivision_eq_of_mem_cleanProfile hGprofile
    have hcastSub : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hbalanced : ∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
            (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n := by
      intro i
      simpa only [hdivision, hcastSub] using R.part_card_close i
    have hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2 := by
      simpa only [hdivision] using R.sparse_card_le
    have hdensity : ∀ e,
        supercriticalOffDiagonal k gamma - delta ≤
            profileDensity profile e ∧
          profileDensity profile e ≤
            supercriticalOffDiagonal k gamma + delta := by
      intro e
      have hcloseDensity := R.cross_density_close
        e.left e.right e.left_ne_right
      have hprofileEq := crossEdgeProfile_eq_of_mem_cleanProfile hGprofile
      have habs :
          |profileDensity profile e - supercriticalOffDiagonal k gamma| ≤
            delta := by
        rw [← hprofileEq, profileDensity_crossEdgeProfile]
        simpa only [hdivision] using hcloseDensity
      rw [abs_le] at habs
      constructor <;> linarith [habs.1, habs.2]
    have hdeltaBasic :
        delta < supercriticalSparseDeltaBound k gamma := by
      have hdeltaClean :
          delta < supercriticalCleanSparseDeltaBound k gamma alpha := by
        simpa [delta0] using hdeltaLt
      exact hdeltaClean.trans_le <| by
        calc
          supercriticalCleanSparseDeltaBound k gamma alpha ≤
              min (supercriticalOffDiagonal k gamma / 4)
                (min ((1 - supercriticalOffDiagonal k gamma) / 4)
                  (supercriticalSparseDeltaBound k gamma)) :=
            min_le_right _ _
          _ ≤ min ((1 - supercriticalOffDiagonal k gamma) / 4)
                (supercriticalSparseDeltaBound k gamma) := min_le_right _ _
          _ ≤ supercriticalSparseDeltaBound k gamma := min_le_right _ _
    change ((F.card : ℕ) : ℝ) ≤ _
    simpa [F, nu] using
      supercriticalCleanSparsePenalty_of_geometry hk hgamma hdelta.le
        hdeltaBasic
        D hsparseNonempty hbalanced hsparse profile hdensity hprofile ht

end InducedStars
