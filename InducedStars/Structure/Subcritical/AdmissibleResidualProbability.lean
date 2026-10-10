import InducedStars.Structure.Subcritical.AdmissibleResidualMatching
import InducedStars.Structure.Subcritical.ResidualJanson

/-!
# Uniform safety probability for every admissible residual graph

Paper: the Janson step in lemma:residual-matching-estimate-K1k.
The forbidden set is arbitrary and the whole remainder is fixed. The defect
pattern in the random model is exactly the supplied admissible residual graph.
No profile, generating graph, or induced-freeness assumption is required.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k n R₀ ell m : ℕ} {eta delta d : ℝ}
  {D : SubcriticalDivision k (Fin n)} {B : Finset (Fin n)}

/-- The paper's maximum over the entire narrow quota window, for fixed H,R. -/
def subcriticalAdmissibleResidualSafeMaximum
    (B : Finset (Fin n)) (H : SubcriticalRemainderGraph D eta R₀)
    (R : SimpleGraph (Fin n)) (m : ℕ) (Cwin delta epsilon : ℝ) : ℝ :=
  subcriticalFiniteMax (retainedNarrowEdgeCountWindow D eta R₀ m Cwin delta epsilon)
    (fun mvec ↦ subcriticalResidualSafeProbabilityForRoots B H R R mvec)

/-- Thinning and the shared geometric Janson core give the same rate for
every admissible residual graph and every narrow quota vector. -/
theorem subcriticalAdmissibleResidualProbability_le
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀) (hell : 1 ≤ ell)
    (hscale : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * n)
    (hdelta : delta ≤ subcriticalPaletteGap k / 2)
    (hd0 : 0 ≤ d) (hd : d ≤ subcriticalResidualDegreeCap k eta R₀)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hroots : (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2)
    (H : SubcriticalRemainderGraph D eta R₀) (Cwin epsilon : ℝ)
    (R : SimpleGraph (Fin n))
    (hR : SubcriticalAdmissibleResidualGraph D eta R₀ B d ell R)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m Cwin delta epsilon) :
    subcriticalResidualSafeProbabilityForRoots B H R R mvec ≤
      Real.exp (-(subcriticalResidualMatchingConstant k eta R₀ /
        subcriticalResidualMatchingKappa eta R₀) * ell * n) := by
  obtain ⟨M, hlarge, hsmall⟩ := subcriticalAdmissibleResidual_exists_matching
    hR heta hetaOne hR₀ hell (by simpa only [Fintype.card_fin] using hscale)
  have hvalid : IsSubcriticalRetainedDefectPattern D eta R₀ R := by
    intro x y hxy
    exact hR.allowed x y hxy
  exact subcriticalResidualMatchingSafeProbability_le_of_valid hk J heta hR₀ M
    R hvalid (fun _ _ _ _ ↦ Iff.rfl) H mvec hm hdelta hd0 hd
    (by simpa only [Fintype.card_fin] using hR.degree_le) hpart hroots
    (by simpa only [Fintype.card_fin] using hsmall) hlarge

/-- Taking the finite quota maximum preserves the uniform matching penalty,
including an empty quota window. -/
theorem subcriticalAdmissibleResidualSafeMaximum_le
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀) (hell : 1 ≤ ell)
    (hscale : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * n)
    (hdelta : delta ≤ subcriticalPaletteGap k / 2)
    (hd0 : 0 ≤ d) (hd : d ≤ subcriticalResidualDegreeCap k eta R₀)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hroots : (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2)
    (H : SubcriticalRemainderGraph D eta R₀) (m : ℕ) (Cwin epsilon : ℝ)
    (R : SimpleGraph (Fin n))
    (hR : SubcriticalAdmissibleResidualGraph D eta R₀ B d ell R) :
    subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon ≤
      Real.exp (-(subcriticalResidualMatchingConstant k eta R₀ /
        subcriticalResidualMatchingKappa eta R₀) * ell * n) := by
  apply subcriticalFiniteMax_le (Real.exp_pos _).le
  intro mvec hm
  exact subcriticalAdmissibleResidualProbability_le hk J heta hetaOne hR₀ hell
    hscale hdelta hd0 hd hpart hroots H Cwin epsilon R hR mvec hm

/-- With no residual pair, safety is the certain event for every quota. -/
theorem subcriticalResidualSafeProbabilityForRoots_bot
    (B : Finset (Fin n)) (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph (Fin n)) (mvec : RetainedEdgeCountVector D eta R₀) :
    subcriticalResidualSafeProbabilityForRoots B H T ⊥ mvec = 1 := by
  have hsafe : subcriticalResidualSafeEvent k B (⊥ : SimpleGraph (Fin n)) = Set.univ := by
    ext G
    simp [subcriticalResidualSafeEvent]
  simp [subcriticalResidualSafeProbabilityForRoots, subcriticalActiveBernoulliProbability,
    subcriticalActiveGraphEvent, hsafe]

/-- A nonempty narrow window makes its maximum of the certain event one. -/
theorem subcriticalAdmissibleResidualSafeMaximum_bot
    (B : Finset (Fin n)) (H : SubcriticalRemainderGraph D eta R₀)
    (m : ℕ) (Cwin delta epsilon : ℝ)
    (hne : (retainedNarrowEdgeCountWindow D eta R₀ m Cwin delta epsilon).Nonempty) :
    subcriticalAdmissibleResidualSafeMaximum B H ⊥ m Cwin delta epsilon = 1 := by
  apply le_antisymm
  · apply subcriticalFiniteMax_le zero_le_one
    intro mvec _
    exact (subcriticalResidualSafeProbabilityForRoots_bot B H ⊥ mvec).le
  · obtain ⟨mvec, hm⟩ := hne
    have h := le_subcriticalFiniteMax
      (fun mv ↦ subcriticalResidualSafeProbabilityForRoots B H ⊥ ⊥ mv) hm
    simpa only [subcriticalAdmissibleResidualSafeMaximum,
      subcriticalResidualSafeProbabilityForRoots_bot] using h

/-- The full zero-matching sum is exactly one, with no condition on B beyond
being a vertex set. A nonempty quota window is stated explicitly. -/
theorem subcriticalAdmissibleResidualSafetySum_zero
    (B : Finset (Fin n)) (H : SubcriticalRemainderGraph D eta R₀)
    (m : ℕ) (Cwin delta epsilon d C : ℝ) (hd : 0 ≤ d)
    (hne : (retainedNarrowEdgeCountWindow D eta R₀ m Cwin delta epsilon).Nonempty) :
    (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d 0,
      Real.exp (C * (finiteGraphEdges R).card) *
        subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon) = 1 :=
  subcriticalAdmissibleResidualWeightedSum_zero D eta R₀ B d C
    (fun R ↦ subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon)
    hd (subcriticalAdmissibleResidualSafeMaximum_bot B H m Cwin delta epsilon hne)

end InducedStars
