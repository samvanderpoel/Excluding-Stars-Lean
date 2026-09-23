import InducedStars.Structure.Subcritical.ProfileExtraction
import InducedStars.Structure.Subcritical.ProfileRootBounds
import InducedStars.Structure.Subcritical.RetainedMembership

/-!
# Finite profile classes, pattern families, and covering

Paper: Definition `def:profile-class-K1k` and Lemma
`lemma:profile-covering-K1k`. The core filter works over any finite graph
family; the candidate wrapper uses the existing literal canonical-division
family. Covering follows by extracting data from the actual graph.
-/

noncomputable section
open Finset
open scoped Classical BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A profile class inside a specified finite ambient graph family. -/
def subcriticalProfileClassGraphFinset (F : Finset (SimpleGraph V))
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) : Finset (SimpleGraph V) :=
  F.filter fun G ↦ RealizesSubcriticalProfile G alpha p

@[simp] theorem mem_subcriticalProfileClassGraphFinset
    {F : Finset (SimpleGraph V)} {D : SubcriticalDivision k V}
    {eta theta alpha : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}
    {G : SimpleGraph V} :
    G ∈ subcriticalProfileClassGraphFinset F alpha p ↔
      G ∈ F ∧ RealizesSubcriticalProfile G alpha p := by
  simp [subcriticalProfileClassGraphFinset]

/-- The literal paper profile class inside the candidate/canonical-division family. -/
def subcriticalCandidateProfileClassGraphFinset
    (k n m : ℕ) (W : Graphon) (tau : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (D : SubcriticalDivision k (Fin n)) (eta theta alpha : ℝ)
    (p : SubcriticalProfile D eta R₀ theta) : Finset (SimpleGraph (Fin n)) :=
  subcriticalProfileClassGraphFinset
    (subcriticalCandidateDivisionGraphFinset k n m W tau R₀ hk hn D) alpha p

@[simp] theorem mem_subcriticalCandidateProfileClassGraphFinset
    {k n m : ℕ} {W : Graphon} {tau : ℝ} {R₀ : ℕ} {hk : 3 ≤ k} {hn : k - 1 ≤ n}
    {D : SubcriticalDivision k (Fin n)} {eta theta alpha : ℝ}
    {p : SubcriticalProfile D eta R₀ theta} {G : SimpleGraph (Fin n)} :
    G ∈ subcriticalCandidateProfileClassGraphFinset k n m W tau R₀ hk hn D eta theta alpha p ↔
      G ∈ subcriticalCandidateDivisionGraphFinset k n m W tau R₀ hk hn D ∧
        RealizesSubcriticalProfile G alpha p := mem_subcriticalProfileClassGraphFinset

/-- Finite covering is witnessed by canonical extraction, with no geometric
or freeness hypothesis and no assertion that the classes are disjoint. -/
theorem subcriticalProfileCovering (F : Finset (SimpleGraph V))
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ)
    (halpha : 0 < alpha) (halpha_half : alpha < 1 / 2) :
    ∀ G ∈ F, ∃ p : SubcriticalProfile D eta R₀ theta,
      G ∈ subcriticalProfileClassGraphFinset F alpha p := by
  intro G hG
  exact ⟨subcriticalProfileOfGraph G D eta R₀ theta alpha halpha halpha_half,
    mem_subcriticalProfileClassGraphFinset.mpr ⟨hG,
      realizes_subcriticalProfileOfGraph G D eta R₀ theta alpha halpha halpha_half⟩⟩

theorem subcriticalProfileClasses_biUnion_eq (F : Finset (SimpleGraph V))
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ)
    (halpha : 0 < alpha) (halpha_half : alpha < 1 / 2) :
    Finset.univ.biUnion (fun p : SubcriticalProfile D eta R₀ theta ↦
      subcriticalProfileClassGraphFinset F alpha p) = F := by
  ext G
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h
    exact (mem_subcriticalProfileClassGraphFinset.mp hp).1
  · intro hG
    obtain ⟨p, hp⟩ := subcriticalProfileCovering F D eta R₀ theta alpha halpha halpha_half G hG
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hp⟩

theorem card_le_sum_subcriticalProfileClasses (F : Finset (SimpleGraph V))
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ)
    (halpha : 0 < alpha) (halpha_half : alpha < 1 / 2) :
    F.card ≤ ∑ p : SubcriticalProfile D eta R₀ theta,
      (subcriticalProfileClassGraphFinset F alpha p).card := by
  calc
    F.card = (Finset.univ.biUnion (fun p : SubcriticalProfile D eta R₀ theta ↦
        subcriticalProfileClassGraphFinset F alpha p)).card := by
      rw [subcriticalProfileClasses_biUnion_eq F D eta R₀ theta alpha halpha halpha_half]
    _ ≤ _ := Finset.card_biUnion_le

/-- Retained-incident defect patterns retain actual generating-graph witnesses. -/
def subcriticalRetainedDefectPatternFinset (F : Finset (SimpleGraph V))
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : Finset (SimpleGraph V) :=
  F.image fun G ↦ subcriticalRetainedIncidentDefectGraph G D eta R₀

def subcriticalRootedDefectPatternFinset (F : Finset (SimpleGraph V))
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) : Finset (SimpleGraph V) :=
  (subcriticalProfileClassGraphFinset F alpha p).image fun G ↦
    subcriticalRootedDefectGraph G D eta R₀ theta alpha

/-- Fix the rooted graph before extracting the residual patterns. The
profile itself does not determine the rooted neighbor subsets. -/
def subcriticalResidualDefectPatternFinset (F : Finset (SimpleGraph V))
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) (TB : SimpleGraph V) :
    Finset (SimpleGraph V) :=
  ((subcriticalProfileClassGraphFinset F alpha p).filter fun G ↦
    subcriticalRootedDefectGraph G D eta R₀ theta alpha = TB).image fun G ↦
      subcriticalResidualDefectGraph G D eta R₀ theta alpha

@[simp] theorem mem_subcriticalRetainedDefectPatternFinset
    (F : Finset (SimpleGraph V)) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (T : SimpleGraph V) :
    T ∈ subcriticalRetainedDefectPatternFinset F D eta R₀ ↔
      ∃ G ∈ F, subcriticalRetainedIncidentDefectGraph G D eta R₀ = T := by
  simp [subcriticalRetainedDefectPatternFinset]

@[simp] theorem mem_subcriticalRootedDefectPatternFinset
    (F : Finset (SimpleGraph V)) {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta)
    (T : SimpleGraph V) :
    T ∈ subcriticalRootedDefectPatternFinset F alpha p ↔
      ∃ G ∈ subcriticalProfileClassGraphFinset F alpha p,
        subcriticalRootedDefectGraph G D eta R₀ theta alpha = T := by
  simp [subcriticalRootedDefectPatternFinset]

@[simp] theorem mem_subcriticalResidualDefectPatternFinset
    (F : Finset (SimpleGraph V)) {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta)
    (TB T : SimpleGraph V) :
    T ∈ subcriticalResidualDefectPatternFinset F alpha p TB ↔
      ∃ G ∈ subcriticalProfileClassGraphFinset F alpha p,
        subcriticalRootedDefectGraph G D eta R₀ theta alpha = TB ∧
          subcriticalResidualDefectGraph G D eta R₀ theta alpha = T := by
  simp only [subcriticalResidualDefectPatternFinset, Finset.mem_image, Finset.mem_filter]
  aesop

namespace RealizesSubcriticalProfile

theorem roots_card_le_of_geometry {G : SimpleGraph V} {D : SubcriticalDivision k V}
    {eta theta alpha epsilon : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hn : 0 < Fintype.card V)
    (hretained : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hedges : ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤
      epsilon * (Fintype.card V : ℝ) ^ 2) :
    (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V := by
  rw [h.roots_eq]
  exact subcriticalBadRoots_card_le_finite G D eta R₀ halpha htheta hn hretained hvisible hedges

end RealizesSubcriticalProfile

/-- Realized-profile target trimming, at the paper's root-fraction constant.
The target size on the right is the original full visible part. -/
theorem subcriticalProfile_visibleTarget_trimmed
    {G : SimpleGraph V} {D : SubcriticalDivision k V}
    {eta theta alpha epsilon : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hepsilon : 0 ≤ epsilon) (hn : 0 < Fintype.card V)
    (hretained : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hedges : ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤
      epsilon * (Fintype.card V : ℝ) ^ 2)
    (a : D.PartIndex) (ha : a ∈ D.visiblePartIndices theta) :
    (1 - 2 * subcriticalProfileRootFraction alpha theta epsilon / theta) * (D.part a).card ≤
      ((D.part a \ p.roots).card : ℝ) := by
  exact subcriticalTarget_card_sdiff_ge_mul (D.part a) p.roots
    (by unfold subcriticalProfileRootFraction; positivity) htheta
    (h.roots_card_le_of_geometry halpha htheta hn hretained hvisible hedges) (hvisible a ha)

/-- The finite form of Paper Lemma `lemma:profile-covering-K1k`: covering
and the root bound for every member of every realized profile class. -/
theorem subcriticalProfileCovering_of_geometry (F : Finset (SimpleGraph V))
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha epsilon : ℝ)
    (halpha : 0 < alpha) (halpha_half : alpha < 1 / 2) (htheta : 0 < theta)
    (hn : 0 < Fintype.card V)
    (hretained : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hedges : ∀ G ∈ F, ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤
      epsilon * (Fintype.card V : ℝ) ^ 2) :
    (∀ G ∈ F, ∃ p : SubcriticalProfile D eta R₀ theta,
      G ∈ subcriticalProfileClassGraphFinset F alpha p) ∧
    (∀ p : SubcriticalProfile D eta R₀ theta, ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V) := by
  refine ⟨subcriticalProfileCovering F D eta R₀ theta alpha halpha halpha_half, ?_⟩
  intro p G hG
  obtain ⟨hGF, hr⟩ := mem_subcriticalProfileClassGraphFinset.mp hG
  exact hr.roots_card_le_of_geometry halpha htheta hn hretained hvisible (hedges G hGF)

/-- Paper: Lemma `lemma:profile-covering-K1k`. The radius is chosen before
the explicit candidate representation. Covering and the root estimate hold
for every canonical-division fiber and arbitrary exact edge count after the
order threshold. No later residual-matching constant is used. -/
theorem subcriticalProfileCovering_of_mem_candidateCutBall
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (_hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (hR₀ : 1 ≤ R₀) (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1) (heta : 0 < eta)
    (htheta : 0 < theta) (halpha : 0 < alpha) (halpha_half : alpha < 1 / 2)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (m : ℕ) (D : SubcriticalDivision k (Fin n)),
            let F := subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀
              hk (hn0.trans hn) D
            (∀ G ∈ F, ∃ p : SubcriticalProfile D eta R₀ theta,
              G ∈ subcriticalProfileClassGraphFinset F alpha p) ∧
            (∀ p : SubcriticalProfile D eta R₀ theta,
              ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
                (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * n) := by
  obtain ⟨tau, htau, hbridge⟩ := subcriticalCloseStructure k hk R₀ hR₀
    omega eta theta alpha delta epsilon homega heta htheta halpha hdelta hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L _hL
  obtain ⟨n0, hn0, hbridge⟩ := hbridge L
  refine ⟨n0, hn0, ?_⟩
  intro n hn m D
  refine ⟨subcriticalProfileCovering _ D eta R₀ theta alpha halpha halpha_half, ?_⟩
  intro p G hG
  obtain ⟨hGF, hr⟩ := mem_subcriticalProfileClassGraphFinset.mp hG
  obtain ⟨hball, hcanonical⟩ := mem_subcriticalCandidateDivisionGraphFinset.mp hGF
  have hcut := (mem_subcriticalCandidateCutBallGraphFinset.mp hball).2
  obtain ⟨R⟩ := hbridge hn G hcut
  have RD : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon := by
    simpa only [hcanonical] using R
  rw [hr.roots_eq]
  exact RD.badRoots_card_le halpha htheta (by omega) hR₀ homegaOne hcutoff

end InducedStars
