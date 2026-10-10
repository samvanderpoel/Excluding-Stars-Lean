import InducedStars.FiniteModels.Gnp
import InducedStars.Graphon.RelativeEntropy
import InducedStars.Graphon.SetDistance

/-!
# Uniform finite-family probabilities and optimizer-far events

This file packages the two finite conditional events used by the graphon
rough-structure argument.  Every graph is labeled on `Fin n`, every edge count
uses unordered edges through `SimpleGraph.edgeFinset`, and every finite graph
is compared with optimizer graphons through the existing zero-diagonal
adjacency graphon `graphGraphon`.
-/

noncomputable section

open Set

namespace InducedStars

/-- Local finite-edge instance for the labeled graphs used in this file. -/
noncomputable local instance uniformEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-- Local decidable equality, used only to display finite-event
intersections. -/
noncomputable local instance uniformGraphDecidableEq {n : ℕ} :
    DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

/-! ## Uniform probability on a finite family -/

/-- The uniform mass of a finite subfamily `A` relative to a finite ambient
family `Ω`.  The definition is total, but probability applications must prove
that `Ω` is nonempty and that `A ⊆ Ω`. -/
noncomputable def uniformSubfamilyProbability
    {α : Type*} [Fintype α] (Ω A : Finset α) : ℝ :=
  (A.card : ℝ) / (Ω.card : ℝ)

/-- The defining cardinality-ratio identity. -/
theorem uniformSubfamilyProbability_eq_card_ratio
    {α : Type*} [Fintype α] (Ω A : Finset α) :
    uniformSubfamilyProbability Ω A =
      (A.card : ℝ) / (Ω.card : ℝ) :=
  rfl

/-- A genuine uniform subfamily probability is nonnegative. -/
theorem uniformSubfamilyProbability_nonneg
    {α : Type*} [Fintype α] {Ω A : Finset α}
    (_hΩ : Ω.Nonempty) (_hA : A ⊆ Ω) :
    0 ≤ uniformSubfamilyProbability Ω A := by
  unfold uniformSubfamilyProbability
  positivity

/-- A subfamily has uniform probability at most one in a nonempty ambient
family. -/
theorem uniformSubfamilyProbability_le_one
    {α : Type*} [Fintype α] {Ω A : Finset α}
    (hΩ : Ω.Nonempty) (hA : A ⊆ Ω) :
    uniformSubfamilyProbability Ω A ≤ 1 := by
  unfold uniformSubfamilyProbability
  apply (div_le_one (by exact_mod_cast Finset.card_pos.mpr hΩ)).2
  exact_mod_cast Finset.card_le_card hA

/-- The empty event has uniform probability zero. -/
@[simp] theorem uniformSubfamilyProbability_empty
    {α : Type*} [Fintype α] (Ω : Finset α) :
    uniformSubfamilyProbability Ω ∅ = 0 := by
  simp [uniformSubfamilyProbability]

/-- Uniform subfamily probability is monotone under event inclusion, provided
the common ambient family is nonempty and contains the larger event. -/
theorem uniformSubfamilyProbability_mono
    {α : Type*} [Fintype α] {Ω A B : Finset α}
    (hΩ : Ω.Nonempty) (_hB : B ⊆ Ω) (hAB : A ⊆ B) :
    uniformSubfamilyProbability Ω A ≤
      uniformSubfamilyProbability Ω B := by
  unfold uniformSubfamilyProbability
  apply (div_le_div_iff_of_pos_right
    (by exact_mod_cast Finset.card_pos.mpr hΩ)).2
  exact_mod_cast Finset.card_le_card hAB

/-- A genuine uniform subfamily probability lies in the unit interval. -/
theorem uniformSubfamilyProbability_mem_Icc
    {α : Type*} [Fintype α] {Ω A : Finset α}
    (hΩ : Ω.Nonempty) (hA : A ⊆ Ω) :
    uniformSubfamilyProbability Ω A ∈ Icc (0 : ℝ) 1 :=
  ⟨uniformSubfamilyProbability_nonneg hΩ hA,
    uniformSubfamilyProbability_le_one hΩ hA⟩

/-! ## Fixed-density optimizer-far graphs -/

/-- Labeled induced-`K₁,ₖ`-free graphs with the prescribed exact unordered
edge count whose adjacency graphons remain at least `ε` in cut distance from
the full fixed-density optimizer set. -/
noncomputable def fixedDensityOptimizerFarGraphFinset
    (k : ℕ) (γ ε : ℝ) (m : ℕ → ℕ) (n : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  (inducedStarFreeGraphFinsetWithEdges k n (m n)).filter fun G ↦
    ε ≤ cutDistToSet (graphGraphon G) (fixedDensityOptimizers k γ)

/-- Exact membership in the fixed-density optimizer-far family. -/
@[simp] theorem mem_fixedDensityOptimizerFarGraphFinset
    {k n : ℕ} {γ ε : ℝ} {m : ℕ → ℕ}
    {G : SimpleGraph (Fin n)} :
    G ∈ fixedDensityOptimizerFarGraphFinset k γ ε m n ↔
      ¬Regularity.InducedEmbeds (inducedStar k) G ∧
        G.edgeFinset.card = m n ∧
          ε ≤ cutDistToSet (graphGraphon G)
            (fixedDensityOptimizers k γ) := by
  classical
  simp [fixedDensityOptimizerFarGraphFinset, and_assoc]

/-- The optimizer-far exact-edge family is a subfamily of the full
induced-star-free exact-edge family. -/
theorem fixedDensityOptimizerFarGraphFinset_subset
    (k n : ℕ) (γ ε : ℝ) (m : ℕ → ℕ) :
    fixedDensityOptimizerFarGraphFinset k γ ε m n ⊆
      inducedStarFreeGraphFinsetWithEdges k n (m n) := by
  intro G hG
  exact (Finset.mem_filter.mp hG).1

/-- Uniform probability that an exact-edge induced-star-free labeled graph is
at least `ε` away from the fixed-density optimizer set. -/
noncomputable def fixedDensityOptimizerFarProbability
    (k : ℕ) (γ ε : ℝ) (m : ℕ → ℕ) (n : ℕ) : ℝ :=
  uniformSubfamilyProbability
    (inducedStarFreeGraphFinsetWithEdges k n (m n))
    (fixedDensityOptimizerFarGraphFinset k γ ε m n)

/-- The fixed-density bad-event probability is exactly the bad/full
cardinality ratio. -/
theorem fixedDensityOptimizerFarProbability_eq_card_ratio
    (k : ℕ) (γ ε : ℝ) (m : ℕ → ℕ) (n : ℕ) :
    fixedDensityOptimizerFarProbability k γ ε m n =
      ((fixedDensityOptimizerFarGraphFinset k γ ε m n).card : ℝ) /
        (inducedStarFreeGraphFinsetWithEdges k n (m n)).card :=
  rfl

/-- Nonnegativity of the fixed-density bad-event probability when its ambient
exact-edge family is nonempty. -/
theorem fixedDensityOptimizerFarProbability_nonneg
    {k n : ℕ} {γ ε : ℝ} {m : ℕ → ℕ}
    (hne : (inducedStarFreeGraphFinsetWithEdges k n (m n)).Nonempty) :
    0 ≤ fixedDensityOptimizerFarProbability k γ ε m n :=
  uniformSubfamilyProbability_nonneg hne
    (fixedDensityOptimizerFarGraphFinset_subset k n γ ε m)

/-- The fixed-density bad-event probability is at most one when its ambient
exact-edge family is nonempty. -/
theorem fixedDensityOptimizerFarProbability_le_one
    {k n : ℕ} {γ ε : ℝ} {m : ℕ → ℕ}
    (hne : (inducedStarFreeGraphFinsetWithEdges k n (m n)).Nonempty) :
    fixedDensityOptimizerFarProbability k γ ε m n ≤ 1 :=
  uniformSubfamilyProbability_le_one hne
    (fixedDensityOptimizerFarGraphFinset_subset k n γ ε m)

/-! ## Conditioned `G(n,p)` optimizer-far graphs -/

/-- Labeled induced-`K₁,ₖ`-free graphs whose adjacency graphons remain at
least `ε` in cut distance from the full conditioned optimizer set. -/
noncomputable def gnpOptimizerFarInducedStarFinset
    (k : ℕ) (p ε : ℝ) (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  (inducedFreeGraphFinset (inducedStar k) n).filter fun G ↦
    ε ≤ cutDistToSet (graphGraphon G) (gnpGraphonOptimizers k p)

/-- Exact membership in the conditioned optimizer-far induced-star family. -/
@[simp] theorem mem_gnpOptimizerFarInducedStarFinset
    {k n : ℕ} {p ε : ℝ} {G : SimpleGraph (Fin n)} :
    G ∈ gnpOptimizerFarInducedStarFinset k p ε n ↔
      ¬Regularity.InducedEmbeds (inducedStar k) G ∧
        ε ≤ cutDistToSet (graphGraphon G)
          (gnpGraphonOptimizers k p) := by
  classical
  simp [gnpOptimizerFarInducedStarFinset]

/-- The conditioned optimizer-far event is a subfamily of induced-star
freeness. -/
theorem gnpOptimizerFarInducedStarFinset_subset
    (k n : ℕ) (p ε : ℝ) :
    gnpOptimizerFarInducedStarFinset k p ε n ⊆
      inducedFreeGraphFinset (inducedStar k) n := by
  intro G hG
  exact (Finset.mem_filter.mp hG).1

/-- Explicit event-intersection form of the optimizer-far induced-star
family. -/
theorem gnpOptimizerFarInducedStarFinset_eq_inter
    (k n : ℕ) (p ε : ℝ) :
    gnpOptimizerFarInducedStarFinset k p ε n =
      inducedFreeGraphFinset (inducedStar k) n ∩
        (Finset.univ.filter fun G : SimpleGraph (Fin n) ↦
          ε ≤ cutDistToSet (graphGraphon G)
            (gnpGraphonOptimizers k p)) := by
  classical
  ext G
  simp [gnpOptimizerFarInducedStarFinset]

/-- The `G(n,p)` mass of the induced-star-free optimizer-far event. -/
noncomputable def gnpOptimizerFarInducedStarProbability
    (k n : ℕ) (p ε : ℝ) : ℝ :=
  gnpGraphEventProbability p (gnpOptimizerFarInducedStarFinset k p ε n)

/-- The numerator is literally the `G(n,p)` mass of the displayed event
intersection. -/
theorem gnpOptimizerFarInducedStarProbability_eq_inter
    (k n : ℕ) (p ε : ℝ) :
    gnpOptimizerFarInducedStarProbability k n p ε =
      gnpGraphEventProbability p
        (inducedFreeGraphFinset (inducedStar k) n ∩
          (Finset.univ.filter fun G : SimpleGraph (Fin n) ↦
            ε ≤ cutDistToSet (graphGraphon G)
              (gnpGraphonOptimizers k p))) := by
  rw [gnpOptimizerFarInducedStarProbability,
    gnpOptimizerFarInducedStarFinset_eq_inter]

/-- The optimizer-far numerator is bounded by the full induced-star-free
probability. -/
theorem gnpOptimizerFarInducedStarProbability_le_inducedStarFreeProbability
    {k n : ℕ} {p ε : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    gnpOptimizerFarInducedStarProbability k n p ε ≤
      gnpInducedStarFreeProbability k n p := by
  exact gnpGraphEventProbability_mono hp
    (gnpOptimizerFarInducedStarFinset_subset k n p ε)

/-- The exact conditional probability of being optimizer-far given
induced-star-freeness in the finite labeled `G(n,p)` model. -/
noncomputable def gnpConditionedOptimizerFarProbability
    (k n : ℕ) (p ε : ℝ) : ℝ :=
  gnpOptimizerFarInducedStarProbability k n p ε /
    gnpInducedStarFreeProbability k n p

/-- Expanded event-ratio form of the conditioned optimizer-far
probability. -/
theorem gnpConditionedOptimizerFarProbability_eq_eventRatio
    (k n : ℕ) (p ε : ℝ) :
    gnpConditionedOptimizerFarProbability k n p ε =
      gnpGraphEventProbability p
          (gnpOptimizerFarInducedStarFinset k p ε n) /
        gnpGraphEventProbability p
          (inducedFreeGraphFinset (inducedStar k) n) :=
  rfl

/-- Fully expanded conditional-event identity: the numerator is the
intersection of induced-star-freeness with being optimizer-far, and the
denominator is the induced-star-free event. -/
theorem gnpConditionedOptimizerFarProbability_eq_interRatio
    (k n : ℕ) (p ε : ℝ) :
    gnpConditionedOptimizerFarProbability k n p ε =
      gnpGraphEventProbability p
          (inducedFreeGraphFinset (inducedStar k) n ∩
            (Finset.univ.filter fun G : SimpleGraph (Fin n) ↦
              ε ≤ cutDistToSet (graphGraphon G)
                (gnpGraphonOptimizers k p))) /
        gnpInducedStarFreeProbability k n p := by
  rw [gnpConditionedOptimizerFarProbability,
    gnpOptimizerFarInducedStarProbability_eq_inter]

/-- For the paper's star range and an interior edge probability, the
conditioning denominator is strictly positive. -/
theorem gnpConditionedOptimizerFarProbability_denominator_pos
    {k n : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < gnpInducedStarFreeProbability k n p :=
  gnpInducedStarFreeProbability_pos (by omega) hp

/-- The conditioned optimizer-far probability is nonnegative on the paper's
parameter range. -/
theorem gnpConditionedOptimizerFarProbability_nonneg
    {k n : ℕ} (hk : 3 ≤ k) {p ε : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ gnpConditionedOptimizerFarProbability k n p ε := by
  unfold gnpConditionedOptimizerFarProbability
  exact div_nonneg
    (gnpGraphEventProbability_nonneg ⟨hp.1.le, hp.2.le⟩ _)
    (gnpConditionedOptimizerFarProbability_denominator_pos hk hp).le

/-- The conditioned optimizer-far probability is at most one on the paper's
parameter range. -/
theorem gnpConditionedOptimizerFarProbability_le_one
    {k n : ℕ} (hk : 3 ≤ k) {p ε : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    gnpConditionedOptimizerFarProbability k n p ε ≤ 1 := by
  unfold gnpConditionedOptimizerFarProbability
  apply (div_le_one
    (gnpConditionedOptimizerFarProbability_denominator_pos hk hp)).2
  exact gnpOptimizerFarInducedStarProbability_le_inducedStarFreeProbability
    ⟨hp.1.le, hp.2.le⟩

end InducedStars
