import InducedStars.C4.SplitEnumeration

/-!
# Exact split-size enumeration and the scalar maximum

Paper: the final entropy deduction in `paper/c4-free.tex`.
The binomial product counts actual ordered division/graph pairs of a fixed
clique size. It is not identified with the number of distinct split graphs.
Both impossible clique sizes and impossible forced internal counts are
guarded explicitly.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

def c4DivisionsWithCliqueSize (n b : ℕ) : Finset (C4Division (Fin n)) :=
  univ.filter fun D ↦ D.cliquePart.card = b

@[simp] theorem mem_c4DivisionsWithCliqueSize {n b : ℕ} {D : C4Division (Fin n)} :
    D ∈ c4DivisionsWithCliqueSize n b ↔ D.cliquePart.card = b := by
  simp [c4DivisionsWithCliqueSize]

theorem card_c4DivisionsWithCliqueSize (n b : ℕ) :
    (c4DivisionsWithCliqueSize n b).card = Nat.choose n b := by
  have hcomp (S : Finset (Fin n)) : univ \ (univ \ S) = S :=
    Finset.sdiff_sdiff_eq_self (subset_univ S)
  have hinj : Function.Injective (fun S : Finset (Fin n) ↦ univ \ S) := by
    intro S T h
    have h' := congrArg (fun A : Finset (Fin n) ↦ univ \ A) h
    simpa only [hcomp] using h'
  have himage : c4DivisionsWithCliqueSize n b =
      ((univ : Finset (Fin n)).powersetCard b).image (fun S ↦ univ \ S) := by
    ext D
    constructor
    · intro hD
      refine mem_image.mpr ⟨D.cliquePart, mem_powersetCard.mpr
        ⟨subset_univ _, mem_c4DivisionsWithCliqueSize.mp hD⟩, ?_⟩
      exact hcomp D
    · rintro hD
      obtain ⟨S, hS, rfl⟩ := mem_image.mp hD
      apply mem_c4DivisionsWithCliqueSize.mpr
      change (univ \ (univ \ S)).card = b
      rw [hcomp]
      exact (mem_powersetCard.mp hS).2
  rw [himage, card_image_of_injective _ hinj, card_powersetCard, card_univ, Fintype.card_fin]

/-- The common cardinality of a single split fiber with clique size `b`.
The outer guard prevents both natural-subtraction failure modes. -/
def c4SplitFiberCardOfCliqueSize (n m b : ℕ) : ℕ :=
  if b ≤ n ∧ b.choose 2 ≤ m then
    Nat.choose (b * (n - b)) (m - b.choose 2)
  else 0

theorem c4SplitFiber_card_of_cliqueSize {n m b : ℕ} (D : C4Division (Fin n))
    (hb : D.cliquePart.card = b) :
    (c4SplitFiber D m).card = c4SplitFiberCardOfCliqueSize n m b := by
  have hparts := D.card_add
  rw [hb, Fintype.card_fin] at hparts
  have hbn : b ≤ n := by omega
  have hA : D.independentPart.card = n - b := by omega
  rw [card_c4SplitFiber, hb, hA]
  simp only [c4SplitFiberCardOfCliqueSize, hbn, true_and, Nat.mul_comm]

/-- Actual ordered division/graph pairs, indexed by the division and with
the exact clique size and graph edge count retained. -/
def c4SplitPairsOfCliqueSize (n m b : ℕ) :
    Finset (Σ _D : C4Division (Fin n), SimpleGraph (Fin n)) :=
  (c4DivisionsWithCliqueSize n b).sigma (fun D ↦ c4SplitFiber D m)

@[simp] theorem mem_c4SplitPairsOfCliqueSize {n m b : ℕ}
    {P : Σ _D : C4Division (Fin n), SimpleGraph (Fin n)} :
    P ∈ c4SplitPairsOfCliqueSize n m b ↔
      P.1.cliquePart.card = b ∧ P.2 ∈ c4SplitFiber P.1 m := by
  simp [c4SplitPairsOfCliqueSize]

theorem card_c4SplitPairsOfCliqueSize (n m b : ℕ) :
    (c4SplitPairsOfCliqueSize n m b).card =
      Nat.choose n b * c4SplitFiberCardOfCliqueSize n m b := by
  rw [c4SplitPairsOfCliqueSize, card_sigma]
  calc
    _ = ∑ _D ∈ c4DivisionsWithCliqueSize n b, c4SplitFiberCardOfCliqueSize n m b := by
      apply sum_congr rfl
      intro D hD
      exact c4SplitFiber_card_of_cliqueSize D (mem_c4DivisionsWithCliqueSize.mp hD)
    _ = _ := by rw [sum_const, smul_eq_mul, card_c4DivisionsWithCliqueSize]

/-- The literal finite binomial product, with every infeasible case zero. -/
theorem card_c4SplitPairsOfCliqueSize_eq_guarded_product (n m b : ℕ) :
    (c4SplitPairsOfCliqueSize n m b).card =
      if b ≤ n ∧ b.choose 2 ≤ m then
        Nat.choose n b * Nat.choose (b * (n - b)) (m - b.choose 2)
      else 0 := by
  rw [card_c4SplitPairsOfCliqueSize, c4SplitFiberCardOfCliqueSize]
  split_ifs <;> simp

theorem sum_c4SplitFiber_card_eq_cliqueSize_sum (n m : ℕ) :
    (∑ D : C4Division (Fin n), (c4SplitFiber D m).card) =
      ∑ b ∈ range (n + 1), Nat.choose n b * c4SplitFiberCardOfCliqueSize n m b := by
  have hmap : ∀ D ∈ (univ : Finset (C4Division (Fin n))),
      D.cliquePart.card ∈ range (n + 1) := by
    intro D hD
    have hparts := D.card_add
    simp only [Fintype.card_fin] at hparts
    exact mem_range.mpr (by omega)
  rw [← sum_fiberwise_of_maps_to hmap (fun D ↦ (c4SplitFiber D m).card)]
  apply sum_congr rfl
  intro b hb
  change (∑ D ∈ c4DivisionsWithCliqueSize n b, (c4SplitFiber D m).card) = _
  rw [← card_sigma]
  exact card_c4SplitPairsOfCliqueSize n m b

theorem c4SplitFiberCardOfCliqueSize_le_splitGraphCount (n m b : ℕ) :
    c4SplitFiberCardOfCliqueSize n m b ≤ splitGraphCountWithEdges n m := by
  by_cases hb : b ≤ n
  · rw [← c4SplitFiber_card_of_cliqueSize (c4DivisionOfCliqueSize n b)
      (c4DivisionOfCliqueSize_clique_card hb)]
    exact c4SplitFiber_card_le_splitGraphCount _
  · simp [c4SplitFiberCardOfCliqueSize, hb]

/-- Actual split graphs lie between the largest single fiber and the
binomially weighted count of ordered division/graph pairs. -/
theorem splitGraphCount_cliqueSize_bounds (n m : ℕ) :
    (range (n + 1)).sup (c4SplitFiberCardOfCliqueSize n m) ≤ splitGraphCountWithEdges n m ∧
      splitGraphCountWithEdges n m ≤
        ∑ b ∈ range (n + 1), Nat.choose n b * c4SplitFiberCardOfCliqueSize n m b := by
  constructor
  · exact Finset.sup_le (fun b hb ↦ c4SplitFiberCardOfCliqueSize_le_splitGraphCount n m b)
  · rw [← sum_c4SplitFiber_card_eq_cliqueSize_sum]
    exact splitGraphCount_le_sum_card_c4SplitFiber n m

/-- Literal maximum formula in the complete-edge-count normalization:
the value is attained, not merely an upper bound or a formal supremum. -/
theorem c4SplitOptimalEntropy_isGreatest {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    IsGreatest ((fun x : ℝ ↦ 2 * x * (1 - x) *
      binaryEntropy (c4SplitCrossDensity gamma x)) ''
        Set.Icc (1 - Real.sqrt (1 - gamma)) (Real.sqrt gamma))
      (c4SplitOptimalEntropy gamma) := by
  constructor
  · refine ⟨c4Lambda gamma, ?_, ?_⟩
    · exact ⟨(c4Lambda_mem_feasibleInterior hgamma).1.le,
        (c4Lambda_mem_feasibleInterior hgamma).2.le⟩
    · unfold c4SplitOptimalEntropy c4SplitEntropy
      ring
  · rintro y ⟨x, hx, rfl⟩
    have h := mul_le_mul_of_nonneg_left (c4SplitEntropy_isMaxOn hgamma hx)
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [c4SplitOptimalEntropy, c4SplitEntropy, mul_assoc] using h

theorem c4SplitOptimalEntropy_eq_scalarSup {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    c4SplitOptimalEntropy gamma = sSup ((fun x : ℝ ↦ 2 * x * (1 - x) *
      binaryEntropy (c4SplitCrossDensity gamma x)) ''
        Set.Icc (1 - Real.sqrt (1 - gamma)) (Real.sqrt gamma)) := by
  have h := c4SplitOptimalEntropy_isGreatest hgamma
  exact (h.isLUB.csSup_eq ⟨_, h.1⟩).symm

end InducedStars
