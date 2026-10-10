import InducedStars.Structure.Subcritical.FineStructureDecomposition

/-!
# Almost-all exact subcritical fine structure

Paper: Theorem `thm:main-almostall`, item `item:thm:main-almostall-sub`.
Retained-key counting orders the radii before the candidate representation, and the near-equality argument controls omitted graphon edge mass.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical
namespace InducedStars

theorem subcriticalUnstructuredProbability_tendsto_zero {k : ℕ} (hk : 3 ≤ k)
    {gamma xi : ℝ} (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hxi : 0 < xi)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ subcriticalUnstructuredProbability k gamma
      (subcriticalRemainderLowerCoefficient k gamma) xi n (m n)) atTop (𝓝 0) := by
  obtain ⟨P⟩ := exists_subcriticalFineStructureParameters hk hgamma hxi
  have hfar := subcriticalDistinguishedCutConcentration k hk hgamma
    (P.inputRadius hk hgamma) (P.inputRadius_pos hk hgamma) m hm
  have hnonclean := subcriticalNoncleanProbability_tendsto_zero hk hgamma P m hm
  have hlow := subcriticalRemainderLinearLowerTail hk hgamma P.eta_pos P.delta_pos
    P.size_reserve P.order_star P.delta_mu P.delta_remainder P.variance_reserve
    P.shift_reserve m hm
  obtain ⟨n0, hn0, hinput⟩ := P.inputRadius_spec hk hgamma m hm
  let low := fun n ↦ subcriticalLowRemainderGraphFinset k n (m n)
    (subcriticalDistinguishedBlockSequence k hk gamma hgamma) P.eta P.delta P.R₀
    (Nat.floor (subcriticalRemainderLowerCoefficient k gamma * n))
  apply squeeze_zero' (g := fun n ↦
    subcriticalDistinguishedFarProbability k hk gamma hgamma (P.inputRadius hk hgamma) n (m n) +
      subcriticalNoncleanProbability hk hgamma P n (m n) +
      uniformSubfamilyProbability (inducedStarFreeGraphFinsetWithEdges k n (m n)) (low n))
  · exact Eventually.of_forall fun n ↦ by
      unfold subcriticalUnstructuredProbability uniformSubfamilyProbability; positivity
  · filter_upwards [P.aggregation, eventually_ge_atTop n0,
      eventually_inducedStarFreeGraphFinsetWithEdges_nonempty k hk gamma
        ⟨hgamma.1,hgamma.2.trans (gammaK_lt_one hk)⟩ m hm] with n hP hn hpos
    have hinc := subcriticalUnstructured_subset_three_families hk (hn0.trans hn) hgamma P hP
      (hinput hn).2 (m := m n)
    have hc := (Finset.card_le_card hinc).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have hcR : ((subcriticalUnstructuredGraphFinset k n (m n) gamma
        (subcriticalRemainderLowerCoefficient k gamma) xi).card : ℝ) ≤
        (subcriticalDistinguishedFarGraphFinset k hk gamma hgamma (P.inputRadius hk hgamma)
          n (m n)).card + (subcriticalNoncleanGraphFinset hk hgamma P n (m n)).card +
          (low n).card := by exact_mod_cast hc
    unfold subcriticalUnstructuredProbability subcriticalDistinguishedFarProbability
      subcriticalNoncleanProbability uniformSubfamilyProbability
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right hcR (Nat.cast_nonneg _)
  · simpa only [add_zero] using (hfar.add hnonclean).add hlow

theorem subcriticalStructuredProbability_tendsto_one {k : ℕ} (hk : 3 ≤ k)
    {gamma xi : ℝ} (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hxi : 0 < xi)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ subcriticalStructuredProbability k gamma
      (subcriticalRemainderLowerCoefficient k gamma) xi n (m n)) atTop (𝓝 1) := by
  have h := (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub
    (subcriticalUnstructuredProbability_tendsto_zero hk hgamma hxi m hm)
  have h' : Tendsto (fun n ↦ 1 - subcriticalUnstructuredProbability k gamma
      (subcriticalRemainderLowerCoefficient k gamma) xi n (m n)) atTop (𝓝 1) := by
    simpa only [sub_zero] using h
  apply h'.congr'
  filter_upwards [eventually_inducedStarFreeGraphFinsetWithEdges_nonempty k hk gamma
    ⟨hgamma.1,hgamma.2.trans (gammaK_lt_one hk)⟩ m hm] with n hn
  have he := subcriticalStructuredProbability_add_unstructuredProbability k n (m n)
    gamma (subcriticalRemainderLowerCoefficient k gamma) xi hn.card_pos
  linarith

/-- Paper: Theorem `thm:main-almostall`, item `item:thm:main-almostall-sub`.
The positive linear coefficient depends only on k and gamma and precedes
both accuracy and the arbitrary asymptotic edge sequence. Every property
holds for the same exact induced decomposition. -/
theorem inducedStarSubcriticalAlmostAll (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    ∃ cLower : ℝ, 0 < cLower ∧ ∀ xi : ℝ, 0 < xi →
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        Tendsto (fun n ↦ subcriticalStructuredProbability k gamma cLower xi n (m n))
          atTop (𝓝 1) :=
  ⟨subcriticalRemainderLowerCoefficient k gamma, subcriticalRemainderLowerCoefficient_pos hk hgamma,
    fun _ hxi m hm ↦ subcriticalStructuredProbability_tendsto_one hk hgamma hxi m hm⟩

/-- Unpacking the witness gives a literal disjoint union on complementary
vertex sets, not an edit-distance conclusion. -/
theorem hasSubcriticalStructure_iff_disjointUnion {k n : ℕ} {gamma cLower xi : ℝ}
    (G : SimpleGraph (Fin n)) :
    HasSubcriticalStructure k gamma cLower xi G ↔
      ∃ U : Finset (Fin n),
        G = (G.induce (U : Set (Fin n))).spanningCoe ⊔
          (G.induce (U : Set (Fin n))ᶜ).spanningCoe ∧
        (∀ x ∈ U, ∀ y ∉ U, ¬G.Adj x y) ∧
        DenseGraph.IsCoMultipartite (G.induce (U : Set (Fin n))) (k - 1) ∧
        |(U.card : ℝ) / n - subcriticalOneBlockLength k gamma| ≤ xi ∧
        cLower * n ≤ (finiteGraphEdges (G.induce (U : Set (Fin n))ᶜ)).card ∧
        (finiteGraphEdges (G.induce (U : Set (Fin n))ᶜ)).card ≤ xi * (n : ℝ) ^ 2 := by
  constructor
  · rintro ⟨W,hW⟩
    exact ⟨W.coreVertices,W.disjointUnion,W.noCross,W.coreCoMultipartite,hW⟩
  · rintro ⟨U,_,hcross,hco,hbounds⟩
    exact ⟨⟨U,hcross,hco⟩,hbounds⟩

/-- Literal probability-one disjoint-union form of the subcritical clause.
The core size and both remainder-edge inequalities use the same set U. -/
theorem inducedStarSubcriticalAlmostAll_disjointUnion (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    ∃ cLower : ℝ, 0 < cLower ∧ ∀ xi : ℝ, 0 < xi →
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        Tendsto (fun n ↦ uniformSubfamilyProbability
          (inducedStarFreeGraphFinsetWithEdges k n (m n))
          ((inducedStarFreeGraphFinsetWithEdges k n (m n)).filter fun G ↦
            ∃ U : Finset (Fin n),
              G = (G.induce (U : Set (Fin n))).spanningCoe ⊔
                (G.induce (U : Set (Fin n))ᶜ).spanningCoe ∧
              (∀ x ∈ U, ∀ y ∉ U, ¬G.Adj x y) ∧
              DenseGraph.IsCoMultipartite (G.induce (U : Set (Fin n))) (k - 1) ∧
              |(U.card : ℝ) / n - subcriticalOneBlockLength k gamma| ≤ xi ∧
              cLower * n ≤ (finiteGraphEdges (G.induce (U : Set (Fin n))ᶜ)).card ∧
              (finiteGraphEdges (G.induce (U : Set (Fin n))ᶜ)).card ≤ xi * (n : ℝ) ^ 2))
          atTop (𝓝 1) := by
  obtain ⟨c,hc,hmain⟩ := inducedStarSubcriticalAlmostAll k hk hgamma
  refine ⟨c,hc,?_⟩
  intro xi hxi m hm
  simpa only [subcriticalStructuredProbability, subcriticalStructuredGraphFinset,
    hasSubcriticalStructure_iff_disjointUnion] using hmain xi hxi m hm

end InducedStars
