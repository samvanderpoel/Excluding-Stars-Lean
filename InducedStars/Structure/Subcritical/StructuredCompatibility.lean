import InducedStars.Structure.Subcritical.RetainedCleanStructure
import InducedStars.Structure.Subcritical.CleanMultiplicityGeometry

/-!
# Structural bounds from clean one-block compatibility

The component size, the exact separation, and both remainder-edge bounds
refer to one and the same induced decomposition. This deterministic adapter
contains no probabilistic or asymptotic assumption.
-/

noncomputable section
open Finset Set
namespace InducedStars

/-- The final finite structural event follows from a clean compatible
division and simultaneous upper/lower edge bounds on its actual remainder.
The lower coefficient is not selected from the accuracy parameter. -/
theorem hasSubcriticalStructure_of_oneBlock_compatibility
    {k n R₀ : ℕ} (hk : 3 ≤ k) {gamma eta delta cLower xi : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
    (C : D.CandidateCompatibility
      (subcriticalDistinguishedBlockSequence k hk gamma hgamma) eta delta R₀)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (hsize : eta + delta ≤ subcriticalOneBlockLength k gamma)
    (hR : k - 1 ≤ R₀) (hn : 0 < n) (haccuracy : delta ≤ xi)
    (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥)
    (hlower : cLower * n ≤ (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card)
    (hupper : (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card ≤ xi * (n : ℝ) ^ 2) :
    HasSubcriticalStructure k gamma cLower xi G := by
  classical
  let mu := subcriticalOneBlockLength k gamma
  have hmu : 0 < mu := subcriticalOneBlockLength_pos hk hgamma.1
  have hmuOne : mu ≤ 1 := (subcriticalOneBlockLength_lt_one hk hgamma.2).le
  change D.CandidateCompatibility (oneBlockSequence k hk mu hmu hmuOne) eta delta R₀ at C
  have hcount := C.oneBlock_retainedComponentIndices_card_eq_one hk hmu hmuOne
    heta hdelta hsize hR
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcount
  have hiret : i ∈ D.retainedComponentIndices eta R₀ := by rw [hi]; simp
  have hic : i ∈ D.compatibilityComponentIndices eta R₀ := by
    have h := (D.mem_retainedComponentIndices eta R₀ i).mp hiret
    apply (D.mem_compatibilityComponentIndices eta R₀ i).mpr
    refine ⟨?_, h.2⟩
    have he : 0 ≤ eta * (Fintype.card (Fin n) : ℝ) := mul_nonneg heta (Nat.cast_nonneg _)
    linarith
  have hcore := C.oneBlock_core_eq_complete hk hmu hmuOne i hic
  have horder : (D.core i).order = k - 1 := by rw [hcore]; rfl
  let W := subcriticalStructureWitness_of_incidentClean hclean i hiret horder
  have hret : D.retainedVertices eta R₀ = D.componentSupport i := by
    simp only [SubcriticalDivision.retainedVertices, hi, Finset.singleton_biUnion]
  have hremset : ({v : Fin n | v ∉ D.componentSupport i} : Set (Fin n)) =
      (D.nonretainedVertices eta R₀ : Set (Fin n)) := by
    ext v
    simp only [Finset.mem_coe, D.mem_nonretainedVertices, hret, Set.mem_setOf_eq]
  have hremcount : W.remainderEdgeCount =
      (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card := by
    exact congrArg (fun S : Set (Fin n) ↦ (finiteGraphEdges (G.induce S)).card) hremset
  have hsizeError := C.oneBlock_component_size_error hk hmu hmuOne i hic
  simp only [Fintype.card_fin] at hsizeError
  refine ⟨W, ?_, ?_, ?_⟩
  · change |((D.componentSupport i).card : ℝ) / n - mu| ≤ xi
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hratio : |((D.componentSupport i).card : ℝ) / n - mu| =
        |((D.componentSupport i).card : ℝ) - mu * n| / n := by
      rw [show ((D.componentSupport i).card : ℝ) / n - mu =
        (((D.componentSupport i).card : ℝ) - mu * n) / n by field_simp]
      rw [abs_div, abs_of_pos hnR]
    rw [hratio]
    exact ((div_le_iff₀ hnR).mpr hsizeError).trans haccuracy
  · rwa [hremcount]
  · rwa [hremcount]

end InducedStars
