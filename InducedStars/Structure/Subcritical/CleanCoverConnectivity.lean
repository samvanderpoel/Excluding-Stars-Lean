import InducedStars.Structure.Subcritical.CleanCoverProbability

/-!
# Deterministic connectivity of positive fixed-cell samples

All parts are cliques. A positive quota between every distinct pair of parts
already makes the support connected, without any probabilistic estimate.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem fixedProfileCleanGraph_adj_iff_selected (D : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) (S : (supercriticalFixedProfileBlockModel D p).Sample)
    (e : SupercriticalPartPair k) (xy : V × V)
    (hxy : xy ∈ D.parts e.left ×ˢ D.parts e.right) :
    (fixedProfileCleanGraph D p S).Adj xy.1 xy.2 ↔
      xy ∈ (supercriticalFixedProfileBlockModel D p).selectedInBlock S e := by
  let M := supercriticalFixedProfileBlockModel D p
  let z : M.Coordinate := ⟨e, ⟨xy, hxy⟩⟩
  have hcross : D.IsCrossPair xy.1 xy.2 := ⟨e, Or.inl (Finset.mem_product.mp hxy)⟩
  rw [fixedProfileCleanGraph, supercriticalGraphFromCrossOutcome_adj_of_cross D ⊥ p _ hcross]
  change supercriticalProfileCoordinateSym2 D p z ∈
    supercriticalProfileAmbientOutcome D p (M.sampleOutcome S) ↔ _
  rw [mem_supercriticalProfileAmbientOutcome, M.mem_sampleOutcome]
  constructor
  · intro hz
    exact Finset.mem_map.mpr ⟨z.2, hz, rfl⟩
  · rintro h
    obtain ⟨w, hw, hwz⟩ := Finset.mem_map.mp h
    have heq : w = z.2 := Subtype.ext hwz
    simpa only [heq] using hw

theorem fixedProfileCleanGraph_interedges (D : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) (S : (supercriticalFixedProfileBlockModel D p).Sample)
    (e : SupercriticalPartPair k) :
    (fixedProfileCleanGraph D p S).interedges (D.parts e.left) (D.parts e.right) =
      (supercriticalFixedProfileBlockModel D p).selectedInBlock S e := by
  ext xy
  rw [SimpleGraph.mem_interedges_iff]
  constructor
  · rintro ⟨hx, hy, h⟩
    exact (fixedProfileCleanGraph_adj_iff_selected D p S e xy
      (Finset.mem_product.mpr ⟨hx, hy⟩)).mp h
  · intro h
    have hxy := (supercriticalFixedProfileBlockModel D p).selectedInBlock_subset S e h
    exact ⟨(Finset.mem_product.mp hxy).1, (Finset.mem_product.mp hxy).2,
      (fixedProfileCleanGraph_adj_iff_selected D p S e xy hxy).mpr h⟩

theorem fixedProfileCleanGraph_profile (D : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) (S : (supercriticalFixedProfileBlockModel D p).Sample) :
    crossEdgeProfile (fixedProfileCleanGraph D p S) D = p := by
  apply SupercriticalEdgeProfile.ext
  funext e
  rw [crossEdgeProfile_count, fixedProfileCleanGraph_interedges,
    DenseGraph.FixedCardinalityBlockModel.card_selectedInBlock]
  rfl

theorem fixedProfileCleanGraph_injective (D : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) : Function.Injective (fixedProfileCleanGraph D p) := by
  intro S T h
  apply (supercriticalFixedProfileBlockModel D p).selectedInBlock_injective
  funext e
  dsimp only
  rw [← fixedProfileCleanGraph_interedges, ← fixedProfileCleanGraph_interedges, h]

theorem SupercriticalDivision.connected_of_clique_cross_nonempty
    (D : SupercriticalDivision k V) (hk : 2 ≤ k) (hD : D.IsFull)
    (G : SimpleGraph V) (hclique : ∀ i, G.IsClique (D.parts i : Set V))
    (hcross : ∀ i j, i ≠ j → ∃ x ∈ D.parts i, ∃ y ∈ D.parts j, G.Adj x y) :
    G.Connected := by
  have hwithin (i) {x y : V} (hx : x ∈ D.parts i) (hy : y ∈ D.parts i) :
      G.Reachable x y := by
    by_cases h : x = y
    · subst y
      exact SimpleGraph.Reachable.rfl
    · exact (hclique i hx hy h).reachable
  apply (SimpleGraph.connected_iff G).mpr
  constructor
  · intro x y
    obtain ⟨i, hi⟩ := D.mem_support.mp (show x ∈ D.support by rw [D.support_eq_univ hD]; simp)
    obtain ⟨j, hj⟩ := D.mem_support.mp (show y ∈ D.support by rw [D.support_eq_univ hD]; simp)
    by_cases hij : i = j
    · subst j
      exact hwithin i hi hj
    · obtain ⟨u, hu, v, hv, huv⟩ := hcross i j hij
      exact (hwithin i hi hu).trans (huv.reachable.trans (hwithin j hv hj))
  · obtain ⟨x, _⟩ := D.parts_nonempty ⟨0, by omega⟩
    exact ⟨x⟩

theorem fixedProfileCleanGraph_adj_of_selected (D : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) (S : (supercriticalFixedProfileBlockModel D p).Sample)
    (e : SupercriticalPartPair k) (xy : V × V)
    (hxy : xy ∈ (supercriticalFixedProfileBlockModel D p).selectedInBlock S e) :
    (fixedProfileCleanGraph D p S).Adj xy.1 xy.2 := by
  obtain ⟨z, hz, hze⟩ := Finset.mem_map.mp hxy
  have hval : z.val = xy := hze
  subst xy
  let c : (supercriticalFixedProfileBlockModel D p).Coordinate := ⟨e, z⟩
  have hc : c ∈ (supercriticalFixedProfileBlockModel D p).sampleOutcome S :=
    (supercriticalFixedProfileBlockModel D p).mem_sampleOutcome S c |>.mpr hz
  have hselected := (mem_supercriticalProfileAmbientOutcome D p _ c).mpr hc
  apply (supercriticalGraphFromCrossOutcome_adj D ⊥ p _ _ _).mpr
  exact Or.inl hselected

theorem fixedProfileCleanGraph_connected (D : SupercriticalDivision k V)
    (hk : 2 ≤ k) (p : SupercriticalEdgeProfile D) (hD : D.IsFull)
    (hquota : ∀ e, 0 < p.count e) (S : (supercriticalFixedProfileBlockModel D p).Sample) :
    (fixedProfileCleanGraph D p S).Connected := by
  apply D.connected_of_clique_cross_nonempty hk hD _ (fixedProfileCleanGraph_isClique D p S)
  have hpair (e : SupercriticalPartPair k) :
      ∃ x ∈ D.parts e.left, ∃ y ∈ D.parts e.right, (fixedProfileCleanGraph D p S).Adj x y := by
    have hcard : 0 < ((supercriticalFixedProfileBlockModel D p).selectedInBlock S e).card := by
      rw [DenseGraph.FixedCardinalityBlockModel.card_selectedInBlock]
      exact hquota e
    obtain ⟨xy, hxy⟩ := Finset.card_pos.mp hcard
    have hmem := (supercriticalFixedProfileBlockModel D p).selectedInBlock_subset S e hxy
    have hp := Finset.mem_product.mp hmem
    exact ⟨xy.1, hp.1, xy.2, hp.2, fixedProfileCleanGraph_adj_of_selected D p S e xy hxy⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hpair ⟨i, j, h⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := hpair ⟨j, i, h⟩
    exact ⟨y, hy, x, hx, hxy.symm⟩

end InducedStars
