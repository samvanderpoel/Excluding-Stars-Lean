import InducedStars.Structure.Subcritical.ActiveModels

/-! # Exact realization of retained active outcomes

The base graph consists of retained cliques, the deterministic nonretained
remainder, and the selected active coordinates. Defects are toggled only
after assembling these three disjoint edge sets.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical symmDiff
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Forget the tags of the Bernoulli active coordinates. -/
def subcriticalActiveSelectedEdges {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} {mvec : RetainedEdgeCountVector D eta R₀}
    (S : Finset (subcriticalActiveFixedBlockModel mvec).Coordinate) : Finset (Sym2 V) :=
  S.image (fun e ↦ e.2.1)

theorem subcriticalActiveSelectedEdges_subset {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} {mvec : RetainedEdgeCountVector D eta R₀}
    (S : Finset (subcriticalActiveFixedBlockModel mvec).Coordinate) :
    subcriticalActiveSelectedEdges S ⊆ retainedActiveEdgeUniverse D eta R₀ := by
  intro z hz
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hz
  exact (mem_retainedActiveEdgeUniverse D eta R₀ e.2.1).mpr ⟨e.1, e.2.2⟩

theorem subcriticalActiveSelectedEdges_sample_eq {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} {mvec : RetainedEdgeCountVector D eta R₀}
    (S : (subcriticalActiveFixedBlockModel mvec).Sample) :
    subcriticalActiveSelectedEdges ((subcriticalActiveFixedBlockModel mvec).sampleOutcome S) =
      Finset.univ.biUnion ((subcriticalActiveFixedBlockModel mvec).selectedInBlock S) := by
  ext z
  simp only [subcriticalActiveSelectedEdges, Finset.mem_image,
    DenseGraph.FixedCardinalityBlockModel.mem_sampleOutcome,
    Finset.mem_biUnion, Finset.mem_univ, true_and,
    DenseGraph.FixedCardinalityBlockModel.selectedInBlock, Finset.mem_map]
  constructor
  · rintro ⟨⟨i, e⟩, he, rfl⟩; exact ⟨i, e, he, rfl⟩
  · rintro ⟨i, e, he, rfl⟩; exact ⟨⟨i, e⟩, he, rfl⟩

theorem subcriticalActiveSelectedEdges_sample_card {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} {mvec : RetainedEdgeCountVector D eta R₀}
    (S : (subcriticalActiveFixedBlockModel mvec).Sample) :
    (subcriticalActiveSelectedEdges
      ((subcriticalActiveFixedBlockModel mvec).sampleOutcome S)).card =
      retainedEdgeCountTotal mvec := by
  rw [subcriticalActiveSelectedEdges_sample_eq, Finset.card_biUnion]
  · simp only [DenseGraph.FixedCardinalityBlockModel.card_selectedInBlock]
    rfl
  · intro e _ f _ hef
    exact (retainedActivePotentialEdges_disjoint D eta R₀ hef).mono
      ((subcriticalActiveFixedBlockModel mvec).selectedInBlock_subset S e)
      ((subcriticalActiveFixedBlockModel mvec).selectedInBlock_subset S f)

/-- Realization from an arbitrary active edge subset, before choosing a law. -/
def subcriticalGraphFromActiveEdges {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (A : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet
    (((retainedCliquePotentialEdges D eta R₀ ∪
      finiteGraphEdges (subcriticalRemainderGraphSpanningCoe H) ∪ A) ∆
        finiteGraphEdges T : Finset (Sym2 V)) : Set (Sym2 V))

@[simp] theorem subcriticalGraphFromActiveEdges_adj {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (A : Finset (Sym2 V)) (x y : V) :
    (subcriticalGraphFromActiveEdges H T A).Adj x y ↔
      ((s(x, y) ∈ retainedCliquePotentialEdges D eta R₀ ∨
        (subcriticalRemainderGraphSpanningCoe H).Adj x y ∨ s(x, y) ∈ A) ≠
          T.Adj x y) ∧ x ≠ y := by
  simp only [subcriticalGraphFromActiveEdges, SimpleGraph.fromEdgeSet_adj,
    Finset.mem_coe, Finset.mem_symmDiff, Finset.mem_union, mk_mem_finiteGraphEdges]
  tauto

set_option maxHeartbeats 800000 in
/-- The edge-set extensionality proof expands several dependent finite universes. -/
theorem subcriticalGraphFromActiveEdges_edges {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) {A : Finset (Sym2 V)}
    (hA : A ⊆ retainedActiveEdgeUniverse D eta R₀) :
    finiteGraphEdges (subcriticalGraphFromActiveEdges H T A) =
      (retainedCliquePotentialEdges D eta R₀ ∪
        finiteGraphEdges (subcriticalRemainderGraphSpanningCoe H) ∪ A) ∆
          finiteGraphEdges T := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    have hneA (h : s(x, y) ∈ A) : x ≠ y := by
      intro heq
      subst y
      exact D.not_activePair_self x
        ((mk_mem_retainedActiveEdgeUniverse_iff D eta R₀ x x).mp (hA h)).1
    have hneC (h : s(x, y) ∈ retainedCliquePotentialEdges D eta R₀) : x ≠ y :=
      ((mk_mem_retainedCliquePotentialEdges_iff D eta R₀ x y).mp h).1
    simp only [mk_mem_finiteGraphEdges, subcriticalGraphFromActiveEdges_adj,
      Finset.mem_symmDiff, Finset.mem_union]
    have hneH : (subcriticalRemainderGraphSpanningCoe H).Adj x y → x ≠ y := SimpleGraph.Adj.ne
    have hneT : T.Adj x y → x ≠ y := SimpleGraph.Adj.ne
    tauto

/-- The binomial and fixed laws use exactly the same deterministic realization. -/
def subcriticalActiveBernoulliGraphFromOutcome {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) {mvec : RetainedEdgeCountVector D eta R₀}
    (S : Finset (subcriticalActiveFixedBlockModel mvec).Coordinate) : SimpleGraph V :=
  subcriticalGraphFromActiveEdges H T (subcriticalActiveSelectedEdges S)

def subcriticalActiveGraphFromOutcome {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) {mvec : RetainedEdgeCountVector D eta R₀}
    (S : (subcriticalActiveFixedBlockModel mvec).Sample) : SimpleGraph V :=
  subcriticalActiveBernoulliGraphFromOutcome H T
    ((subcriticalActiveFixedBlockModel mvec).sampleOutcome S)

theorem subcriticalRemainderEdges_subset {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀) :
    finiteGraphEdges (subcriticalRemainderGraphSpanningCoe H) ⊆
      nonretainedPotentialEdges D eta R₀ := by
  intro z hz
  induction z using Sym2.inductionOn with
  | _ x y =>
    have hg := (mk_mem_finiteGraphEdges _ x y).mp hz
    exact (mk_mem_nonretainedPotentialEdges_iff D eta R₀ x y).mpr
      ⟨(subcriticalRemainderGraphSpanningCoe_support H hg).1,
        (subcriticalRemainderGraphSpanningCoe_support H hg).2, hg.ne⟩

/-- Exact integer edge count; no truncated subtraction is used. -/
theorem subcriticalGraphFromActiveEdges_card {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    {A : Finset (Sym2 V)} (hA : A ⊆ retainedActiveEdgeUniverse D eta R₀) :
    ((finiteGraphEdges (subcriticalGraphFromActiveEdges H T A)).card : ℤ) =
      (retainedCliqueCapacity D eta R₀ : ℤ) + A.card + (finiteGraphEdges H).card +
        subcriticalSignedDefectSize D eta R₀ T := by
  let C := retainedCliquePotentialEdges D eta R₀
  let F := finiteGraphEdges (subcriticalRemainderGraphSpanningCoe H)
  let B := C ∪ F ∪ A
  let Q := finiteGraphEdges T
  have hCF : Disjoint C F :=
    (retainedCliquePotentialEdges_disjoint_nonretained D eta R₀).mono
      (Finset.Subset.refl C) (subcriticalRemainderEdges_subset H)
  have hCA : Disjoint C A :=
    (retainedCliquePotentialEdges_disjoint_active D eta R₀).mono
      (Finset.Subset.refl C) hA
  have hFA : Disjoint F A :=
    (retainedActiveEdgeUniverse_disjoint_nonretained D eta R₀).symm.mono
      (subcriticalRemainderEdges_subset H) hA
  have hQB : Q ∩ B = Q ∩ C := by
    have hQF : Disjoint Q F := hT.disjoint_nonretained.mono
      (Finset.Subset.refl Q) (subcriticalRemainderEdges_subset H)
    have hQA : Disjoint Q A := hT.disjoint_active.mono (Finset.Subset.refl Q) hA
    ext z
    have hhF : z ∈ Q → z ∉ F := fun hq hf ↦ Finset.disjoint_left.mp hQF hq hf
    have hhA : z ∈ Q → z ∉ A := fun hq ha ↦ Finset.disjoint_left.mp hQA hq ha
    simp only [B, Finset.mem_inter, Finset.mem_union]
    tauto
  have hB : B.card = C.card + F.card + A.card := by
    dsimp only [B]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hCA, hFA⟩),
      Finset.card_union_of_disjoint hCF]
  have hsym : (B ∆ Q).card = (B \ Q).card + (Q \ B).card := by
    rw [symmDiff_def]
    change ((B \ Q) ∪ (Q \ B)).card = _
    rw [Finset.card_union_of_disjoint]
    exact Finset.disjoint_left.mpr (fun z hz hq ↦ (Finset.mem_sdiff.mp hz).2
      (Finset.mem_sdiff.mp hq).1)
  have h1 := Finset.card_sdiff_add_card_inter B Q
  have h2 := Finset.card_sdiff_add_card_inter Q B
  rw [Finset.inter_comm B Q, hQB] at h1
  rw [hQB] at h2
  rw [subcriticalGraphFromActiveEdges_edges H T hA]
  change ((B ∆ Q).card : ℤ) = _
  rw [hsym]
  have hC := retainedCliquePotentialEdges_card D eta R₀
  have hF := subcriticalRemainderGraphSpanningCoe_card H
  change C.card = _ at hC
  change F.card = _ at hF
  change (_ : ℤ) = (retainedCliqueCapacity D eta R₀ : ℤ) + A.card +
    (finiteGraphEdges H).card + ((Q.card : ℤ) - 2 * ((Q ∩ C).card : ℤ))
  omega

theorem subcriticalActiveGraphFromOutcome_card {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    {mvec : RetainedEdgeCountVector D eta R₀}
    (S : (subcriticalActiveFixedBlockModel mvec).Sample) :
    ((finiteGraphEdges (subcriticalActiveGraphFromOutcome H T S)).card : ℤ) =
      (retainedCliqueCapacity D eta R₀ : ℤ) + retainedEdgeCountTotal mvec +
        (finiteGraphEdges H).card + subcriticalSignedDefectSize D eta R₀ T := by
  simpa only [subcriticalActiveGraphFromOutcome, subcriticalActiveBernoulliGraphFromOutcome,
    subcriticalActiveSelectedEdges_sample_card] using
    subcriticalGraphFromActiveEdges_card H T hT
      (subcriticalActiveSelectedEdges_subset ((subcriticalActiveFixedBlockModel mvec).sampleOutcome S))

theorem subcriticalActiveGraphFromOutcome_card_of_mem_level
    {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ} {u : ℤ}
    (H : SubcriticalRemainderGraph D eta R₀) (T : SimpleGraph V)
    (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    {mvec : RetainedEdgeCountVector D eta R₀}
    (hmvec : mvec ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u)
    (hu : u = (finiteGraphEdges H).card + subcriticalSignedDefectSize D eta R₀ T)
    (S : (subcriticalActiveFixedBlockModel mvec).Sample) :
    (finiteGraphEdges (subcriticalActiveGraphFromOutcome H T S)).card = m := by
  have hcard := subcriticalActiveGraphFromOutcome_card H T hT S
  have hlevel := (mem_retainedNarrowEdgeCountLevel.mp hmvec).1
  omega

end InducedStars
