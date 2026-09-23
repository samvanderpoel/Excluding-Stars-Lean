import InducedStars.Structure.Supercritical.MediumRefinement
import InducedStars.Structure.Supercritical.MediumDensity
import Mathlib.Tactic

/-!
# Tagged Bernoulli outcomes for the supercritical medium family

The exact-size block model and its associated Bernoulli product use tagged
coordinates.  This file identifies those coordinates with the unordered
cross edges they represent, constructs the single global complementation
and connects tagged Bernoulli outcomes to the graph-valued
outcomes used by the refined-family count.
-/

noncomputable section

open Finset Set

namespace InducedStars

/-! ## Tagged coordinates as unordered graph edges -/

/-- The unordered graph edge represented by one tagged sampled-block
coordinate. -/
def supercriticalMediumCoordinateSym2
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (c : (supercriticalMediumFixedModel w).Coordinate) : Sym2 (Fin n) :=
  s(c.2.1.1, c.2.1.2)

/-- The increasing part orientation makes the tagged-coordinate map
injective.  In particular, no unordered cross edge is sampled twice. -/
theorem supercriticalMediumCoordinateSym2_injective
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Function.Injective (supercriticalMediumCoordinateSym2 w) := by
  classical
  rintro ⟨e, xy⟩ ⟨f, uv⟩ h
  have hxy := (mem_supercriticalMediumCrossBlock w e xy.1).mp xy.2
  have huv := (mem_supercriticalMediumCrossBlock w f uv.1).mp uv.2
  rcases Sym2.eq_iff.mp h with hstraight | hswap
  · have hx : xy.1.1 = uv.1.1 := hstraight.1
    have hy : xy.1.2 = uv.1.2 := hstraight.2
    have hleft : e.left = f.left := D.mem_part_unique
      (supercriticalMediumSampledPart_subset w _ hxy.1)
      (supercriticalMediumSampledPart_subset w _ (hx ▸ huv.1))
    have hright : e.right = f.right := D.mem_part_unique
      (supercriticalMediumSampledPart_subset w _ hxy.2)
      (supercriticalMediumSampledPart_subset w _ (hy ▸ huv.2))
    have hef : e = f := SupercriticalPartPair.ext hleft hright
    subst f
    have hxyuv : xy = uv := Subtype.ext (Prod.ext hx hy)
    subst uv
    rfl
  · have hx : xy.1.1 = uv.1.2 := hswap.1
    have hy : xy.1.2 = uv.1.1 := hswap.2
    have hleft : e.left = f.right := D.mem_part_unique
      (supercriticalMediumSampledPart_subset w _ hxy.1)
      (supercriticalMediumSampledPart_subset w _ (hx ▸ huv.2))
    have hright : e.right = f.left := D.mem_part_unique
      (supercriticalMediumSampledPart_subset w _ hxy.2)
      (supercriticalMediumSampledPart_subset w _ (hy ▸ huv.1))
    have hbad : f.right < f.left := by
      simpa [hleft, hright] using e.left_lt_right
    exact (lt_asymm f.left_lt_right hbad).elim

/-- Embedding form of `supercriticalMediumCoordinateSym2`. -/
def supercriticalMediumCoordinateEmbedding
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (supercriticalMediumFixedModel w).Coordinate ↪ Sym2 (Fin n) :=
  ⟨supercriticalMediumCoordinateSym2 w,
    supercriticalMediumCoordinateSym2_injective w⟩

/-- Every unordered pair in a sampled cross block has a unique tagged
coordinate representing it. -/
theorem exists_unique_supercriticalMediumCoordinate_of_sampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) {x y : Fin n}
    (hxy : supercriticalMediumIsSampledCrossPair w x y) :
    ∃! c : (supercriticalMediumFixedModel w).Coordinate,
      supercriticalMediumCoordinateSym2 w c = s(x, y) := by
  classical
  obtain ⟨e, h | h⟩ := hxy
  · let c : (supercriticalMediumFixedModel w).Coordinate :=
      ⟨e, ⟨(x, y), h⟩⟩
    have hc : supercriticalMediumCoordinateSym2 w c = s(x, y) := rfl
    refine ⟨c, hc, ?_⟩
    intro d hd
    exact supercriticalMediumCoordinateSym2_injective w (hd.trans hc.symm)
  · let c : (supercriticalMediumFixedModel w).Coordinate :=
      ⟨e, ⟨(y, x), h⟩⟩
    have hc : supercriticalMediumCoordinateSym2 w c = s(x, y) := by
      simp [c, supercriticalMediumCoordinateSym2]
    refine ⟨c, hc, ?_⟩
    intro d hd
    exact supercriticalMediumCoordinateSym2_injective w (hd.trans hc.symm)

/-- The tagged coordinate represented by a sampled unordered cross pair. -/
noncomputable def supercriticalMediumCoordinateOfSampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (x y : Fin n)
    (hxy : supercriticalMediumIsSampledCrossPair w x y) :
    (supercriticalMediumFixedModel w).Coordinate :=
  Classical.choose
    (exists_unique_supercriticalMediumCoordinate_of_sampled w hxy)

@[simp] theorem supercriticalMediumCoordinateOfSampled_spec
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (x y : Fin n)
    (hxy : supercriticalMediumIsSampledCrossPair w x y) :
    supercriticalMediumCoordinateSym2 w
        (supercriticalMediumCoordinateOfSampled w x y hxy) = s(x, y) :=
  (Classical.choose_spec
    (exists_unique_supercriticalMediumCoordinate_of_sampled w hxy)).1

/-- Forget the block tags in a Bernoulli outcome. -/
def supercriticalMediumAmbientOutcome
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate) :
    Finset (Sym2 (Fin n)) :=
  outcome.map (supercriticalMediumCoordinateEmbedding w)

@[simp] theorem mem_supercriticalMediumAmbientOutcome
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate)
    (c : (supercriticalMediumFixedModel w).Coordinate) :
    supercriticalMediumCoordinateSym2 w c ∈
        supercriticalMediumAmbientOutcome w outcome ↔ c ∈ outcome := by
  classical
  simp [supercriticalMediumAmbientOutcome,
    supercriticalMediumCoordinateEmbedding]

/-! ## Graphs from arbitrary tagged outcomes -/

/-- A sampled unordered pair is selected by a tagged Boolean-cube outcome. -/
def supercriticalMediumIsSelectedTaggedPair
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate)
    (x y : Fin n) : Prop :=
  s(x, y) ∈ supercriticalMediumAmbientOutcome w outcome

theorem supercriticalMediumIsSelectedTaggedPair_comm
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate)
    (x y : Fin n) :
    supercriticalMediumIsSelectedTaggedPair w outcome x y ↔
      supercriticalMediumIsSelectedTaggedPair w outcome y x := by
  simp only [supercriticalMediumIsSelectedTaggedPair, Sym2.eq_swap]

theorem supercriticalMediumIsSelectedTaggedPair_isSampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate)
    {x y : Fin n}
    (hxy : supercriticalMediumIsSelectedTaggedPair w outcome x y) :
    supercriticalMediumIsSampledCrossPair w x y := by
  classical
  rw [supercriticalMediumIsSelectedTaggedPair,
    supercriticalMediumAmbientOutcome, Finset.mem_map] at hxy
  obtain ⟨c, _hc, hcxy⟩ := hxy
  rcases c with ⟨e, uv⟩
  have huv := (mem_supercriticalMediumCrossBlock w e uv.1).mp uv.2
  rcases Sym2.eq_iff.mp hcxy with h | h
  · exact ⟨e, Or.inl ((mem_supercriticalMediumCrossBlock w e (x, y)).2
      ⟨h.1 ▸ huv.1, h.2 ▸ huv.2⟩)⟩
  · exact ⟨e, Or.inr ((mem_supercriticalMediumCrossBlock w e (y, x)).2
      ⟨h.1 ▸ huv.1, h.2 ▸ huv.2⟩)⟩

theorem supercriticalMediumIsSelectedTaggedPair_iff_coordinate_mem
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate)
    {x y : Fin n} (hxy : supercriticalMediumIsSampledCrossPair w x y) :
    supercriticalMediumIsSelectedTaggedPair w outcome x y ↔
      supercriticalMediumCoordinateOfSampled w x y hxy ∈ outcome := by
  classical
  let c := supercriticalMediumCoordinateOfSampled w x y hxy
  have hc : supercriticalMediumCoordinateSym2 w c = s(x, y) := by
    simpa [c] using supercriticalMediumCoordinateOfSampled_spec w x y hxy
  constructor
  · intro h
    rw [supercriticalMediumIsSelectedTaggedPair,
      supercriticalMediumAmbientOutcome, Finset.mem_map] at h
    obtain ⟨d, hd, hdc⟩ := h
    have hdc' : supercriticalMediumCoordinateSym2 w d =
        supercriticalMediumCoordinateSym2 w c := hdc.trans hc.symm
    have hdcEq : d = c := supercriticalMediumCoordinateSym2_injective w hdc'
    simpa [c, hdcEq] using hd
  · intro h
    rw [supercriticalMediumIsSelectedTaggedPair, ← hc]
    exact (mem_supercriticalMediumAmbientOutcome w outcome c).2 (by simpa [c] using h)

/-! ## Global complementation on the tagged coordinate space -/

/-- The pullback of the single global orientation to the tagged
cross-edge coordinate space. -/
def supercriticalMediumTaggedGlobalFlipSet
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Finset (supercriticalMediumFixedModel w).Coordinate := by
  classical
  exact Finset.univ.filter fun c ↦
    ¬mediumSuccessPresent w (supercriticalMediumCoordinateSym2 w c)

@[simp] theorem mem_supercriticalMediumTaggedGlobalFlipSet
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (c : (supercriticalMediumFixedModel w).Coordinate) :
    c ∈ supercriticalMediumTaggedGlobalFlipSet w ↔
      ¬mediumSuccessPresent w (supercriticalMediumCoordinateSym2 w c) := by
  classical
  simp [supercriticalMediumTaggedGlobalFlipSet]

/-- The associated block-Bernoulli model after the one global orientation. -/
def supercriticalMediumOrientedBernoulliModel
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :=
  (supercriticalMediumBernoulliModel w).complementCoordinates
    (supercriticalMediumTaggedGlobalFlipSet w)

/-- Replace precisely the sampled cross blocks of the exemplar by an
arbitrary tagged Boolean-cube outcome. -/
def supercriticalMediumTaggedOutcomeGraph
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y ↦
    supercriticalMediumIsSelectedTaggedPair w outcome x y ∨
      (¬supercriticalMediumIsSampledCrossPair w x y ∧ G.Adj x y)

@[simp] theorem supercriticalMediumTaggedOutcomeGraph_adj
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate)
    (x y : Fin n) :
    (supercriticalMediumTaggedOutcomeGraph w outcome).Adj x y ↔
      supercriticalMediumIsSelectedTaggedPair w outcome x y ∨
        (¬supercriticalMediumIsSampledCrossPair w x y ∧ G.Adj x y) := by
  rw [supercriticalMediumTaggedOutcomeGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rcases h with h | h
      · exact Or.inl
          ((supercriticalMediumIsSelectedTaggedPair_comm w outcome y x).mp h)
      · exact Or.inr ⟨fun hxy ↦ h.1
          ((supercriticalMediumIsSampledCrossPair_comm w x y).mp hxy),
          (G.adj_comm y x).mp h.2⟩
  · intro h
    have hne : x ≠ y := by
      rcases h with h | h
      · exact supercriticalMediumIsSampledCrossPair_ne w
          (supercriticalMediumIsSelectedTaggedPair_isSampled w outcome h)
      · exact G.ne_of_adj h.2
    exact ⟨hne, Or.inl h⟩

theorem supercriticalMediumTaggedOutcomeGraph_adj_of_sampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate)
    {x y : Fin n} (hxy : supercriticalMediumIsSampledCrossPair w x y) :
    (supercriticalMediumTaggedOutcomeGraph w outcome).Adj x y ↔
      supercriticalMediumIsSelectedTaggedPair w outcome x y := by
  rw [supercriticalMediumTaggedOutcomeGraph_adj]
  tauto

theorem supercriticalMediumTaggedOutcomeGraph_adj_of_not_sampled
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate)
    {x y : Fin n} (hxy : ¬supercriticalMediumIsSampledCrossPair w x y) :
    (supercriticalMediumTaggedOutcomeGraph w outcome).Adj x y ↔ G.Adj x y := by
  rw [supercriticalMediumTaggedOutcomeGraph_adj]
  constructor
  · rintro (h | h)
    · exact (hxy
        (supercriticalMediumIsSelectedTaggedPair_isSampled w outcome h)).elim
    · exact h.2
  · exact fun h ↦ Or.inr ⟨hxy, h⟩

/-! ## Candidate roles in the tagged coordinate space -/

theorem supercriticalMediumN_subset_sampledPart
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    supercriticalMediumN w ⊆ supercriticalMediumSampledPart w w.part := by
  classical
  intro x hx
  rw [supercriticalMediumSampledPart_distinguished]
  by_cases hv : w.vertex ∈ D.parts w.part
  · rw [if_pos hv, Finset.mem_erase]
    have hx' : x ∈ D.parts w.part ∧ x ≠ w.vertex ∧
        ¬G.Adj w.vertex x := by
      simpa [supercriticalMediumN, hv] using hx
    exact ⟨hx'.2.1, hx'.1⟩
  · rw [if_neg hv]
    exact supercriticalMediumN_subset_part w hx

theorem supercriticalMediumZ_subset_sampledPart
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    supercriticalMediumZ w ⊆ supercriticalMediumSampledPart w w.part := by
  classical
  intro x hx
  rw [supercriticalMediumSampledPart_distinguished]
  by_cases hv : w.vertex ∈ D.parts w.part
  · rw [if_pos hv, Finset.mem_erase]
    have hx' : x ∈ D.parts w.part ∧ G.Adj w.vertex x := by
      simpa [supercriticalMediumZ, hv] using hx
    exact ⟨(G.ne_of_adj hx'.2).symm, hx'.1⟩
  · rw [if_neg hv]
    exact supercriticalMediumZ_subset_part w hx

theorem supercriticalMediumCandidate_center_mem_sampledPart
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    K.embedding mediumCenterIndex ∈
      supercriticalMediumSampledPart w w.part := by
  classical
  by_cases hv : w.vertex ∈ D.parts w.part
  · rw [K.embedding_center, if_pos hv]
    exact supercriticalMediumZ_subset_sampledPart w K.z_mem
  · rw [K.embedding_center, if_neg hv]
    exact supercriticalMediumN_subset_sampledPart w K.x_mem

theorem supercriticalMediumCandidate_companion_mem_sampledPart
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    K.embedding (mediumCompanionIndex hk) ∈
      supercriticalMediumSampledPart w w.part := by
  classical
  by_cases hv : w.vertex ∈ D.parts w.part
  · rw [K.embedding_companion, if_pos hv]
    exact supercriticalMediumN_subset_sampledPart w K.x_mem
  · rw [K.embedding_companion, if_neg hv]
    exact supercriticalMediumZ_subset_sampledPart w K.z_mem

theorem supercriticalMediumCandidate_other_mem_sampledPart
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) (r : Fin (k - 2)) :
    K.embedding (mediumOtherLeafIndex hk r) ∈
      supercriticalMediumSampledPart w
        (otherSupercriticalPartEquiv hk w.part r) := by
  rw [K.embedding_other,
    supercriticalMediumSampledPart_of_ne w
      (otherSupercriticalPartEquiv_ne hk w.part r)]
  exact supercriticalMediumOtherN_subset_part w _ (K.y_mem r)

theorem supercriticalMediumIsSampledCrossPair_of_mem_sampledParts
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    {i j : Fin (k - 1)} {x y : Fin n}
    (hij : i ≠ j)
    (hx : x ∈ supercriticalMediumSampledPart w i)
    (hy : y ∈ supercriticalMediumSampledPart w j) :
    supercriticalMediumIsSampledCrossPair w x y := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨⟨i, j, hij⟩, Or.inl
      ((mem_supercriticalMediumCrossBlock w ⟨i, j, hij⟩ (x, y)).2
        ⟨hx, hy⟩)⟩
  · exact ⟨⟨j, i, hji⟩, Or.inr
      ((mem_supercriticalMediumCrossBlock w ⟨j, i, hji⟩ (y, x)).2
        ⟨hy, hx⟩)⟩

/-- Ordered endpoints used to realize a random role in the tagged block
coordinate space.  Their unordered pair is `mediumRandomRoleCoordinate`. -/
def supercriticalMediumRandomRoleEndpoints
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    SupercriticalMediumRandomRole k → Fin n × Fin n
  | Sum.inl r =>
      (K.embedding mediumCenterIndex,
        K.embedding (mediumOtherLeafIndex hk r))
  | Sum.inr (Sum.inl r) =>
      (K.embedding (mediumCompanionIndex hk),
        K.embedding (mediumOtherLeafIndex hk r))
  | Sum.inr (Sum.inr p) =>
      (K.embedding (mediumOtherLeafIndex hk p.1.1),
        K.embedding (mediumOtherLeafIndex hk p.1.2))

@[simp] theorem mediumRandomRoleCoordinate_eq_endpoints
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (r : SupercriticalMediumRandomRole k) :
    mediumRandomRoleCoordinate hk K r =
      s((supercriticalMediumRandomRoleEndpoints hk K r).1,
        (supercriticalMediumRandomRoleEndpoints hk K r).2) := by
  rcases r with r | r
  · rfl
  · rcases r with r | p <;> rfl

/-- Every random role of a potential star is represented by one sampled
cross-edge coordinate. -/
theorem supercriticalMediumRandomRole_isSampled
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (r : SupercriticalMediumRandomRole k) :
    supercriticalMediumIsSampledCrossPair w
      (supercriticalMediumRandomRoleEndpoints hk K r).1
      (supercriticalMediumRandomRoleEndpoints hk K r).2 := by
  rcases r with r | r
  · simpa [supercriticalMediumRandomRoleEndpoints] using
      supercriticalMediumIsSampledCrossPair_of_mem_sampledParts w
        (otherSupercriticalPartEquiv_ne hk w.part r).symm
        (supercriticalMediumCandidate_center_mem_sampledPart hk K)
        (supercriticalMediumCandidate_other_mem_sampledPart hk K r)
  · rcases r with r | p
    · simpa [supercriticalMediumRandomRoleEndpoints] using
        supercriticalMediumIsSampledCrossPair_of_mem_sampledParts w
          (otherSupercriticalPartEquiv_ne hk w.part r).symm
          (supercriticalMediumCandidate_companion_mem_sampledPart hk K)
          (supercriticalMediumCandidate_other_mem_sampledPart hk K r)
    · have hij :
          (otherSupercriticalPartEquiv hk w.part p.1.1 : Fin (k - 1)) ≠
            (otherSupercriticalPartEquiv hk w.part p.1.2 : Fin (k - 1)) := by
        intro h
        have hp : p.1.1 = p.1.2 :=
          (otherSupercriticalPartEquiv hk w.part).injective (Subtype.ext h)
        exact (Fin.ne_of_lt p.2) hp
      simpa [supercriticalMediumRandomRoleEndpoints] using
        supercriticalMediumIsSampledCrossPair_of_mem_sampledParts w hij
          (supercriticalMediumCandidate_other_mem_sampledPart hk K p.1.1)
          (supercriticalMediumCandidate_other_mem_sampledPart hk K p.1.2)

/-- The unique tagged block coordinate occupied by a candidate's random
role. -/
noncomputable def supercriticalMediumTaggedRoleCoordinate
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (r : SupercriticalMediumRandomRole k) :
    (supercriticalMediumFixedModel w).Coordinate :=
  supercriticalMediumCoordinateOfSampled w
    (supercriticalMediumRandomRoleEndpoints hk K r).1
    (supercriticalMediumRandomRoleEndpoints hk K r).2
    (supercriticalMediumRandomRole_isSampled hk K r)

@[simp] theorem supercriticalMediumTaggedRoleCoordinate_sym2
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (r : SupercriticalMediumRandomRole k) :
    supercriticalMediumCoordinateSym2 w
        (supercriticalMediumTaggedRoleCoordinate hk K r) =
      mediumRandomRoleCoordinate hk K r := by
  rw [supercriticalMediumTaggedRoleCoordinate,
    supercriticalMediumCoordinateOfSampled_spec,
    mediumRandomRoleCoordinate_eq_endpoints]

/-- Candidate random roles realized in the tagged fixed-block coordinate
space, with the same one global success predicate for every candidate. -/
def supercriticalMediumTaggedRoleCoordinates
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    SupercriticalMediumRoleCoordinates k hk
      (supercriticalMediumFixedModel w).Coordinate where
  coordinate := supercriticalMediumTaggedRoleCoordinate hk K
  successPresent := fun c ↦
    mediumSuccessPresent w (supercriticalMediumCoordinateSym2 w c)
  role_orientation := by
    intro r
    rw [supercriticalMediumTaggedRoleCoordinate_sym2,
      mediumRandomRole_orientation hk K r]

/-- Required tagged successes for one potential star. -/
def supercriticalMediumTaggedRequired
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    Finset (supercriticalMediumFixedModel w).Coordinate :=
  (supercriticalMediumTaggedRoleCoordinates hk K).required hk

theorem supercriticalMediumAmbientOutcome_taggedRequired
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    supercriticalMediumAmbientOutcome w
        (supercriticalMediumTaggedRequired hk K) =
      requiredSuccessCoordinates hk K := by
  classical
  ext e
  simp only [supercriticalMediumAmbientOutcome,
    supercriticalMediumTaggedRequired,
    SupercriticalMediumRoleCoordinates.required,
    requiredSuccessCoordinates, Finset.mem_map,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, (supercriticalMediumTaggedRoleCoordinate_sym2 hk K r).symm⟩
  · rintro ⟨r, hr⟩
    refine ⟨supercriticalMediumTaggedRoleCoordinate hk K r, ⟨r, rfl⟩, ?_⟩
    exact (supercriticalMediumTaggedRoleCoordinate_sym2 hk K r).trans hr

/-- Forgetting tags preserves and reflects overlap of candidate required
sets. -/
theorem supercriticalMediumTaggedRequired_disjoint_iff
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K L : SupercriticalMediumStarCandidate hk w) :
    Disjoint (supercriticalMediumTaggedRequired hk K)
        (supercriticalMediumTaggedRequired hk L) ↔
      Disjoint (requiredSuccessCoordinates hk K)
        (requiredSuccessCoordinates hk L) := by
  rw [← supercriticalMediumAmbientOutcome_taggedRequired hk K,
    ← supercriticalMediumAmbientOutcome_taggedRequired hk L]
  exact (Finset.disjoint_map
    (supercriticalMediumCoordinateEmbedding w)).symm

/-- The cardinality support bound transfers verbatim to tagged coordinates. -/
theorem supercriticalMediumTaggedRequired_card_le
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    (supercriticalMediumTaggedRequired hk K).card ≤
      2 * (k - 2) + (k - 2) ^ 2 :=
  (supercriticalMediumTaggedRoleCoordinates hk K).required_card_le hk

theorem supercriticalMediumCandidate_required_isSampled
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    {a b : Fin (k + 1)}
    (hab : s(K.embedding a, K.embedding b) ∈
      requiredSuccessCoordinates hk K) :
    supercriticalMediumIsSampledCrossPair w
      (K.embedding a) (K.embedding b) := by
  apply supercriticalMediumIsSelectedTaggedPair_isSampled w
    (supercriticalMediumTaggedRequired hk K)
  change s(K.embedding a, K.embedding b) ∈
    supercriticalMediumAmbientOutcome w
      (supercriticalMediumTaggedRequired hk K)
  rw [supercriticalMediumAmbientOutcome_taggedRequired hk K]
  exact hab

/-- Among the selected vertices of a potential star, the sampled pairs are
exactly among its recorded random roles. -/
theorem supercriticalMediumCandidate_sampledPair_mem_required
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (a b : Fin (k + 1))
    (hsample : supercriticalMediumIsSampledCrossPair w
      (K.embedding a) (K.embedding b)) :
    s(K.embedding a, K.embedding b) ∈ requiredSuccessCoordinates hk K := by
  rcases mediumStarIndex_cases hk a with ha | ha | ha | ⟨r, ha⟩ <;>
    rcases mediumStarIndex_cases hk b with hb | hb | hb | ⟨t, hb⟩ <;>
    subst a <;> subst b
  · exact (supercriticalMediumIsSampledCrossPair_ne w hsample rfl).elim
  · rw [K.embedding_witness] at hsample
    exact (not_supercriticalMediumIsSampledCrossPair_witness_left w _
      ((supercriticalMediumIsSampledCrossPair_comm w _ _).mp hsample)).elim
  · exact (not_supercriticalMediumIsSampledCrossPair_of_mem_same_part w w.part
      (supercriticalMediumSampledPart_subset w _
        (supercriticalMediumCandidate_center_mem_sampledPart hk K))
      (supercriticalMediumSampledPart_subset w _
        (supercriticalMediumCandidate_companion_mem_sampledPart hk K))
      hsample).elim
  · simpa [mediumRandomRoleCoordinate] using
      mediumRandomRoleCoordinate_mem_required hk K (Sum.inl t)
  · rw [K.embedding_witness] at hsample
    exact (not_supercriticalMediumIsSampledCrossPair_witness_left w _ hsample).elim
  · exact (supercriticalMediumIsSampledCrossPair_ne w hsample rfl).elim
  · rw [K.embedding_witness] at hsample
    exact (not_supercriticalMediumIsSampledCrossPair_witness_left w _ hsample).elim
  · rw [K.embedding_witness] at hsample
    exact (not_supercriticalMediumIsSampledCrossPair_witness_left w _ hsample).elim
  · exact (not_supercriticalMediumIsSampledCrossPair_of_mem_same_part w w.part
      (supercriticalMediumSampledPart_subset w _
        (supercriticalMediumCandidate_companion_mem_sampledPart hk K))
      (supercriticalMediumSampledPart_subset w _
        (supercriticalMediumCandidate_center_mem_sampledPart hk K))
      hsample).elim
  · rw [K.embedding_witness] at hsample
    exact (not_supercriticalMediumIsSampledCrossPair_witness_left w _
      ((supercriticalMediumIsSampledCrossPair_comm w _ _).mp hsample)).elim
  · exact (supercriticalMediumIsSampledCrossPair_ne w hsample rfl).elim
  · simpa [mediumRandomRoleCoordinate] using
      mediumRandomRoleCoordinate_mem_required hk K (Sum.inr (Sum.inl t))
  · rw [Sym2.eq_swap]
    simpa [mediumRandomRoleCoordinate] using
      mediumRandomRoleCoordinate_mem_required hk K (Sum.inl r)
  · rw [K.embedding_witness] at hsample
    exact (not_supercriticalMediumIsSampledCrossPair_witness_left w _
      ((supercriticalMediumIsSampledCrossPair_comm w _ _).mp hsample)).elim
  · rw [Sym2.eq_swap]
    simpa [mediumRandomRoleCoordinate] using
      mediumRandomRoleCoordinate_mem_required hk K (Sum.inr (Sum.inl r))
  · by_cases hrt : r = t
    · subst t
      exact (supercriticalMediumIsSampledCrossPair_ne w hsample rfl).elim
    · rcases lt_or_gt_of_ne hrt with hlt | hgt
      · simpa [mediumRandomRoleCoordinate] using
          mediumRandomRoleCoordinate_mem_required hk K
            (Sum.inr (Sum.inr ⟨(r, t), hlt⟩))
      · rw [Sym2.eq_swap]
        simpa [mediumRandomRoleCoordinate] using
          mediumRandomRoleCoordinate_mem_required hk K
            (Sum.inr (Sum.inr ⟨(t, r), hgt⟩))

theorem not_supercriticalMediumCandidate_sampledPair_of_not_required
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (a b : Fin (k + 1))
    (hab : s(K.embedding a, K.embedding b) ∉
      requiredSuccessCoordinates hk K) :
    ¬supercriticalMediumIsSampledCrossPair w
      (K.embedding a) (K.embedding b) :=
  fun hsample ↦ hab
    (supercriticalMediumCandidate_sampledPair_mem_required hk K a b hsample)

/-- Decoding an oriented outcome means flipping the globally complemented
coordinates back before constructing the actual graph. -/
def supercriticalMediumGraphOfOrientedOutcome
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate) :
    SimpleGraph (Fin n) :=
  supercriticalMediumTaggedOutcomeGraph w
    (DenseGraph.FiniteBernoulliProduct.flipOutcome
      (supercriticalMediumTaggedGlobalFlipSet w) outcome)

@[simp] theorem supercriticalMediumOrientedBernoulliModel_probability
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (c : (supercriticalMediumFixedModel w).Coordinate) :
    (supercriticalMediumOrientedBernoulliModel w).probability c =
      supercriticalMediumOrientedCoordinateProbability w c := by
  classical
  unfold supercriticalMediumOrientedBernoulliModel
    supercriticalMediumOrientedCoordinateProbability
    supercriticalMediumTaggedSuccessPresent
  by_cases hc : mediumSuccessPresent w s(c.2.1.1, c.2.1.2) <;>
    simp [supercriticalMediumCoordinateSym2, hc]

/-- Membership in a globally reoriented outcome decodes to the required
present/absent value of the represented graph edge. -/
theorem supercriticalMediumIsSelectedTaggedPair_flipOutcome_iff
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate)
    {x y : Fin n} (hxy : supercriticalMediumIsSampledCrossPair w x y) :
    supercriticalMediumIsSelectedTaggedPair w
        (DenseGraph.FiniteBernoulliProduct.flipOutcome
          (supercriticalMediumTaggedGlobalFlipSet w) outcome) x y ↔
      (mediumSuccessPresent w s(x, y) ↔
        supercriticalMediumIsSelectedTaggedPair w outcome x y) := by
  classical
  rw [supercriticalMediumIsSelectedTaggedPair_iff_coordinate_mem w _ hxy,
    supercriticalMediumIsSelectedTaggedPair_iff_coordinate_mem w _ hxy,
    DenseGraph.FiniteBernoulliProduct.mem_flipOutcome]
  have hc := supercriticalMediumCoordinateOfSampled_spec w x y hxy
  by_cases hp : mediumSuccessPresent w s(x, y)
  · simp [hp, hc]
  · simp [hp, hc]

/-- The graph decoded from every oriented outcome realizes every selected
candidate with precisely its tagged required coordinates. -/
theorem supercriticalMediumGraphOfOrientedOutcome_realizes
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate) :
    MediumCandidateOutcomeRealizes hk K
      (supercriticalMediumGraphOfOrientedOutcome w outcome)
      (supercriticalMediumAmbientOutcome w outcome) := by
  intro a b
  by_cases hab : s(K.embedding a, K.embedding b) ∈
      requiredSuccessCoordinates hk K
  · have hsample :=
      supercriticalMediumCandidate_required_isSampled hk K hab
    rw [if_pos hab, supercriticalMediumGraphOfOrientedOutcome,
      supercriticalMediumTaggedOutcomeGraph_adj_of_sampled w _ hsample,
      supercriticalMediumIsSelectedTaggedPair_flipOutcome_iff w outcome hsample]
    rfl
  · have hnot :=
      not_supercriticalMediumCandidate_sampledPair_of_not_required hk K a b hab
    rw [if_neg hab, supercriticalMediumGraphOfOrientedOutcome,
      supercriticalMediumTaggedOutcomeGraph_adj_of_not_sampled w _ hnot]

/-! ## Exact fixed-sample / tagged-outcome correspondence -/

theorem supercriticalMediumIsSelectedTaggedPair_sampleOutcome_iff
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample)
    {x y : Fin n} (hxy : supercriticalMediumIsSampledCrossPair w x y) :
    supercriticalMediumIsSelectedTaggedPair w
        ((supercriticalMediumFixedModel w).sampleOutcome S) x y ↔
      supercriticalMediumIsSelectedCrossPair w S x y := by
  classical
  let c := supercriticalMediumCoordinateOfSampled w x y hxy
  have hc : supercriticalMediumCoordinateSym2 w c = s(x, y) := by
    simpa [c] using supercriticalMediumCoordinateOfSampled_spec w x y hxy
  rw [supercriticalMediumIsSelectedTaggedPair_iff_coordinate_mem w _ hxy]
  constructor
  · intro hmem
    have hcBlock : c.2 ∈ (S c.1).1 :=
      ((supercriticalMediumFixedModel w).mem_sampleOutcome S c).mp
        (by simpa [c] using hmem)
    have hcSelected : c.2.1 ∈
        (supercriticalMediumFixedModel w).selectedInBlock S c.1 :=
      Finset.mem_map.mpr ⟨c.2, hcBlock, rfl⟩
    rcases Sym2.eq_iff.mp hc with h | h
    · refine ⟨c.1, Or.inl ?_⟩
      have hpair : c.2.1 = (x, y) := Prod.ext h.1 h.2
      rw [← hpair]
      exact hcSelected
    · refine ⟨c.1, Or.inr ?_⟩
      have hpair : c.2.1 = (y, x) := Prod.ext h.1 h.2
      rw [← hpair]
      exact hcSelected
  · rintro ⟨e, h | h⟩
    · obtain ⟨uv, huv, huvEq⟩ := Finset.mem_map.mp h
      let d : (supercriticalMediumFixedModel w).Coordinate := ⟨e, uv⟩
      have hdSym : supercriticalMediumCoordinateSym2 w d = s(x, y) := by
        have huvEq' : uv.1 = (x, y) := huvEq
        change s(uv.1.1, uv.1.2) = s(x, y)
        rw [huvEq']
      have hdc : d = c :=
        supercriticalMediumCoordinateSym2_injective w (hdSym.trans hc.symm)
      have hdMem : d ∈ (supercriticalMediumFixedModel w).sampleOutcome S := by
        rw [(supercriticalMediumFixedModel w).mem_sampleOutcome]
        exact huv
      simpa [c, hdc] using hdMem
    · obtain ⟨uv, huv, huvEq⟩ := Finset.mem_map.mp h
      let d : (supercriticalMediumFixedModel w).Coordinate := ⟨e, uv⟩
      have hdSym : supercriticalMediumCoordinateSym2 w d = s(x, y) := by
        have huvEq' : uv.1 = (y, x) := huvEq
        change s(uv.1.1, uv.1.2) = s(x, y)
        rw [huvEq']
        exact Sym2.eq_swap
      have hdc : d = c :=
        supercriticalMediumCoordinateSym2_injective w (hdSym.trans hc.symm)
      have hdMem : d ∈ (supercriticalMediumFixedModel w).sampleOutcome S := by
        rw [(supercriticalMediumFixedModel w).mem_sampleOutcome]
        exact huv
      simpa [c, hdc] using hdMem

/-- The graph constructed from a fixed sample is definitionally the same
random-edge replacement as the graph constructed from its combined tagged
outcome. -/
theorem supercriticalMediumTaggedOutcomeGraph_sampleOutcome
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : (supercriticalMediumFixedModel w).Sample) :
    supercriticalMediumTaggedOutcomeGraph w
        ((supercriticalMediumFixedModel w).sampleOutcome S) =
      supercriticalMediumOutcomeGraph w S := by
  ext x y
  by_cases hxy : supercriticalMediumIsSampledCrossPair w x y
  · rw [supercriticalMediumTaggedOutcomeGraph_adj_of_sampled w _ hxy,
      supercriticalMediumOutcomeGraph_adj_of_sampled w S hxy,
      supercriticalMediumIsSelectedTaggedPair_sampleOutcome_iff w S hxy]
  · rw [supercriticalMediumTaggedOutcomeGraph_adj_of_not_sampled w _ hxy,
      supercriticalMediumOutcomeGraph_adj_of_not_sampled w S hxy]

/-- Tagged base outcomes whose decoded graph is induced-`K_{1,k}`-free. -/
def supercriticalMediumTaggedInducedFreeEvent
    (k : ℕ) {n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Finset (Finset (supercriticalMediumFixedModel w).Coordinate) := by
  classical
  exact Finset.univ.filter fun outcome ↦
    ¬Regularity.InducedEmbeds (inducedStar k)
      (supercriticalMediumTaggedOutcomeGraph w outcome)

@[simp] theorem mem_supercriticalMediumTaggedInducedFreeEvent
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate) :
    outcome ∈ supercriticalMediumTaggedInducedFreeEvent k w ↔
      ¬Regularity.InducedEmbeds (inducedStar k)
        (supercriticalMediumTaggedOutcomeGraph w outcome) := by
  classical
  simp [supercriticalMediumTaggedInducedFreeEvent]

theorem supercriticalMediumInducedFreeSampleEvent_eq_sampleEvent
    {k : ℕ} {hk : 3 ≤ k} {γ : ℝ}
    {hγ : γ ∈ Set.Ico (gammaK k) 1}
    {α : ℝ} (hα : 0 < α)
    {m n : ℕ} {τ : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph k hk γ hγ α m n τ hn D) :
    supercriticalMediumInducedFreeSampleEvent hα K =
      (supercriticalMediumFixedModel
        (supercriticalMediumWitnessOfMem hα K.2)).sampleEvent
          (supercriticalMediumTaggedInducedFreeEvent k
            (supercriticalMediumWitnessOfMem hα K.2)) := by
  classical
  ext S
  rw [mem_supercriticalMediumInducedFreeSampleEvent,
    DenseGraph.FixedCardinalityBlockModel.mem_sampleEvent,
    mem_supercriticalMediumTaggedInducedFreeEvent,
    supercriticalMediumTaggedOutcomeGraph_sampleOutcome]

/-- The same induced-free event transported to the single globally oriented
Bernoulli cube. -/
def supercriticalMediumOrientedInducedFreeEvent
    (k : ℕ) {n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Finset (Finset (supercriticalMediumFixedModel w).Coordinate) :=
  DenseGraph.FiniteBernoulliProduct.flipEvent
    (supercriticalMediumTaggedGlobalFlipSet w)
    (supercriticalMediumTaggedInducedFreeEvent k w)

@[simp] theorem mem_supercriticalMediumOrientedInducedFreeEvent
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (outcome : Finset (supercriticalMediumFixedModel w).Coordinate) :
    outcome ∈ supercriticalMediumOrientedInducedFreeEvent k w ↔
      ¬Regularity.InducedEmbeds (inducedStar k)
        (supercriticalMediumGraphOfOrientedOutcome w outcome) := by
  classical
  simp [supercriticalMediumOrientedInducedFreeEvent,
    supercriticalMediumGraphOfOrientedOutcome]

/-- Required tagged coordinates, indexed by a concrete finite candidate
family. -/
def supercriticalMediumTaggedRequiredFamily
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (candidates : Finset (SupercriticalMediumStarCandidate hk w)) :
    ↑candidates → Finset (supercriticalMediumFixedModel w).Coordinate :=
  fun K ↦ supercriticalMediumTaggedRequired hk K.1

/-- Star-freeness of an oriented outcome implies simultaneous avoidance of
all potential-star principal events in any selected candidate family. -/
theorem supercriticalMediumOrientedInducedFreeEvent_subset_avoidance
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (candidates : Finset (SupercriticalMediumStarCandidate hk w))
    [LinearOrder ↑candidates] :
    supercriticalMediumOrientedInducedFreeEvent k w ⊆
      DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
        (supercriticalMediumTaggedRequiredFamily hk candidates) := by
  classical
  intro outcome hfree
  rw [DenseGraph.FiniteBernoulliProduct.mem_principalAvoidanceEvent]
  intro K hsuccess
  have hambient : requiredSuccessCoordinates hk K.1 ⊆
      supercriticalMediumAmbientOutcome w outcome := by
    rw [← supercriticalMediumAmbientOutcome_taggedRequired hk K.1]
    intro e he
    unfold supercriticalMediumAmbientOutcome at he ⊢
    rw [Finset.mem_map] at he ⊢
    obtain ⟨c, hc, rfl⟩ := he
    exact ⟨c, hsuccess (by
      simpa [supercriticalMediumTaggedRequiredFamily] using hc), rfl⟩
  have hfree' :=
    (mem_supercriticalMediumOrientedInducedFreeEvent w outcome).mp hfree
  exact hfree' (mediumPotentialSuccess_inducedStar hk K.1
    (supercriticalMediumGraphOfOrientedOutcome w outcome)
    (supercriticalMediumAmbientOutcome w outcome)
    (supercriticalMediumGraphOfOrientedOutcome_realizes hk K.1 outcome)
    hambient)

/-- Exact transport of the induced-free event probability across the global
coordinate complementation. -/
theorem supercriticalMediumBaseProbability_eq_orientedProbability
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (supercriticalMediumBernoulliModel w).eventProbability
        (supercriticalMediumTaggedInducedFreeEvent k w) =
      (supercriticalMediumOrientedBernoulliModel w).eventProbability
        (supercriticalMediumOrientedInducedFreeEvent k w) := by
  exact (DenseGraph.FiniteBernoulliProduct.complementCoordinates_eventProbability_flipEvent
      (supercriticalMediumBernoulliModel w)
      (supercriticalMediumTaggedGlobalFlipSet w)
      (supercriticalMediumTaggedInducedFreeEvent k w)).symm

/-- Exact fixed-count-to-oriented-Bernoulli comparison for the graph-valued
induced-free event, before applying Janson. -/
theorem supercriticalMediumFixedProbability_le_conditioning_mul_avoidance
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (candidates : Finset (SupercriticalMediumStarCandidate hk w))
    [LinearOrder ↑candidates] :
    (supercriticalMediumFixedModel w).outcomeEventProbability
        (supercriticalMediumTaggedInducedFreeEvent k w) ≤
      (supercriticalMediumFixedModel w).conditioningFactor *
        (supercriticalMediumOrientedBernoulliModel w).eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
            (supercriticalMediumTaggedRequiredFamily hk candidates)) := by
  classical
  calc
    (supercriticalMediumFixedModel w).outcomeEventProbability
        (supercriticalMediumTaggedInducedFreeEvent k w) ≤
      (supercriticalMediumFixedModel w).conditioningFactor *
        (supercriticalMediumBernoulliModel w).eventProbability
          (supercriticalMediumTaggedInducedFreeEvent k w) :=
      DenseGraph.FixedCardinalityBlockModel.fixedCardinality_eventProbability_le_conditioningFactor_mul
          (supercriticalMediumFixedModel w) _
    _ = (supercriticalMediumFixedModel w).conditioningFactor *
        (supercriticalMediumOrientedBernoulliModel w).eventProbability
          (supercriticalMediumOrientedInducedFreeEvent k w) := by
      rw [supercriticalMediumBaseProbability_eq_orientedProbability]
    _ ≤ (supercriticalMediumFixedModel w).conditioningFactor *
        (supercriticalMediumOrientedBernoulliModel w).eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
            (supercriticalMediumTaggedRequiredFamily hk candidates)) := by
      exact mul_le_mul_of_nonneg_left
        ((supercriticalMediumOrientedBernoulliModel w).eventProbability_mono
          (supercriticalMediumOrientedInducedFreeEvent_subset_avoidance
            hk candidates))
        (supercriticalMediumFixedModel w).conditioningFactor_pos.le

end InducedStars
