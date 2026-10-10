import InducedStars.Structure.Subcritical.Retained
import DenseGraph.FiniteModels.FixedCardinalityBlocks
import Mathlib.Data.Sym.Card

/-!
# Retained active coordinates and exact edge bookkeeping

This file supplies the finite coordinate universe used in the subcritical
counting argument.  Only bounded-order, large components are retained.  An
active coordinate is an unordered edge of the corresponding finite core,
but its endpoints are stored in increasing order so no bipartite block is
counted twice.
-/

noncomputable section

open Finset Set
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The finite retained active index -/

/-- A retained component together with one (increasingly oriented) active
core edge.  This is the paper's finite set of retained active coordinates. -/
@[ext]
structure RetainedActivePair (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) where
  component : Fin D.componentCount
  component_retained : component ∈ D.retainedComponentIndices eta R₀
  left : Fin (D.core component).order
  right : Fin (D.core component).order
  left_lt_right : left < right
  active : (D.core component).graph.Adj left right

private def retainedActivePairEncoding
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ} :
    RetainedActivePair D eta R₀ → D.PartIndex × D.PartIndex :=
  fun e ↦ (⟨e.component, e.left⟩, ⟨e.component, e.right⟩)

private theorem retainedActivePairEncoding_injective
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ} :
    Function.Injective (retainedActivePairEncoding (D := D) (eta := eta) (R₀ := R₀)) := by
  intro e f h
  cases e
  cases f
  simp_all [retainedActivePairEncoding, Sigma.mk.inj_iff]

noncomputable instance retainedActivePairFinite
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Finite (RetainedActivePair D eta R₀) :=
  Finite.of_injective retainedActivePairEncoding retainedActivePairEncoding_injective

noncomputable instance retainedActivePairFintype
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Fintype (RetainedActivePair D eta R₀) := Fintype.ofFinite _

noncomputable instance retainedActivePairDecidableEq
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    DecidableEq (RetainedActivePair D eta R₀) := Classical.decEq _

namespace RetainedActivePair

variable {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}

/-- The left global part index of a retained active coordinate. -/
def leftPart (e : RetainedActivePair D eta R₀) : D.PartIndex :=
  ⟨e.component, e.left⟩

/-- The right global part index of a retained active coordinate. -/
def rightPart (e : RetainedActivePair D eta R₀) : D.PartIndex :=
  ⟨e.component, e.right⟩

@[simp] theorem leftPart_fst (e : RetainedActivePair D eta R₀) :
    e.leftPart.1 = e.component := rfl

@[simp] theorem rightPart_fst (e : RetainedActivePair D eta R₀) :
    e.rightPart.1 = e.component := rfl

theorem leftPart_mem_retained (e : RetainedActivePair D eta R₀) :
    e.leftPart ∈ D.retainedPartIndices eta R₀ := by
  simpa [leftPart] using e.component_retained

theorem rightPart_mem_retained (e : RetainedActivePair D eta R₀) :
    e.rightPart ∈ D.retainedPartIndices eta R₀ := by
  simpa [rightPart] using e.component_retained

theorem leftPart_ne_rightPart (e : RetainedActivePair D eta R₀) :
    e.leftPart ≠ e.rightPart := by
  intro h
  exact (ne_of_lt e.left_lt_right) (by
    simpa [leftPart, rightPart, Sigma.mk.inj_iff] using h)

/-- The selected core edge really is active in the global division. -/
theorem activePart (e : RetainedActivePair D eta R₀) :
    D.ActivePart e.leftPart e.rightPart := by
  simpa [leftPart, rightPart, D.activePart_mk_mk] using e.active

/-- A retained active coordinate is determined by its two oriented global
part indices. -/
theorem eq_of_parts {e f : RetainedActivePair D eta R₀}
    (hl : e.leftPart = f.leftPart) (hr : e.rightPart = f.rightPart) : e = f :=
  retainedActivePairEncoding_injective (Prod.ext hl hr)

end RetainedActivePair

/-! ## Potential bipartite and clique edge sets -/

/-- All unordered vertex pairs available in one retained active bipartite
block.  The increasing orientation makes `Sym2.mk` injective on this block. -/
def retainedActivePotentialEdges (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (e : RetainedActivePair D eta R₀) : Finset (Sym2 V) :=
  ((D.part e.leftPart) ×ˢ (D.part e.rightPart)).image Sym2.mk.uncurry

/-- Capacity of one retained active bipartite block. -/
def retainedActiveCapacity (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (e : RetainedActivePair D eta R₀) : ℕ :=
  (D.part e.leftPart).card * (D.part e.rightPart).card

theorem retainedActivePotentialEdges_card (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (e : RetainedActivePair D eta R₀) :
    (retainedActivePotentialEdges D eta R₀ e).card =
      retainedActiveCapacity D eta R₀ e := by
  rw [retainedActivePotentialEdges, retainedActiveCapacity,
    Finset.card_image_iff.mpr (by
      intro p hp q hq heq
      change s(p.1, p.2) = s(q.1, q.2) at heq
      rw [Sym2.mk_eq_mk_iff] at heq
      rcases heq with h | h
      · exact h
      · have hp' := Finset.mem_product.mp hp
        have hq' := Finset.mem_product.mp hq
        have hleftRight : Disjoint (D.part e.leftPart) (D.part e.rightPart) :=
          D.part_disjoint e.leftPart_ne_rightPart
        exfalso
        exact Finset.disjoint_left.mp hleftRight hp'.1 (h.symm ▸ hq'.2))]
  simp

@[simp] theorem mem_retainedActivePotentialEdges
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (e : RetainedActivePair D eta R₀) (z : Sym2 V) :
    z ∈ retainedActivePotentialEdges D eta R₀ e ↔
      ∃ x ∈ D.part e.leftPart, ∃ y ∈ D.part e.rightPart, z = s(x, y) := by
  simp only [retainedActivePotentialEdges, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

theorem retainedActivePotentialEdges_disjoint
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    {e f : RetainedActivePair D eta R₀} (hef : e ≠ f) :
    Disjoint (retainedActivePotentialEdges D eta R₀ e)
      (retainedActivePotentialEdges D eta R₀ f) := by
  rw [Finset.disjoint_left]
  intro z hze hzf
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    (mem_retainedActivePotentialEdges D eta R₀ e z).mp hze
  subst z
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (mem_retainedActivePotentialEdges D eta R₀ f s(x, y)).mp hzf
  have hpair : (x, y) = (u, v) ∨ (x, y) = (v, u) := by
    exact Sym2.mk_eq_mk_iff.mp huv
  rcases hpair with h | h
  · have hxu : x = u := congrArg Prod.fst h
    have hyv : y = v := congrArg Prod.snd h
    have hleft : e.leftPart = f.leftPart := D.mem_part_unique hx (hxu ▸ hu)
    have hright : e.rightPart = f.rightPart := D.mem_part_unique hy (hyv ▸ hv)
    exact hef (retainedActivePairEncoding_injective (Prod.ext hleft hright))
  · have hxv : x = v := congrArg Prod.fst h
    have hyu : y = u := congrArg Prod.snd h
    have hleft : e.leftPart = f.rightPart := D.mem_part_unique hx (hxv ▸ hv)
    have hright : e.rightPart = f.leftPart := D.mem_part_unique hy (hyu ▸ hu)
    have h1 : e.left.val = f.right.val :=
      congrArg (fun a : D.PartIndex ↦ a.2.val) hleft
    have h2 : e.right.val = f.left.val :=
      congrArg (fun a : D.PartIndex ↦ a.2.val) hright
    have heval : e.left.val < e.right.val := e.left_lt_right
    have hfval : f.left.val < f.right.val := f.left_lt_right
    omega

/-- The union of every retained active bipartite coordinate. -/
def retainedActiveEdgeUniverse (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Finset (Sym2 V) :=
  Finset.univ.biUnion (retainedActivePotentialEdges D eta R₀)

@[simp] theorem mem_retainedActiveEdgeUniverse
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (z : Sym2 V) :
    z ∈ retainedActiveEdgeUniverse D eta R₀ ↔
      ∃ e : RetainedActivePair D eta R₀,
        z ∈ retainedActivePotentialEdges D eta R₀ e := by
  simp [retainedActiveEdgeUniverse]

theorem retainedActiveEdgeUniverse_card
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (retainedActiveEdgeUniverse D eta R₀).card =
      ∑ e : RetainedActivePair D eta R₀, retainedActiveCapacity D eta R₀ e := by
  rw [retainedActiveEdgeUniverse, Finset.card_biUnion]
  · simp [retainedActivePotentialEdges_card]
  · intro e _ f _ hef
    exact retainedActivePotentialEdges_disjoint D eta R₀ hef

/-- The potential clique edges in one retained part. -/
def retainedPartCliquePotentialEdges (D : SubcriticalDivision k V) (a : D.PartIndex) :
    Finset (Sym2 V) :=
  (D.part a).offDiag.image Sym2.mk.uncurry

@[simp] theorem mem_retainedPartCliquePotentialEdges
    (D : SubcriticalDivision k V) (a : D.PartIndex) (z : Sym2 V) :
    z ∈ retainedPartCliquePotentialEdges D a ↔
      ∃ x ∈ D.part a, ∃ y ∈ D.part a, x ≠ y ∧ z = s(x, y) := by
  simp only [retainedPartCliquePotentialEdges, Finset.mem_image,
    Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, rfl⟩
    exact ⟨x, hx, y, hy, hxy, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy, hxy⟩, rfl⟩

@[simp] theorem retainedPartCliquePotentialEdges_card
    (D : SubcriticalDivision k V) (a : D.PartIndex) :
    (retainedPartCliquePotentialEdges D a).card = (D.part a).card.choose 2 := by
  exact Sym2.card_image_offDiag (D.part a)

/-- The union of all retained clique-coordinate sets. -/
def retainedCliquePotentialEdges (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Finset (Sym2 V) :=
  (D.retainedPartIndices eta R₀).biUnion (retainedPartCliquePotentialEdges D)

@[simp] theorem mem_retainedCliquePotentialEdges
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (z : Sym2 V) :
    z ∈ retainedCliquePotentialEdges D eta R₀ ↔
      ∃ a ∈ D.retainedPartIndices eta R₀,
        z ∈ retainedPartCliquePotentialEdges D a := by
  simp [retainedCliquePotentialEdges]

/-- The retained internal clique capacity. -/
def retainedCliqueCapacity (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : ℕ :=
  ∑ a ∈ D.retainedPartIndices eta R₀, (D.part a).card.choose 2

theorem retainedPartCliquePotentialEdges_disjoint
    (D : SubcriticalDivision k V) {a b : D.PartIndex} (hab : a ≠ b) :
    Disjoint (retainedPartCliquePotentialEdges D a)
      (retainedPartCliquePotentialEdges D b) := by
  rw [Finset.disjoint_left]
  intro z hza hzb
  obtain ⟨x, hxa, y, hya, _, rfl⟩ :=
    (mem_retainedPartCliquePotentialEdges D a z).mp hza
  obtain ⟨u, hub, v, hvb, _, huv⟩ :=
    (mem_retainedPartCliquePotentialEdges D b s(x, y)).mp hzb
  change s(x, y) = s(u, v) at huv
  rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (u, v))).mp huv with h | h
  · have hxu : x = u := congrArg Prod.fst h
    exact hab (D.mem_part_unique hxa (hxu.symm ▸ hub))
  · have hxv : x = v := congrArg Prod.fst h
    exact hab (D.mem_part_unique hxa (hxv.symm ▸ hvb))

theorem retainedCliquePotentialEdges_card
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (retainedCliquePotentialEdges D eta R₀).card = retainedCliqueCapacity D eta R₀ := by
  rw [retainedCliquePotentialEdges, retainedCliqueCapacity, Finset.card_biUnion]
  · simp
  · intro a _ b _ hab
    exact retainedPartCliquePotentialEdges_disjoint D hab

theorem retainedCliquePotentialEdges_disjoint_active
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Disjoint (retainedCliquePotentialEdges D eta R₀)
      (retainedActiveEdgeUniverse D eta R₀) := by
  rw [Finset.disjoint_left]
  intro z hzc hza
  obtain ⟨a, ha, hzac⟩ :=
    (mem_retainedCliquePotentialEdges D eta R₀ z).mp hzc
  obtain ⟨x, hxa, y, hya, _, hxy⟩ :=
    (mem_retainedPartCliquePotentialEdges D a z).mp hzac
  obtain ⟨e, hze⟩ := (mem_retainedActiveEdgeUniverse D eta R₀ z).mp hza
  obtain ⟨u, hul, v, hvr, huv⟩ :=
    (mem_retainedActivePotentialEdges D eta R₀ e z).mp hze
  rw [hxy] at huv
  change s(x, y) = s(u, v) at huv
  rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (u, v))).mp huv with h | h
  · have hxu : x = u := congrArg Prod.fst h
    have hyv : y = v := congrArg Prod.snd h
    have hal : a = e.leftPart := D.mem_part_unique hxa (hxu.symm ▸ hul)
    have har : a = e.rightPart := D.mem_part_unique hya (hyv.symm ▸ hvr)
    exact e.leftPart_ne_rightPart (hal.symm.trans har)
  · have hxv : x = v := congrArg Prod.fst h
    have hyu : y = u := congrArg Prod.snd h
    have har : a = e.rightPart := D.mem_part_unique hxa (hxv.symm ▸ hvr)
    have hal : a = e.leftPart := D.mem_part_unique hya (hyu.symm ▸ hul)
    exact e.leftPart_ne_rightPart (hal.symm.trans har)

/-- All unordered pairs wholly inside the nonretained side. -/
def nonretainedPotentialEdges (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Finset (Sym2 V) :=
  (D.nonretainedVertices eta R₀).offDiag.image Sym2.mk.uncurry

@[simp] theorem mem_nonretainedPotentialEdges
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (z : Sym2 V) :
    z ∈ nonretainedPotentialEdges D eta R₀ ↔
      ∃ x ∈ D.nonretainedVertices eta R₀,
        ∃ y ∈ D.nonretainedVertices eta R₀, x ≠ y ∧ z = s(x, y) := by
  simp only [nonretainedPotentialEdges, Finset.mem_image, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, rfl⟩
    exact ⟨x, hx, y, hy, hxy, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy, hxy⟩, rfl⟩

@[simp] theorem nonretainedPotentialEdges_card
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (nonretainedPotentialEdges D eta R₀).card =
      (D.nonretainedVertices eta R₀).card.choose 2 := by
  exact Sym2.card_image_offDiag _

theorem retainedCliquePotentialEdges_disjoint_nonretained
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Disjoint (retainedCliquePotentialEdges D eta R₀)
      (nonretainedPotentialEdges D eta R₀) := by
  rw [Finset.disjoint_left]
  intro z hzc hzn
  obtain ⟨a, ha, hza⟩ :=
    (mem_retainedCliquePotentialEdges D eta R₀ z).mp hzc
  obtain ⟨x, hxa, y, hya, _, hxy⟩ :=
    (mem_retainedPartCliquePotentialEdges D a z).mp hza
  obtain ⟨u, hun, v, hvn, _, huv⟩ :=
    (mem_nonretainedPotentialEdges D eta R₀ z).mp hzn
  have hxr : x ∈ D.retainedVertices eta R₀ := D.part_subset_retainedVertices ha hxa
  rw [hxy] at huv
  change s(x, y) = s(u, v) at huv
  rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (u, v))).mp huv with h | h
  · have hxu : x = u := congrArg Prod.fst h
    exact ((D.mem_nonretainedVertices eta R₀ u).mp hun) (hxu.symm ▸ hxr)
  · have hxv : x = v := congrArg Prod.fst h
    exact ((D.mem_nonretainedVertices eta R₀ v).mp hvn) (hxv.symm ▸ hxr)

theorem retainedActiveEdgeUniverse_disjoint_nonretained
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Disjoint (retainedActiveEdgeUniverse D eta R₀)
      (nonretainedPotentialEdges D eta R₀) := by
  rw [Finset.disjoint_left]
  intro z hza hzn
  obtain ⟨e, hze⟩ := (mem_retainedActiveEdgeUniverse D eta R₀ z).mp hza
  obtain ⟨x, hxl, y, hyr, hxy⟩ :=
    (mem_retainedActivePotentialEdges D eta R₀ e z).mp hze
  obtain ⟨u, hun, v, hvn, _, huv⟩ :=
    (mem_nonretainedPotentialEdges D eta R₀ z).mp hzn
  have hxr : x ∈ D.retainedVertices eta R₀ :=
    D.part_subset_retainedVertices e.leftPart_mem_retained hxl
  rw [hxy] at huv
  change s(x, y) = s(u, v) at huv
  rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (u, v))).mp huv with h | h
  · have hxu : x = u := congrArg Prod.fst h
    exact ((D.mem_nonretainedVertices eta R₀ u).mp hun) (hxu.symm ▸ hxr)
  · have hxv : x = v := congrArg Prod.fst h
    exact ((D.mem_nonretainedVertices eta R₀ v).mp hvn) (hxv.symm ▸ hxr)

/-! ## Feasible retained count vectors -/

/-- A capacity-bounded edge count on every retained active coordinate. -/
@[ext]
structure RetainedEdgeCountVector (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) where
  count : RetainedActivePair D eta R₀ → ℕ
  count_le_capacity : ∀ e, count e ≤ retainedActiveCapacity D eta R₀ e

private def retainedEdgeCountVectorEncoding
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ} :
    RetainedEdgeCountVector D eta R₀ →
      (e : RetainedActivePair D eta R₀) → Fin (retainedActiveCapacity D eta R₀ e + 1) :=
  fun m e ↦ ⟨m.count e, Nat.lt_succ_iff.mpr (m.count_le_capacity e)⟩

private theorem retainedEdgeCountVectorEncoding_injective
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ} :
    Function.Injective
      (retainedEdgeCountVectorEncoding (D := D) (eta := eta) (R₀ := R₀)) := by
  intro m m' h
  apply RetainedEdgeCountVector.ext
  funext e
  exact congrArg (fun f ↦ (f e).val) h

noncomputable instance retainedEdgeCountVectorFinite
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Finite (RetainedEdgeCountVector D eta R₀) :=
  Finite.of_injective retainedEdgeCountVectorEncoding retainedEdgeCountVectorEncoding_injective

noncomputable instance retainedEdgeCountVectorFintype
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Fintype (RetainedEdgeCountVector D eta R₀) := Fintype.ofFinite _

noncomputable instance retainedEdgeCountVectorDecidableEq
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    DecidableEq (RetainedEdgeCountVector D eta R₀) := Classical.decEq _

/-- Total number of chosen retained active edges. -/
def retainedEdgeCountTotal {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (m : RetainedEdgeCountVector D eta R₀) : ℕ :=
  ∑ e, m.count e

/-- Product of the independent binomial multiplicities of a retained vector. -/
def retainedEdgeCountMultiplicity {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (m : RetainedEdgeCountVector D eta R₀) : ℕ :=
  ∏ e, Nat.choose (retainedActiveCapacity D eta R₀ e) (m.count e)

/-- The actual retained active count vector of a finite graph. -/
def actualRetainedEdgeCountVector (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : RetainedEdgeCountVector D eta R₀ where
  count e := (G.interedges (D.part e.leftPart) (D.part e.rightPart)).card
  count_le_capacity e := G.card_interedges_le_mul _ _

@[simp] theorem actualRetainedEdgeCountVector_count
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (e : RetainedActivePair D eta R₀) :
    (actualRetainedEdgeCountVector G D eta R₀).count e =
      (G.interedges (D.part e.leftPart) (D.part e.rightPart)).card := rfl

/-- Density associated with one retained coordinate. -/
def retainedEdgeCountDensity {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (m : RetainedEdgeCountVector D eta R₀) (e : RetainedActivePair D eta R₀) : ℝ :=
  (m.count e : ℝ) / (retainedActiveCapacity D eta R₀ e : ℕ)

theorem retainedActiveCapacity_pos (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (e : RetainedActivePair D eta R₀) :
    0 < retainedActiveCapacity D eta R₀ e := by
  exact Nat.mul_pos (D.part_nonempty e.leftPart).card_pos
    (D.part_nonempty e.rightPart).card_pos

theorem retainedEdgeCountDensity_actual_eq_graphDensity
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (e : RetainedActivePair D eta R₀) :
    retainedEdgeCountDensity (actualRetainedEdgeCountVector G D eta R₀) e =
      Regularity.graphDensity G (D.part e.leftPart) (D.part e.rightPart) := by
  rw [retainedEdgeCountDensity, Regularity.graphDensity_eq]
  simp only [actualRetainedEdgeCountVector_count, retainedActiveCapacity, Nat.cast_mul]

/-! ## Actual retained edge sets -/

/-- The chosen unordered edges in one retained active block. -/
def actualRetainedActiveEdges (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (e : RetainedActivePair D eta R₀) : Finset (Sym2 V) :=
  retainedActivePotentialEdges D eta R₀ e ∩ finiteGraphEdges G

theorem actualRetainedActiveEdges_card (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (e : RetainedActivePair D eta R₀) :
    (actualRetainedActiveEdges G D eta R₀ e).card =
      (actualRetainedEdgeCountVector G D eta R₀).count e := by
  let f : V × V → Sym2 V := Sym2.mk.uncurry
  have hinj : Set.InjOn f (G.interedges (D.part e.leftPart) (D.part e.rightPart)) := by
    intro p hp q hq heq
    have hcard :
        #((D.part e.leftPart ×ˢ D.part e.rightPart).image f) =
          #(D.part e.leftPart ×ˢ D.part e.rightPart) := by
      simpa [retainedActivePotentialEdges, retainedActiveCapacity, f] using
        retainedActivePotentialEdges_card D eta R₀ e
    apply (Finset.card_image_iff.mp hcard)
    · exact Finset.mem_product.mpr
        ⟨(G.mem_interedges_iff.mp hp).1, (G.mem_interedges_iff.mp hp).2.1⟩
    · exact Finset.mem_product.mpr
        ⟨(G.mem_interedges_iff.mp hq).1, (G.mem_interedges_iff.mp hq).2.1⟩
    · exact heq
  have hset : (G.interedges (D.part e.leftPart) (D.part e.rightPart)).image f =
      actualRetainedActiveEdges G D eta R₀ e := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hx, hy, hG⟩ := G.mem_interedges_iff.mp hxy
      exact Finset.mem_inter.mpr ⟨
        (mem_retainedActivePotentialEdges D eta R₀ e s(x, y)).mpr
          ⟨x, hx, y, hy, rfl⟩,
        (mk_mem_finiteGraphEdges G x y).mpr hG⟩
    · intro hz
      obtain ⟨hpot, hG⟩ := Finset.mem_inter.mp hz
      obtain ⟨x, hx, y, hy, rfl⟩ :=
        (mem_retainedActivePotentialEdges D eta R₀ e z).mp hpot
      exact Finset.mem_image.mpr ⟨(x, y),
        G.mem_interedges_iff.mpr ⟨hx, hy, (mk_mem_finiteGraphEdges G x y).mp hG⟩, rfl⟩
  rw [← hset, Finset.card_image_iff.mpr hinj]
  rfl

/-- All chosen retained active edges. -/
def actualRetainedActiveEdgeUniverse (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : Finset (Sym2 V) :=
  retainedActiveEdgeUniverse D eta R₀ ∩ finiteGraphEdges G

theorem actualRetainedActiveEdgeUniverse_eq_biUnion
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    actualRetainedActiveEdgeUniverse G D eta R₀ =
      Finset.univ.biUnion (actualRetainedActiveEdges G D eta R₀) := by
  ext z
  simp [actualRetainedActiveEdgeUniverse, actualRetainedActiveEdges]

theorem actualRetainedActiveEdgeUniverse_card
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (actualRetainedActiveEdgeUniverse G D eta R₀).card =
      retainedEdgeCountTotal (actualRetainedEdgeCountVector G D eta R₀) := by
  rw [actualRetainedActiveEdgeUniverse_eq_biUnion, Finset.card_biUnion]
  · simp [retainedEdgeCountTotal, actualRetainedActiveEdges_card]
  · intro e _ f _ hef
    exact (retainedActivePotentialEdges_disjoint D eta R₀ hef).mono
      (Finset.inter_subset_left) (Finset.inter_subset_left)

end InducedStars
