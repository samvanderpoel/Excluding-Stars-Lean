import DenseGraph.Combinatorics.Matching
import DenseGraph.FiniteModels.BernoulliTail

/-!
# Matching-cover encodings for bounded-degree graphs

A graph is determined by the neighborhoods of its canonical maximum-matching
endpoints. Counting those neighborhoods directly gives a uniform Hamming
bound even while every other graph edge varies.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace DenseGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def canonicalMatchingCover (G : SimpleGraph V) : Finset V :=
  (Set.toFinite (canonicalMaximumMatching G).verts).toFinset

theorem canonicalMatchingCover_vertexCover (G : SimpleGraph V) :
    G.IsVertexCover (canonicalMatchingCover G : Set V) := by
  simpa only [canonicalMatchingCover, Set.Finite.coe_toFinset] using
    canonicalMaximumMatching_endpoints_vertexCover G

@[simp] theorem card_canonicalMatchingCover (G : SimpleGraph V) :
    (canonicalMatchingCover G).card = 2 * matchingNumber G := by
  rw [canonicalMatchingCover, ← Set.ncard_eq_toFinset_card,
    canonicalMaximumMatching_endpoint_ncard]

@[simp] theorem matchingNumber_bot : matchingNumber (⊥ : SimpleGraph V) = 0 := by
  have h := Finset.card_le_card
    (canonicalMaximumMatching_subset_edgeFinset (⊥ : SimpleGraph V))
  simpa only [card_matchingEdgeFinset, canonicalMaximumMatching_card,
    SimpleGraph.edgeFinset, SimpleGraph.edgeSet_bot, Set.toFinset_empty,
    Finset.card_empty, Nat.le_zero] using h

/-- Matching number zero means that there is no edge, including on an empty
vertex type. This is the finite endpoint of matching-penalty estimates. -/
theorem matchingNumber_eq_zero_iff (G : SimpleGraph V) :
    matchingNumber G = 0 ↔ G = ⊥ := by
  constructor
  · intro h
    have hc : canonicalMatchingCover G = ∅ := by
      apply Finset.card_eq_zero.mp
      simp [h]
    apply bot_unique
    intro x y hxy
    rcases canonicalMatchingCover_vertexCover G hxy with hx | hy
    · simpa [hc] using hx
    · simpa [hc] using hy
  · rintro rfl
    exact matchingNumber_bot

/-- Oriented rows of the canonical endpoint cover. Both orientations of
an edge may be present; this harmless redundancy keeps the encoding uniform. -/
def matchingCoverNeighborhoodCode (G : SimpleGraph V) : Finset (V × V) :=
  (canonicalMatchingCover G ×ˢ (Finset.univ : Finset V)).filter
    (fun xy ↦ G.Adj xy.1 xy.2)

@[simp] theorem mem_matchingCoverNeighborhoodCode (G : SimpleGraph V) (x y : V) :
    (x, y) ∈ matchingCoverNeighborhoodCode G ↔ x ∈ canonicalMatchingCover G ∧ G.Adj x y := by
  simp [matchingCoverNeighborhoodCode]

theorem matchingCoverNeighborhoodCode_injective :
    Function.Injective (matchingCoverNeighborhoodCode (V := V)) := by
  intro G H hcode
  ext x y
  have transfer (G H : SimpleGraph V)
      (heq : matchingCoverNeighborhoodCode G = matchingCoverNeighborhoodCode H)
      (hxy : G.Adj x y) : H.Adj x y := by
    rcases canonicalMatchingCover_vertexCover G hxy with hx | hy
    · have hh := (mem_matchingCoverNeighborhoodCode G x y).mpr ⟨hx, hxy⟩
      rw [heq] at hh
      exact ((mem_matchingCoverNeighborhoodCode H x y).mp hh).2
    · have hh := (mem_matchingCoverNeighborhoodCode G y x).mpr ⟨hy, hxy.symm⟩
      rw [heq] at hh
      exact ((mem_matchingCoverNeighborhoodCode H y x).mp hh).2.symm
  exact ⟨transfer G H hcode, transfer H G hcode.symm⟩

theorem card_matchingCoverNeighborhoodCode (G : SimpleGraph V) :
    (matchingCoverNeighborhoodCode G).card =
      ∑ v ∈ canonicalMatchingCover G, G.degree v := by
  have heq : matchingCoverNeighborhoodCode G =
      (canonicalMatchingCover G).biUnion
        (fun v ↦ (G.neighborFinset v).image (fun w ↦ (v, w))) := by
    ext xy
    rcases xy with ⟨x, y⟩
    simp
  rw [heq, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro v _
    rw [Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.snd h)]
    rfl
  · intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro xy hx hy
    obtain ⟨u, _, huxy⟩ := Finset.mem_image.mp hx
    obtain ⟨v, _, hvxy⟩ := Finset.mem_image.mp hy
    exact hxy (congrArg Prod.fst (huxy.trans hvxy.symm))

theorem edgeFinset_card_le_matchingCoverNeighborhoodCode (G : SimpleGraph V) :
    G.edgeFinset.card ≤ (matchingCoverNeighborhoodCode G).card := by
  have heq : (matchingCoverNeighborhoodCode G).image (fun xy ↦ s(xy.1, xy.2)) =
      G.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      constructor
      · intro he
        obtain ⟨⟨u,v⟩, huv, heq⟩ := Finset.mem_image.mp he
        have hh : s(u,v) ∈ G.edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr ((mem_matchingCoverNeighborhoodCode G u v).mp huv).2
        exact heq ▸ hh
      · intro he
        have hxy := SimpleGraph.mem_edgeFinset.mp he
        rcases canonicalMatchingCover_vertexCover G hxy with hx | hy
        · exact Finset.mem_image.mpr
            ⟨(x,y), (mem_matchingCoverNeighborhoodCode G x y).mpr ⟨hx,hxy⟩, rfl⟩
        · exact Finset.mem_image.mpr
            ⟨(y,x), (mem_matchingCoverNeighborhoodCode G y x).mpr ⟨hy,hxy.symm⟩, Sym2.eq_swap⟩
  rw [← heq]
  exact Finset.card_image_le

theorem card_matchingCoverNeighborhoodCode_le (G : SimpleGraph V) {d : ℝ}
    (hdegree : ∀ v, (G.degree v : ℝ) ≤ d * Fintype.card V) :
    ((matchingCoverNeighborhoodCode G).card : ℝ) ≤
      (2 * matchingNumber G : ℕ) * (d * Fintype.card V) := by
  rw [card_matchingCoverNeighborhoodCode, Nat.cast_sum]
  calc
    _ ≤ ∑ _v ∈ canonicalMatchingCover G, d * (Fintype.card V : ℝ) :=
      Finset.sum_le_sum (fun v _ ↦ hdegree v)
    _ = _ := by simp

theorem edgeFinset_card_le_matching_degree (G : SimpleGraph V) {d : ℝ}
    (hdegree : ∀ v, (G.degree v : ℝ) ≤ d * Fintype.card V) :
    (G.edgeFinset.card : ℝ) ≤ (2 * matchingNumber G : ℕ) * (d * Fintype.card V) := by
  have h : (G.edgeFinset.card : ℝ) ≤ (matchingCoverNeighborhoodCode G).card := by
    exact_mod_cast edgeFinset_card_le_matchingCoverNeighborhoodCode G
  exact h.trans (card_matchingCoverNeighborhoodCode_le G hdegree)

/-- Uniform finite entropy count, without fixing any ambient or remainder
graph. Zero matching number and the empty vertex type are included. -/
theorem card_graphFamily_le_exp_of_matching_degree
    (F : Finset (SimpleGraph V)) (ell : ℕ) {d : ℝ}
    (hd : 0 ≤ d) (hdHalf : d ≤ 1/2)
    (hmatching : ∀ G ∈ F, matchingNumber G = ell)
    (hdegree : ∀ G ∈ F, ∀ v, (G.degree v : ℝ) ≤ d * Fintype.card V) :
    (F.card : ℝ) ≤ Real.exp ((2 * ell : ℕ) *
      ((Fintype.card V : ℝ) * Real.binEntropy d + Real.log (Fintype.card V + 1))) := by
  let covers := (Finset.univ : Finset V).powersetCard (2 * ell)
  let rows := fun C : Finset V ↦
    FiniteBernoulliProduct.smallPatterns (C ×ˢ (Finset.univ : Finset V)) d
  have hmap : F.image matchingCoverNeighborhoodCode ⊆ covers.biUnion rows := by
    intro code hcode
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hcode
    apply Finset.mem_biUnion.mpr
    refine ⟨canonicalMatchingCover G, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp [hmatching G hG]⟩
    · apply (FiniteBernoulliProduct.mem_smallPatterns _ _ _).mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      have hc := card_matchingCoverNeighborhoodCode_le G (hdegree G hG)
      simpa only [Finset.card_product, Finset.card_univ, card_canonicalMatchingCover,
        Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hc
  have hcovers : covers.card ≤ (Fintype.card V + 1)^(2 * ell) := by
    apply le_trans (Finset.card_le_card (t := smallSubsetFinset Finset.univ (2 * ell)) ?_)
      (by simpa using card_smallSubsetFinset_le_pow (Finset.univ : Finset V) (2*ell))
    intro C hC
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hC
    exact (mem_smallSubsetFinset _ _ _).mpr ⟨hsub, hcard.le⟩
  have hrows (C : Finset V) (hC : C ∈ covers) :
      ((rows C).card : ℝ) ≤ Real.exp ((2 * ell : ℕ) *
        (Fintype.card V : ℝ) * Real.binEntropy d) := by
    have hc := (Finset.mem_powersetCard.mp hC).2
    simpa only [rows, Finset.card_product, Finset.card_univ, hc, Nat.cast_mul] using
      FiniteBernoulliProduct.card_smallPatterns_le_exp_binEntropy
        (C ×ˢ (Finset.univ : Finset V)) hd hdHalf
  have hcard : (F.card : ℝ) ≤
      (covers.card : ℝ) * Real.exp ((2 * ell : ℕ) * (Fintype.card V : ℝ) * Real.binEntropy d) := by
    have hc : F.card ≤ ∑ C ∈ covers, (rows C).card := by
      rw [← Finset.card_image_of_injective F matchingCoverNeighborhoodCode_injective]
      exact (Finset.card_le_card hmap).trans Finset.card_biUnion_le
    calc
      _ ≤ ∑ C ∈ covers, ((rows C).card : ℝ) := by exact_mod_cast hc
      _ ≤ ∑ _C ∈ covers,
          Real.exp ((2 * ell : ℕ) * (Fintype.card V : ℝ) * Real.binEntropy d) :=
        Finset.sum_le_sum hrows
      _ = _ := by simp
  have hpow : ((Fintype.card V + 1 : ℕ) : ℝ)^(2*ell) =
      Real.exp ((2 * ell : ℕ) * Real.log (Fintype.card V + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    simp
  calc
    _ ≤ _ := hcard
    _ ≤ ((Fintype.card V + 1 : ℕ) : ℝ)^(2*ell) *
        Real.exp ((2 * ell : ℕ) * (Fintype.card V : ℝ) * Real.binEntropy d) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast hcovers
    _ = _ := by rw [hpow, ← Real.exp_add]; congr 1; ring

/-- Weighted matching-cover count with the edge cost charged through the
same bounded-degree rows. The entropy and all logarithms are natural. -/
theorem sum_exp_edges_le_of_matching_degree
    (F : Finset (SimpleGraph V)) (ell : ℕ) {d C : ℝ}
    (hd : 0 ≤ d) (hdHalf : d ≤ 1/2) (hC : 0 ≤ C)
    (hmatching : ∀ G ∈ F, matchingNumber G = ell)
    (hdegree : ∀ G ∈ F, ∀ v, (G.degree v : ℝ) ≤ d * Fintype.card V) :
    (∑ G ∈ F, Real.exp (C * G.edgeFinset.card)) ≤
      Real.exp ((2 * ell : ℕ) * ((Fintype.card V : ℝ) *
        (Real.binEntropy d + C*d) + Real.log (Fintype.card V + 1))) := by
  have hpoint (G : SimpleGraph V) (hG : G ∈ F) :
      C * G.edgeFinset.card ≤ C * ((2 * ell : ℕ) * (d * Fintype.card V)) := by
    apply mul_le_mul_of_nonneg_left _ hC
    simpa only [hmatching G hG] using edgeFinset_card_le_matching_degree G (hdegree G hG)
  calc
    _ ≤ ∑ _G ∈ F, Real.exp (C * ((2 * ell : ℕ) * (d * Fintype.card V))) :=
      Finset.sum_le_sum (fun G hG ↦ Real.exp_le_exp.mpr (hpoint G hG))
    _ = (F.card : ℝ) * Real.exp (C * ((2 * ell : ℕ) * (d * Fintype.card V))) := by simp
    _ ≤ Real.exp ((2 * ell : ℕ) * ((Fintype.card V : ℝ) * Real.binEntropy d +
        Real.log (Fintype.card V + 1))) *
        Real.exp (C * ((2 * ell : ℕ) * (d * Fintype.card V))) :=
      mul_le_mul_of_nonneg_right
        (card_graphFamily_le_exp_of_matching_degree F ell hd hdHalf hmatching hdegree)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end DenseGraph
