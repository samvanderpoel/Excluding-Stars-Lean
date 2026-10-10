import InducedStars.Structure.Subcritical.ProfileResidual
import InducedStars.Structure.Subcritical.RetainedCounts
import Mathlib.Combinatorics.Pigeonhole

/-!
# Four residual matching placements and finite thinning scales

Paper: the matching-placement paragraph of
`lemma:residual-matching-estimate-K1k`. Every index is an actual retained
part; no initial-segment representation of the retained components is used.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

/-- The paper's retained matching scale. -/
def subcriticalResidualMatchingLambda (eta : ℝ) (R₀ : ℕ) : ℝ := eta / (4 * R₀)

/-- The exact integer placement bound from the paper. -/
def subcriticalResidualMatchingKappa (eta : ℝ) (R₀ : ℕ) : ℕ :=
  Nat.ceil (10 * (R₀ : ℝ)^2 / eta^2)

theorem subcriticalResidualMatchingLambda_pos {eta : ℝ} {R₀ : ℕ}
    (heta : 0 < eta) (hR : 1 ≤ R₀) : 0 < subcriticalResidualMatchingLambda eta R₀ := by
  have hRp : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  unfold subcriticalResidualMatchingLambda
  positivity

theorem subcriticalResidualMatchingLambda_le_quarter {eta : ℝ} {R₀ : ℕ}
    (heta : eta ≤ 1) (hR : 1 ≤ R₀) : subcriticalResidualMatchingLambda eta R₀ ≤ 1 / 4 := by
  have hRp : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
  unfold subcriticalResidualMatchingLambda
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * R₀)).mpr
  linarith

theorem subcriticalResidualMatchingKappa_pos {eta : ℝ} {R₀ : ℕ}
    (heta : 0 < eta) (hR : 1 ≤ R₀) : 1 ≤ subcriticalResidualMatchingKappa eta R₀ := by
  have hRp : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  have hc : 0 < 10 * (R₀ : ℝ)^2 / eta^2 := by positivity
  have hh := Nat.le_ceil (10 * (R₀ : ℝ)^2 / eta^2)
  unfold subcriticalResidualMatchingKappa
  by_contra hn
  have he : Nat.ceil (10 * (R₀ : ℝ)^2 / eta^2) = 0 := by omega
  rw [he] at hh
  norm_num at hh
  linarith

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

abbrev SubcriticalRetainedPartIndex (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :=
  {a : D.PartIndex // a ∈ D.retainedPartIndices eta R₀}

/-- A fixed finite rank, used only to orient unordered placement indices. -/
def subcriticalRetainedPartRank {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (a : SubcriticalRetainedPartIndex D eta R₀) :
    Fin (Fintype.card (SubcriticalRetainedPartIndex D eta R₀)) := Fintype.equivFin _ a

theorem subcriticalRetainedPartRank_injective
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ} :
    Function.Injective (subcriticalRetainedPartRank (D := D) (eta := eta) (R₀ := R₀)) :=
  (Fintype.equivFin _).injective

/-- The exact four paper placements. The order proof ensures that the
two distinct retained-part placements occur only once. -/
inductive SubcriticalResidualMatchingPlacement
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) where
  | internal (a : SubcriticalRetainedPartIndex D eta R₀)
  | inactive (a b : SubcriticalRetainedPartIndex D eta R₀)
      (ordered : subcriticalRetainedPartRank a < subcriticalRetainedPartRank b)
      (component_eq : a.val.1 = b.val.1) (nonactive : ¬ D.ActivePart a.val b.val)
  | different (a b : SubcriticalRetainedPartIndex D eta R₀)
      (ordered : subcriticalRetainedPartRank a < subcriticalRetainedPartRank b)
      (component_ne : a.val.1 ≠ b.val.1)
  | sparse (a : SubcriticalRetainedPartIndex D eta R₀)

namespace SubcriticalResidualMatchingPlacement
variable {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}

def encoding : SubcriticalResidualMatchingPlacement D eta R₀ →
    SubcriticalRetainedPartIndex D eta R₀ × Option (SubcriticalRetainedPartIndex D eta R₀)
  | .internal a => (a, some a)
  | .inactive a b _ _ _ => (a, some b)
  | .different a b _ _ => (a, some b)
  | .sparse a => (a, none)

theorem encoding_injective : Function.Injective
    (encoding (D := D) (eta := eta) (R₀ := R₀)) := by
  intro x y hxy
  cases x <;> cases y <;> simp_all [encoding]
  all_goals rcases hxy with ⟨rfl, rfl⟩ <;> simp_all

noncomputable instance : Finite (SubcriticalResidualMatchingPlacement D eta R₀) :=
  Finite.of_injective encoding encoding_injective

noncomputable instance : Fintype (SubcriticalResidualMatchingPlacement D eta R₀) :=
  Fintype.ofFinite _

noncomputable instance : DecidableEq (SubcriticalResidualMatchingPlacement D eta R₀) :=
  Classical.decEq _

def leftPart (a : SubcriticalResidualMatchingPlacement D eta R₀) : D.PartIndex :=
  a.encoding.1.val

def rightPart (a : SubcriticalResidualMatchingPlacement D eta R₀) : Option D.PartIndex :=
  a.encoding.2.map Subtype.val

def rightVertices (a : SubcriticalResidualMatchingPlacement D eta R₀) : Finset V :=
  match a.rightPart with
  | some b => D.part b
  | none => D.nonretainedVertices eta R₀

theorem leftPart_mem_retained (a : SubcriticalResidualMatchingPlacement D eta R₀) :
    a.leftPart ∈ D.retainedPartIndices eta R₀ := a.encoding.1.property

/-- The unordered pair has one endpoint in the designated source part
and the other in the exact target of this placement. -/
def Contains (a : SubcriticalResidualMatchingPlacement D eta R₀) (e : Sym2 V) : Prop :=
  ∃ x ∈ D.part a.leftPart, ∃ y ∈ a.rightVertices, e = s(x, y)

theorem card_le : Fintype.card (SubcriticalResidualMatchingPlacement D eta R₀) ≤
    (D.retainedPartIndices eta R₀).card * ((D.retainedPartIndices eta R₀).card + 1) := by
  simpa only [Fintype.card_prod, Fintype.card_option, Fintype.card_coe] using
    Fintype.card_le_of_injective encoding encoding_injective

theorem card_le_kappa (heta : 0 < eta) (heta1 : eta ≤ 1) (hR : 1 ≤ R₀) :
    Fintype.card (SubcriticalResidualMatchingPlacement D eta R₀) ≤
      subcriticalResidualMatchingKappa eta R₀ := by
  let Q := ((D.retainedPartIndices eta R₀).card : ℝ)
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hRQ : eta * Q ≤ R₀ := D.eta_mul_card_retainedPartIndices_le R₀ heta.le
  have hR1 : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
  have hsq := pow_le_pow_left₀ (mul_nonneg heta.le hQ) hRQ 2
  have hlin := mul_le_mul_of_nonneg_left hRQ heta.le
  have hetaR := mul_le_mul_of_nonneg_right heta1 (show (0 : ℝ) ≤ R₀ by positivity)
  have hRR := mul_le_mul_of_nonneg_right hR1 (show (0 : ℝ) ≤ R₀ by positivity)
  have hcap : Q * (Q + 1) ≤ 10 * (R₀ : ℝ)^2 / eta^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos heta)).mpr
    nlinarith only [hsq, hlin, hetaR, hRR, sq_nonneg (R₀ : ℝ)]
  have hcount : (Fintype.card (SubcriticalResidualMatchingPlacement D eta R₀) : ℝ) ≤
      Q * (Q + 1) := by
    dsimp [Q]
    exact_mod_cast card_le (D := D) (eta := eta) (R₀ := R₀)
  have hc := (hcount.trans hcap).trans (Nat.le_ceil _)
  unfold subcriticalResidualMatchingKappa
  exact_mod_cast hc

end SubcriticalResidualMatchingPlacement

/-- A root-avoiding homogeneous residual matching, with actual unordered
edges and a single one of the four retained placements. -/
structure SubcriticalHomogeneousResidualMatching
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (T : SimpleGraph V) (B : Finset V) where
  placement : SubcriticalResidualMatchingPlacement D eta R₀
  edges : Finset (Sym2 V)
  isMatching : DenseGraph.IsEdgeMatching T edges
  samePlacement : ∀ e ∈ edges, placement.Contains e
  avoids : ∀ e ∈ edges, ∀ x ∈ e, x ∉ B

namespace SubcriticalHomogeneousResidualMatching
variable {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
  {T : SimpleGraph V} {B : Finset V}

def firstEndpoint (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (e : {e // e ∈ M.edges}) : V := Classical.choose (M.samePlacement e.val e.property)

def secondEndpoint (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (e : {e // e ∈ M.edges}) : V :=
  Classical.choose (Classical.choose_spec (M.samePlacement e.val e.property)).2

theorem firstEndpoint_mem (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (e : {e // e ∈ M.edges}) : M.firstEndpoint e ∈ D.part M.placement.leftPart :=
  (Classical.choose_spec (M.samePlacement e.val e.property)).1

theorem secondEndpoint_mem (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (e : {e // e ∈ M.edges}) : M.secondEndpoint e ∈ M.placement.rightVertices :=
  (Classical.choose_spec (Classical.choose_spec (M.samePlacement e.val e.property)).2).1

theorem edge_eq_endpoints (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (e : {e // e ∈ M.edges}) : e.val = s(M.firstEndpoint e, M.secondEndpoint e) :=
  (Classical.choose_spec (Classical.choose_spec (M.samePlacement e.val e.property)).2).2

theorem firstEndpoint_mem_edge (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (e : {e // e ∈ M.edges}) : M.firstEndpoint e ∈ e.val := by
  rw [M.edge_eq_endpoints e]
  simp

theorem secondEndpoint_mem_edge (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (e : {e // e ∈ M.edges}) : M.secondEndpoint e ∈ e.val := by
  rw [M.edge_eq_endpoints e]
  simp

theorem firstEndpoint_not_mem_roots (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (e : {e // e ∈ M.edges}) : M.firstEndpoint e ∉ B :=
  M.avoids e.val e.property _ (M.firstEndpoint_mem_edge e)

theorem secondEndpoint_not_mem_roots (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (e : {e // e ∈ M.edges}) : M.secondEndpoint e ∉ B :=
  M.avoids e.val e.property _ (M.secondEndpoint_mem_edge e)

theorem firstEndpoint_injective (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B) :
    Function.Injective M.firstEndpoint := by
  intro e f hef
  apply Subtype.ext
  by_contra hne
  have he : M.firstEndpoint e ∈ (e.val : Set V) := by rw [M.edge_eq_endpoints e]; simp
  have hf : M.firstEndpoint f ∈ (f.val : Set V) := by rw [M.edge_eq_endpoints f]; simp
  exact Set.disjoint_left.mp (M.isMatching.2 e.property f.property hne)
    he (by simpa only [hef] using hf)

theorem secondEndpoint_injective (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B) :
    Function.Injective M.secondEndpoint := by
  intro e f hef
  apply Subtype.ext
  by_contra hne
  have he : M.secondEndpoint e ∈ (e.val : Set V) := by rw [M.edge_eq_endpoints e]; simp
  have hf : M.secondEndpoint f ∈ (f.val : Set V) := by rw [M.edge_eq_endpoints f]; simp
  exact Set.disjoint_left.mp (M.isMatching.2 e.property f.property hne)
    he (by simpa only [hef] using hf)

def firstEndpoints (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B) : Finset V :=
  M.edges.attach.image M.firstEndpoint

def secondEndpoints (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B) : Finset V :=
  M.edges.attach.image M.secondEndpoint

@[simp] theorem card_firstEndpoints (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B) :
    M.firstEndpoints.card = M.edges.card := by
  rw [firstEndpoints, Finset.card_image_of_injective _ M.firstEndpoint_injective,
    Finset.card_attach]

@[simp] theorem card_secondEndpoints (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B) :
    M.secondEndpoints.card = M.edges.card := by
  rw [secondEndpoints, Finset.card_image_of_injective _ M.secondEndpoint_injective,
    Finset.card_attach]

theorem endpoints_card (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B) :
    (DenseGraph.matchingEndpoints M.edges).card = 2 * M.edges.card :=
  M.isMatching.matchingEndpoints_card

theorem two_mul_card_le (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B) :
    2 * M.edges.card ≤ Fintype.card V := by
  rw [← M.endpoints_card]
  exact Finset.card_le_univ _

theorem endpoints_disjoint_roots (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B) :
    Disjoint (DenseGraph.matchingEndpoints M.edges) B := by
  apply Finset.disjoint_left.mpr
  intro x hx hB
  obtain ⟨e, he, hxe⟩ := (DenseGraph.mem_matchingEndpoints M.edges x).mp hx
  exact M.avoids e he x hxe hB

end SubcriticalHomogeneousResidualMatching
end InducedStars
