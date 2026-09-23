import InducedStars.C4.TypeLift
import Mathlib.Data.Fintype.Powerset

/-!
# Finite data counting for lifted C4 types

The grouping object is the actual lifted partial template. A bounded reduced
order has only exponentially many lifts in the ambient order: choose its
finite colored data, the cluster label of each vertex, and the active set.
This deliberately overcounts, so no graph-dependent regular partition is
silently assumed to be uniquely determined.
-/

noncomputable section
open Finset InducedStars.Regularity
open scoped Classical
namespace InducedStars

variable {V : Type*} [Fintype V]

def c4ColoredTemplateCode (J : RegularityColoredGraph V) :
    (V → Bool) × (V × V → Option EdgeColor) :=
  (fun v ↦ decide (J.vertexColor v = .blue),
    fun p ↦ DenseGraph.coloredPairStatus J s(p.1,p.2))

theorem c4ColoredTemplateCode_injective :
    Function.Injective (c4ColoredTemplateCode (V := V)) := by
  intro J K h
  have hv (x : V) : J.vertexColor x = K.vertexColor x := by
    have he := congrFun (congrArg Prod.fst h) x
    change decide (J.vertexColor x = .blue) = decide (K.vertexColor x = .blue) at he
    cases hJ : J.vertexColor x <;> cases hK : K.vertexColor x <;> simp_all
  have he (x y : V) : DenseGraph.coloredPairStatus J s(x,y) =
      DenseGraph.coloredPairStatus K s(x,y) := congrFun (congrArg Prod.snd h) (x,y)
  have hg : J.graph = K.graph := by
    ext x y
    have hh := he x y
    simp only [DenseGraph.coloredPairStatus_mk] at hh
    by_cases hJ : J.graph.Adj x y <;> by_cases hK : K.graph.Adj x y <;> simp_all
  cases J with
  | mk graph vertexColor edgeColor =>
    cases K with
    | mk graph' vertexColor' edgeColor' =>
      dsimp only at hg hv he
      cases hg
      have hvv : vertexColor = vertexColor' := funext hv
      cases hvv
      congr 1
      apply SimpleGraph.EdgeLabeling.ext_get
      intro x y hxy
      have hh := he x y
      simpa only [DenseGraph.coloredPairStatus_mk, dif_pos hxy, Option.some.injEq] using hh

local instance c4FiniteColoredTemplates : Finite (RegularityColoredGraph V) :=
  Finite.of_injective c4ColoredTemplateCode c4ColoredTemplateCode_injective

theorem c4ColoredTemplate_count_le (k : ℕ) :
    Nat.card (RegularityColoredGraph (Fin k)) ≤ 2^k * 4^(k*k) := by
  letI : Fintype (RegularityColoredGraph (Fin k)) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective c4ColoredTemplateCode
    (c4ColoredTemplateCode_injective (V := Fin k))
  have he : Fintype.card EdgeColor = 3 := by decide
  simpa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_option, he] using h

def c4ReducedTemplateFinset (k : ℕ) : Finset (RegularityColoredGraph (Fin k)) :=
  @univ _ (Fintype.ofFinite _)

@[simp] theorem mem_c4ReducedTemplateFinset (k : ℕ)
    (J : RegularityColoredGraph (Fin k)) : J ∈ c4ReducedTemplateFinset k := by
  simp [c4ReducedTemplateFinset]

theorem card_c4ReducedTemplateFinset_le (k : ℕ) :
    (c4ReducedTemplateFinset k).card ≤ 2^k * 4^(k*k) := by
  simpa only [c4ReducedTemplateFinset, card_univ, ← Nat.card_eq_fintype_card]
    using c4ColoredTemplate_count_le k

def c4LiftTemplateFamily (n k : ℕ) : Finset (RegularityColoredGraph (Fin n)) :=
  (c4ReducedTemplateFinset k).biUnion fun J ↦
    ((univ : Finset (Fin n → Fin k)).product (univ : Finset (Finset (Fin n)))).image
      fun data ↦ DenseGraph.coloredBlowUp J data.1 (data.2 : Set (Fin n))

theorem coloredBlowUp_mem_c4LiftTemplateFamily {n k : ℕ}
    (J : RegularityColoredGraph (Fin k)) (f : Fin n → Fin k) (S : Finset (Fin n)) :
    DenseGraph.coloredBlowUp J f (S : Set (Fin n)) ∈ c4LiftTemplateFamily n k := by
  exact mem_biUnion.mpr ⟨J, mem_c4ReducedTemplateFinset k J,
    mem_image.mpr ⟨(f,S), mem_product.mpr ⟨mem_univ _, mem_univ _⟩, rfl⟩⟩

theorem card_c4LiftTemplateFamily_le (n k : ℕ) :
    (c4LiftTemplateFamily n k).card ≤ (2^k * 4^(k*k)) * (k^n * 2^n) := by
  calc
    _ ≤ (c4ReducedTemplateFinset k).card * (k^n * 2^n) := by
      apply card_biUnion_le_card_mul
      intro J hJ
      exact (card_image_le).trans_eq (by simp [card_product, Fintype.card_fun])
    _ ≤ _ := Nat.mul_le_mul_right _ (card_c4ReducedTemplateFinset_le k)

def c4BoundedLiftTemplateFamily (n u : ℕ) : Finset (RegularityColoredGraph (Fin n)) :=
  (range (u+1)).biUnion (c4LiftTemplateFamily n)

theorem c4LiftedType_mem_boundedFamily {n u : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {eta tau : ℝ} (T : RegularityType G eta tau 4)
    (hk : 0 < T.partition.clusterCount) (hu : T.partition.clusterCount ≤ u) :
    c4LiftedType T hk ∈ c4BoundedLiftTemplateFamily n u := by
  apply mem_biUnion.mpr
  refine ⟨T.partition.clusterCount, mem_range.mpr (by omega), ?_⟩
  have h := coloredBlowUp_mem_c4LiftTemplateFamily T.coloredGraph
    (c4TypeClusterLabel T.partition hk) (univ \ T.partition.exceptional)
  have hs : ((univ \ T.partition.exceptional : Finset (Fin n)) : Set (Fin n)) =
      {v | v ∉ T.partition.exceptional} := by ext v; simp
  rw [hs] at h
  exact h

/-- Explicit subquadratic data overhead for bounded reduced order. -/
theorem card_c4BoundedLiftTemplateFamily_le (n u : ℕ) :
    (c4BoundedLiftTemplateFamily n u).card ≤
      (u+1) * (2^u * 4^(u*u)) * ((2*u)^n) := by
  calc
    _ ≤ (u+1) * ((2^u * 4^(u*u)) * (u^n * 2^n)) := by
      simpa only [c4BoundedLiftTemplateFamily, card_range] using
        (card_biUnion_le_card_mul (range (u+1)) (c4LiftTemplateFamily n)
          ((2^u * 4^(u*u)) * (u^n * 2^n)) (by
            intro k hk
            have hku : k ≤ u := Nat.le_of_lt_succ (mem_range.mp hk)
            apply (card_c4LiftTemplateFamily_le n k).trans
            gcongr <;> norm_num))
    _ = _ := by rw [mul_pow]; ring

end InducedStars
