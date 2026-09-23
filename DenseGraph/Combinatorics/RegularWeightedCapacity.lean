import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-!
# Weighted capacities of regular finite graphs

The sum of products of weights over unordered edges is at most half the
degree-weighted sum of squares.  For a regular graph this gives the usual
quadratic capacity inequality without any spectral theory.  The natural
weight specialization retains the exact linear correction from internal
clique capacities.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DenseGraph

variable {V : Type*} [Fintype V]

/-- Sum of endpoint-weight products, counting each unordered edge once. -/
def weightedEdgeCapacity (G : SimpleGraph V) [DecidableRel G.Adj] (a : V → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v ↦ a u * a v, fun _ _ ↦ mul_comm _ _⟩ e

/-- The weighted degree-sum identity, in oriented-edge form. -/
theorem sum_dart_fst_eq_sum_degree_mul (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → ℝ) :
    (∑ d : G.Dart, f d.fst) = ∑ v, (G.degree v : ℝ) * f v := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul, G.dart_fst_fiber_card_eq_degree] using
    (Finset.sum_fiberwise' (Finset.univ : Finset G.Dart)
      (fun d ↦ d.fst) f).symm

/-- Every unordered edge has precisely two orientations, also for weighted
edge sums. -/
theorem sum_dart_edge_eq_two_mul_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Sym2 V → ℝ) :
    (∑ d : G.Dart, f d.edge) = 2 * ∑ e ∈ G.edgeFinset, f e := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
    (g := fun d ↦ d.edge)
    (fun d _ ↦ G.mem_edgeFinset.mpr d.edge_mem) f
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_const, nsmul_eq_mul,
    G.dart_edge_fiber_card e (G.mem_edgeFinset.mp he)]
  norm_num

/-- The quadratic bound holds for arbitrary signed real weights and an
arbitrary finite simple graph. -/
theorem weightedEdgeCapacity_le_half_sum_degree_mul_sq
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V → ℝ) :
    weightedEdgeCapacity G a ≤ (1 / 2 : ℝ) * ∑ v, (G.degree v : ℝ) * (a v)^2 := by
  have hfst := sum_dart_fst_eq_sum_degree_mul G (fun v ↦ (a v)^2)
  have hswap : (∑ d : G.Dart, (a d.snd)^2) = ∑ d : G.Dart, (a d.fst)^2 := by
    exact Fintype.sum_equiv
      (Function.Involutive.toPerm SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive)
      _ _ (fun d ↦ rfl)
  have hedge : (∑ d : G.Dart, a d.fst * a d.snd) = 2 * weightedEdgeCapacity G a := by
    simpa only [weightedEdgeCapacity, SimpleGraph.Dart.edge, Sym2.lift_mk] using
      sum_dart_edge_eq_two_mul_sum G
        (Sym2.lift ⟨fun u v ↦ a u * a v, fun _ _ ↦ mul_comm _ _⟩)
  have h : (∑ d : G.Dart, 2 * (a d.fst * a d.snd)) ≤
      ∑ d : G.Dart, ((a d.fst)^2 + (a d.snd)^2) := by
    apply Finset.sum_le_sum
    intro d _
    nlinarith [sq_nonneg (a d.fst - a d.snd)]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hswap, hfst, hedge] at h
  linarith

/-- For a `Δ`-regular graph, the endpoint-product capacity is at most
`Δ / 2` times the sum of squares. -/
theorem weightedEdgeCapacity_le_regular_half_sum_sq
    (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hregular : G.IsRegularOfDegree Δ) (a : V → ℝ) :
    weightedEdgeCapacity G a ≤ (Δ : ℝ) / 2 * ∑ v, (a v)^2 := by
  have h := weightedEdgeCapacity_le_half_sum_degree_mul_sq G a
  simp only [hregular.degree_eq, ← Finset.mul_sum] at h
  convert h using 1; ring

/-- Natural vertex weights interpreted as part sizes: the linear remainder
is exactly `(Δ / 2) * ∑ a`, with no balance or divisibility assumptions. -/
theorem weightedEdgeCapacity_nat_le_regular_internalCapacity
    (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hregular : G.IsRegularOfDegree Δ) (a : V → ℕ) :
    weightedEdgeCapacity G (fun v ↦ (a v : ℝ)) ≤
      (Δ : ℝ) * (∑ v, (Nat.choose (a v) 2 : ℝ)) +
        (Δ : ℝ) / 2 * ∑ v, (a v : ℝ) := by
  have hsq : (∑ v, (a v : ℝ)^2) =
      2 * (∑ v, (Nat.choose (a v) 2 : ℝ)) + ∑ v, (a v : ℝ) := by
    simp only [Nat.cast_choose_two, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have h := weightedEdgeCapacity_le_regular_half_sum_sq G hregular (fun v ↦ (a v : ℝ))
  rw [hsq] at h
  convert h using 1; ring

end DenseGraph
