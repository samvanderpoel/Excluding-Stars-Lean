import InducedStars.Regularity.Embedding

/-!
# Uniform rectangle error for a regular pair

This file packages the standard consequence of regularity that every
subrectangle, including a small one, has centered adjacency sum bounded by
the ambient `ε |A| |B|` scale.
-/

open Finset
open scoped BigOperators SimpleGraph

namespace InducedStars.Regularity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The sum of the real adjacency indicator over a rectangle is its number
of oriented interedges. -/
theorem sum_adjIndicator_eq_card_interedges
    (G : SimpleGraph V) [DecidableRel G.Adj] (s t : Finset V) :
    ∑ v ∈ s, ∑ w ∈ t, (if G.Adj v w then (1 : ℝ) else 0) =
      ((G.interedges s t).card : ℝ) := by
  rw [card_interedges_eq_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro v hv
  simp

/-- Expanding the centered adjacency-indicator sum into edge count minus
density times rectangle size. -/
theorem sum_centered_adjIndicator_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : Finset V) (d : ℝ) :
    ∑ v ∈ s, ∑ w ∈ t,
        ((if G.Adj v w then (1 : ℝ) else 0) - d) =
      ((G.interedges s t).card : ℝ) -
        d * (s.card : ℝ) * (t.card : ℝ) := by
  simp_rw [Finset.sum_sub_distrib]
  rw [sum_adjIndicator_eq_card_interedges]
  simp
  ring

omit [Fintype V] [DecidableEq V] in
/-- A centered adjacency sum is bounded by the cardinality of its rectangle. -/
theorem abs_card_interedges_sub_density_mul_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : Finset V) (d : ℝ) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    |((G.interedges s t).card : ℝ) -
        d * (s.card : ℝ) * (t.card : ℝ)| ≤
      (s.card : ℝ) * (t.card : ℝ) := by
  have hedge₀ : 0 ≤ ((G.interedges s t).card : ℝ) := by positivity
  have hedge₁ : ((G.interedges s t).card : ℝ) ≤
      (s.card : ℝ) * (t.card : ℝ) := by
    exact_mod_cast G.card_interedges_le_mul s t
  have hprod₀ : 0 ≤ (s.card : ℝ) * (t.card : ℝ) := by positivity
  have hdprod₀ : 0 ≤ d * (s.card : ℝ) * (t.card : ℝ) := by positivity
  have hdprod₁ : d * (s.card : ℝ) * (t.card : ℝ) ≤
      (s.card : ℝ) * (t.card : ℝ) := by
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- For a regular pair, every subrectangle has centered adjacency sum at
most `ε |A| |B|`.  Large subrectangles use regularity; if either side is
small, the trivial unit bound on each summand suffices. -/
theorem IsRegularPair.abs_sum_centered_adjIndicator_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} {A B s t : Finset V}
    (hreg : IsRegularPair G ε A B) (hε : 0 ≤ ε)
    (hs : s ⊆ A) (ht : t ⊆ B) :
    |∑ v ∈ s, ∑ w ∈ t,
        ((if G.Adj v w then (1 : ℝ) else 0) - graphDensity G A B)| ≤
      ε * (A.card : ℝ) * (B.card : ℝ) := by
  rw [sum_centered_adjIndicator_eq]
  let d := graphDensity G A B
  have hd₀ : 0 ≤ d := graphDensity_nonneg G A B
  have hd₁ : d ≤ 1 := graphDensity_le_one G A B
  by_cases hsLarge : ε * (A.card : ℝ) ≤ (s.card : ℝ)
  · by_cases htLarge : ε * (B.card : ℝ) ≤ (t.card : ℝ)
    · by_cases hsne : s.Nonempty
      · by_cases htne : t.Nonempty
        · have hregular : |graphDensity G s t - d| ≤ ε :=
            hreg hs ht hsLarge htLarge
          have hspos : 0 < (s.card : ℝ) := by exact_mod_cast hsne.card_pos
          have htpos : 0 < (t.card : ℝ) := by exact_mod_cast htne.card_pos
          have hfactor :
              ((G.interedges s t).card : ℝ) -
                  d * (s.card : ℝ) * (t.card : ℝ) =
                (graphDensity G s t - d) *
                  ((s.card : ℝ) * (t.card : ℝ)) := by
            rw [graphDensity_eq]
            field_simp
          rw [hfactor, abs_mul, abs_of_nonneg (by positivity :
            0 ≤ (s.card : ℝ) * (t.card : ℝ))]
          calc
            |graphDensity G s t - d| * ((s.card : ℝ) * (t.card : ℝ)) ≤
                ε * ((s.card : ℝ) * (t.card : ℝ)) := by gcongr
            _ ≤ ε * ((A.card : ℝ) * (B.card : ℝ)) := by
              gcongr
            _ = ε * (A.card : ℝ) * (B.card : ℝ) := by ring
        · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
          subst t
          calc
            |((G.interedges s ∅).card : ℝ) -
                d * (s.card : ℝ) * ((∅ : Finset V).card : ℝ)| ≤
                (s.card : ℝ) * ((∅ : Finset V).card : ℝ) :=
              abs_card_interedges_sub_density_mul_le G s ∅ d hd₀ hd₁
            _ = 0 := by simp
            _ ≤ ε * (A.card : ℝ) * (B.card : ℝ) := by positivity
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
        subst s
        calc
          |((G.interedges ∅ t).card : ℝ) -
              d * ((∅ : Finset V).card : ℝ) * (t.card : ℝ)| ≤
              ((∅ : Finset V).card : ℝ) * (t.card : ℝ) :=
            abs_card_interedges_sub_density_mul_le G ∅ t d hd₀ hd₁
          _ = 0 := by simp
          _ ≤ ε * (A.card : ℝ) * (B.card : ℝ) := by positivity
    · have htSmall : (t.card : ℝ) < ε * (B.card : ℝ) := lt_of_not_ge htLarge
      calc
        |((G.interedges s t).card : ℝ) -
            d * (s.card : ℝ) * (t.card : ℝ)| ≤
            (s.card : ℝ) * (t.card : ℝ) :=
          abs_card_interedges_sub_density_mul_le G s t d hd₀ hd₁
        _ ≤ (A.card : ℝ) * (ε * (B.card : ℝ)) := by
          gcongr
        _ = ε * (A.card : ℝ) * (B.card : ℝ) := by ring
  · have hsSmall : (s.card : ℝ) < ε * (A.card : ℝ) := lt_of_not_ge hsLarge
    calc
      |((G.interedges s t).card : ℝ) -
          d * (s.card : ℝ) * (t.card : ℝ)| ≤
          (s.card : ℝ) * (t.card : ℝ) :=
        abs_card_interedges_sub_density_mul_le G s t d hd₀ hd₁
      _ ≤ (ε * (A.card : ℝ)) * (B.card : ℝ) := by
        gcongr
      _ = ε * (A.card : ℝ) * (B.card : ℝ) := by ring

end InducedStars.Regularity
