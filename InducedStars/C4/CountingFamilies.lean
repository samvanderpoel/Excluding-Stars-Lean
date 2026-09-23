import InducedStars.C4.TypeGrouping
import InducedStars.C4.NondegenerateFamilies
import InducedStars.C4.LowDegreeGeometry
import InducedStars.C4.Relocation

/-!
# Canonical finite families for the final C4 decomposition

Paper: the families in the final counting argument and `eqn:c4-union-bound`.
Every family consists of actual induced-C4-free labeled graphs at the exact
edge count. Canonical divisions are globally optimal; nondegeneracy and
defect tolerances are independent, as in the paper's sequential parameter hierarchy.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

def c4CloseDivisionGraphFinset (n m : ℕ) (gamma epsilon zeta : ℝ)
    (D : C4Division (Fin n)) : Finset (SimpleGraph (Fin n)) :=
  (inducedC4FreeGraphFinsetWithEdges n m).filter fun G ↦
    canonicalC4Division G = D ∧ (c4DefectCost G D : ℝ) ≤ epsilon*(n : ℝ)^2 ∧
      |(D.cliquePart.card : ℝ)-c4Lambda gamma*n| ≤ zeta*n

@[simp] theorem mem_c4CloseDivisionGraphFinset {n m : ℕ} {gamma epsilon zeta : ℝ}
    {D : C4Division (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ c4CloseDivisionGraphFinset n m gamma epsilon zeta D ↔
      G ∈ inducedC4FreeGraphFinsetWithEdges n m ∧ canonicalC4Division G = D ∧
        (c4DefectCost G D : ℝ) ≤ epsilon*(n : ℝ)^2 ∧
          |(D.cliquePart.card : ℝ)-c4Lambda gamma*n| ≤ zeta*n := by
  simp [c4CloseDivisionGraphFinset]

theorem c4CloseDivision_minimal {n m : ℕ} {gamma epsilon zeta : ℝ}
    {D : C4Division (Fin n)} {G : SimpleGraph (Fin n)}
    (hG : G ∈ c4CloseDivisionGraphFinset n m gamma epsilon zeta D)
    (E : C4Division (Fin n)) : c4DefectCost G D ≤ c4DefectCost G E := by
  rw [← (mem_c4CloseDivisionGraphFinset.mp hG).2.1]
  exact canonicalC4Division_minimal G E

theorem c4CloseDivision_mem_fixedDefectFiber {n m : ℕ} {gamma epsilon zeta : ℝ}
    {D : C4Division (Fin n)} {G : SimpleGraph (Fin n)}
    (hG : G ∈ c4CloseDivisionGraphFinset n m gamma epsilon zeta D) :
    G ∈ c4FixedDefectFreeFiber D (c4DefectGraph G D) m := by
  have h := mem_inducedC4FreeGraphFinsetWithEdges.mp
    (mem_c4CloseDivisionGraphFinset.mp hG).1
  exact mem_c4FixedDefectFreeFiber.mpr ⟨⟨rfl, h.2⟩, h.1⟩

theorem c4_nondegenerate_ratio_iff {n : ℕ} (hn : 0 < n) (D : C4Division (Fin n))
    (gamma zeta : ℝ) :
    |(D.cliquePart.card : ℝ)/n-c4Lambda gamma| ≤ zeta ↔
      |(D.cliquePart.card : ℝ)-c4Lambda gamma*n| ≤ zeta*n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h : (D.cliquePart.card : ℝ)/n-c4Lambda gamma =
      ((D.cliquePart.card : ℝ)-c4Lambda gamma*n)/n := by field_simp
  rw [h, abs_div, abs_of_pos hnR, div_le_iff₀ hnR]

def c4HighIndependentGraphFinset (n m : ℕ) (gamma epsilon zeta alpha : ℝ)
    (D : C4Division (Fin n)) : Finset (SimpleGraph (Fin n)) :=
  (c4CloseDivisionGraphFinset n m gamma epsilon zeta D).filter fun G ↦
    ∃ v ∈ D.independentPart, alpha*D.independentPart.card ≤
      ((c4DefectGraph G D).degree v : ℝ)

def c4HighCliqueGraphFinset (n m : ℕ) (gamma epsilon zeta alpha : ℝ)
    (D : C4Division (Fin n)) : Finset (SimpleGraph (Fin n)) :=
  (c4CloseDivisionGraphFinset n m gamma epsilon zeta D).filter fun G ↦
    ∃ v ∈ D.cliquePart, alpha*D.cliquePart.card ≤ ((c4DefectGraph G D).degree v : ℝ)

@[simp] theorem mem_c4HighIndependentGraphFinset {n m : ℕ} {gamma epsilon zeta alpha : ℝ}
    {D : C4Division (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D ↔
      G ∈ c4CloseDivisionGraphFinset n m gamma epsilon zeta D ∧
        ∃ v ∈ D.independentPart, alpha*D.independentPart.card ≤
          ((c4DefectGraph G D).degree v : ℝ) := by
  simp only [c4HighIndependentGraphFinset, mem_filter]

@[simp] theorem mem_c4HighCliqueGraphFinset {n m : ℕ} {gamma epsilon zeta alpha : ℝ}
    {D : C4Division (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D ↔
      G ∈ c4CloseDivisionGraphFinset n m gamma epsilon zeta D ∧
        ∃ v ∈ D.cliquePart, alpha*D.cliquePart.card ≤
          ((c4DefectGraph G D).degree v : ℝ) := by
  simp only [c4HighCliqueGraphFinset, mem_filter]

private theorem degree_univ (G : SimpleGraph (Fin n)) (v : Fin n) :
    degreeInFinset G v univ = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold degreeInFinset
  congr 1
  ext y
  simp

theorem c4DefectGraph_degree_eq_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (D : C4Division (Fin n)) {v : Fin n} (hv : v ∈ D.independentPart) :
    (c4DefectGraph G D).degree v = degreeInFinset G v D.independentPart := by
  rw [← degree_univ]
  exact c4DefectGraph_degree_of_mem_independent G D hv

theorem c4DefectGraph_degree_eq_clique {n : ℕ} (G : SimpleGraph (Fin n))
    (D : C4Division (Fin n)) {v : Fin n} (hv : v ∈ D.cliquePart) :
    (c4DefectGraph G D).degree v = complementDegreeInFinset G v D.cliquePart := by
  rw [← degree_univ]
  exact c4DefectGraph_degree_of_mem_clique G D hv

def c4LowDegreeMatchingGraphFinset (n m : ℕ) (gamma epsilon zeta alpha : ℝ)
    (D : C4Division (Fin n)) (q : ℕ) : Finset (SimpleGraph (Fin n)) :=
  (c4CloseDivisionGraphFinset n m gamma epsilon zeta D).filter fun G ↦
    (∀ v, ((c4DefectGraph G D).degree v : ℝ) ≤ alpha*n) ∧
      c4SideMatchingNumber D (c4DefectGraph G D) = q

@[simp] theorem mem_c4LowDegreeMatchingGraphFinset {n m q : ℕ}
    {gamma epsilon zeta alpha : ℝ} {D : C4Division (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D q ↔
      G ∈ c4CloseDivisionGraphFinset n m gamma epsilon zeta D ∧
        (∀ v, ((c4DefectGraph G D).degree v : ℝ) ≤ alpha*n) ∧
          c4SideMatchingNumber D (c4DefectGraph G D) = q := by
  simp only [c4LowDegreeMatchingGraphFinset, mem_filter]

theorem c4SideMatchingNumber_le_order {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) : c4SideMatchingNumber D T ≤ n := by
  have hb (H : SimpleGraph (Fin n)) : DenseGraph.matchingNumber H ≤ n := by
    have h := card_le_univ (s := DenseGraph.canonicalMatchingCover H)
    rw [DenseGraph.card_canonicalMatchingCover, Fintype.card_fin] at h
    omega
  exact max_le (hb _) (hb _)

theorem c4SideMatchingNumber_pos_of_nonsplit {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : ¬DenseGraph.IsSplitGraph G) :
    0 < c4SideMatchingNumber (canonicalC4Division G)
      (c4DefectGraph G (canonicalC4Division G)) := by
  by_contra h
  have hz : c4SideMatchingNumber (canonicalC4Division G)
      (c4DefectGraph G (canonicalC4Division G)) = 0 := by omega
  have hzero := (c4SideMatchingNumber_le_iff _ _ 0).mp hz.le
  have ha := (DenseGraph.matchingNumber_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hzero.1)
  have hb := (DenseGraph.matchingNumber_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero hzero.2)
  have hsup := (c4DefectGraph_supported G (canonicalC4Division G)).within_sup_eq
  rw [ha, hb, sup_idem] at hsup
  apply hG
  apply (canonicalC4Division_defect_zero_iff G).mp
  exact (c4DefectCost_eq_zero_iff _ _).mpr hsup.symm

/-- The genuine finite master inclusion behind `eqn:c4-union-bound`.
Its low-degree branch may overcount graphs, but assumes no penalty. -/
theorem c4Graph_master_decomposition {n m : ℕ} {gamma epsilon zeta alpha : ℝ}
    (halpha : 0 ≤ alpha) {G : SimpleGraph (Fin n)}
    (hG : G ∈ inducedC4FreeGraphFinsetWithEdges n m) :
    DenseGraph.IsSplitGraph G ∨ G ∈ c4FarGraphFinset n m epsilon ∨
      G ∈ c4CloseDegenerateGraphFinset n m gamma epsilon zeta ∨
      ∃ D : C4Division (Fin n),
        G ∈ c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D ∨
        G ∈ c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D ∨
        ∃ q ∈ Finset.Icc 1 n,
          G ∈ c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D q := by
  by_cases hsplit : DenseGraph.IsSplitGraph G
  · exact Or.inl hsplit
  right
  by_cases hfar : G ∈ c4FarGraphFinset n m epsilon
  · exact Or.inl hfar
  right
  have hcost : (c4DefectCost G (canonicalC4Division G) : ℝ) ≤ epsilon*(n : ℝ)^2 := by
    by_contra h
    exact hfar (mem_c4FarGraphFinset.mpr ⟨hG, (not_le.mp h).le⟩)
  by_cases hdeg : G ∈ c4CloseDegenerateGraphFinset n m gamma epsilon zeta
  · exact Or.inl hdeg
  right
  let D := canonicalC4Division G
  have hnondeg : |(D.cliquePart.card : ℝ)-c4Lambda gamma*n| ≤ zeta*n := by
    by_contra h
    exact hdeg (mem_c4CloseDegenerateGraphFinset.mpr ⟨hG, hcost, not_le.mp h⟩)
  have hclose : G ∈ c4CloseDivisionGraphFinset n m gamma epsilon zeta D :=
    mem_c4CloseDivisionGraphFinset.mpr ⟨hG, rfl, hcost, hnondeg⟩
  refine ⟨D, ?_⟩
  by_cases hA : G ∈ c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D
  · exact Or.inl hA
  right
  by_cases hB : G ∈ c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D
  · exact Or.inl hB
  right
  let q := c4SideMatchingNumber D (c4DefectGraph G D)
  refine ⟨q, mem_Icc.mpr ⟨c4SideMatchingNumber_pos_of_nonsplit G hsplit,
    c4SideMatchingNumber_le_order D _⟩, mem_c4LowDegreeMatchingGraphFinset.mpr
      ⟨hclose, ?_, rfl⟩⟩
  intro v
  have hparts := D.card_add
  simp only [Fintype.card_fin] at hparts
  by_cases hv : v ∈ D.independentPart
  · have hlt : ((c4DefectGraph G D).degree v : ℝ) < alpha*D.independentPart.card := by
      by_contra h
      exact hA (mem_c4HighIndependentGraphFinset.mpr ⟨hclose, v, hv, not_lt.mp h⟩)
    exact hlt.le.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast (show D.independentPart.card ≤ n by omega)) halpha)
  · have hvB : v ∈ D.cliquePart := (D.mem_cliquePart v).mpr hv
    have hlt : ((c4DefectGraph G D).degree v : ℝ) < alpha*D.cliquePart.card := by
      by_contra h
      exact hB (mem_c4HighCliqueGraphFinset.mpr ⟨hclose, v, hvB, not_lt.mp h⟩)
    exact hlt.le.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast (show D.cliquePart.card ≤ n by omega)) halpha)

end InducedStars
