import InducedStars.C4.DefectModels
import DenseGraph.Combinatorics.BoundedMatchingCounting

/-!
# Low-degree internal defect geometry

The maximum of the two side matching numbers is the source matching index.
The endpoints of maximum matchings on both sides cover every internal
defect, using at most four times that index many vertices.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]

def c4SideMatchingNumber (D : C4Division V) (T : SimpleGraph V) : ℕ :=
  max (DenseGraph.matchingNumber (c4WithinGraph T D.independentPart))
    (DenseGraph.matchingNumber (c4WithinGraph T D.cliquePart))

theorem c4SideMatchingNumber_le_iff (D : C4Division V) (T : SimpleGraph V) (k : ℕ) :
    c4SideMatchingNumber D T ≤ k ↔
      DenseGraph.matchingNumber (c4WithinGraph T D.independentPart) ≤ k ∧
        DenseGraph.matchingNumber (c4WithinGraph T D.cliquePart) ≤ k := max_le_iff

theorem c4SideMatchingNumber_eq_imp_matching (D : C4Division V) (T : SimpleGraph V)
    {k : ℕ} (hk : c4SideMatchingNumber D T = k) :
    k ≤ DenseGraph.matchingNumber (c4WithinGraph T D.independentPart) ∨
      k ≤ DenseGraph.matchingNumber (c4WithinGraph T D.cliquePart) := by
  rw [← hk]
  unfold c4SideMatchingNumber
  exact le_max_iff.mp le_rfl

theorem c4WithinGraph_le (T : SimpleGraph V) (S : Finset V) : c4WithinGraph T S ≤ T := by
  intro x y h
  exact h.2.2

theorem C4DefectSupported.within_sup_eq {D : C4Division V} {T : SimpleGraph V}
    (hT : C4DefectSupported D T) :
    c4WithinGraph T D.independentPart ⊔ c4WithinGraph T D.cliquePart = T := by
  ext x y
  constructor
  · rintro (h | h) <;> exact h.2.2
  · intro h
    rcases hT x y h with hside | hside
    · exact Or.inl ⟨hside.1,hside.2,h⟩
    · exact Or.inr ⟨hside.1,hside.2,h⟩

theorem C4DefectSupported.edgeCount_eq {D : C4Division V} {T : SimpleGraph V}
    (hT : C4DefectSupported D T) :
    (finiteGraphEdges T).card =
      (finiteGraphEdges (c4WithinGraph T D.independentPart)).card +
        (finiteGraphEdges (c4WithinGraph T D.cliquePart)).card := by
  have he : finiteGraphEdges T = finiteGraphEdges (c4WithinGraph T D.independentPart) ∪
      finiteGraphEdges (c4WithinGraph T D.cliquePart) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [mem_union, mk_mem_finiteGraphEdges]
      change T.Adj x y ↔ (c4WithinGraph T D.independentPart ⊔
        c4WithinGraph T D.cliquePart).Adj x y
      rw [hT.within_sup_eq]
  rw [he, card_union_of_disjoint]
  apply disjoint_left.mpr
  intro e ha hb
  induction e using Sym2.inductionOn with
  | _ x y =>
    have ha := (mk_mem_finiteGraphEdges _ x y).mp ha
    have hb := (mk_mem_finiteGraphEdges _ x y).mp hb
    exact disjoint_left.mp D.disjoint ha.1 hb.1

def c4DefectMatchingCover (D : C4Division V) (T : SimpleGraph V) : Finset V :=
  DenseGraph.canonicalMatchingCover (c4WithinGraph T D.independentPart) ∪
    DenseGraph.canonicalMatchingCover (c4WithinGraph T D.cliquePart)

theorem c4DefectMatchingCover_vertexCover {D : C4Division V} {T : SimpleGraph V}
    (hT : C4DefectSupported D T) :
    T.IsVertexCover (c4DefectMatchingCover D T : Set V) := by
  intro x y hxy
  rcases hT x y hxy with hside | hside
  · rcases DenseGraph.canonicalMatchingCover_vertexCover (c4WithinGraph T D.independentPart)
      ⟨hside.1,hside.2,hxy⟩ with hx | hy
    · exact Or.inl (mem_union_left _ hx)
    · exact Or.inr (mem_union_left _ hy)
  · rcases DenseGraph.canonicalMatchingCover_vertexCover (c4WithinGraph T D.cliquePart)
      ⟨hside.1,hside.2,hxy⟩ with hx | hy
    · exact Or.inl (mem_union_right _ hx)
    · exact Or.inr (mem_union_right _ hy)

theorem c4DefectMatchingCover_card_le (D : C4Division V) (T : SimpleGraph V)
    {k : ℕ} (hk : c4SideMatchingNumber D T ≤ k) :
    (c4DefectMatchingCover D T).card ≤ 4*k := by
  obtain ⟨ha,hb⟩ := (c4SideMatchingNumber_le_iff D T k).mp hk
  have h := card_union_le (DenseGraph.canonicalMatchingCover (c4WithinGraph T D.independentPart))
    (DenseGraph.canonicalMatchingCover (c4WithinGraph T D.cliquePart))
  simp only [DenseGraph.card_canonicalMatchingCover] at h
  unfold c4DefectMatchingCover
  omega

theorem c4LowDegreeDefect_edgeCount_le {n k : ℕ} {D : C4Division (Fin n)}
    {T : SimpleGraph (Fin n)} {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hT : C4DefectSupported D T) (hk : c4SideMatchingNumber D T ≤ k)
    (hdegree : ∀ v, (T.degree v : ℝ) ≤ alpha*n) :
    ((finiteGraphEdges T).card : ℝ) ≤ 4*(k : ℝ)*alpha*n := by
  have hside (S : Finset (Fin n)) :
      ((finiteGraphEdges (c4WithinGraph T S)).card : ℝ) ≤
        (2*DenseGraph.matchingNumber (c4WithinGraph T S) : ℕ)*(alpha*n) := by
    have h := DenseGraph.edgeFinset_card_le_matching_degree (c4WithinGraph T S)
        (d := alpha) (fun v ↦ (show ((c4WithinGraph T S).degree v : ℝ) ≤ T.degree v by
          exact_mod_cast SimpleGraph.degree_le_of_le (c4WithinGraph_le T S)).trans
            (by simpa using hdegree v))
    have he : finiteGraphEdges (c4WithinGraph T S) =
        @SimpleGraph.edgeFinset (Fin n) (c4WithinGraph T S) (c4WithinGraph T S).fintypeEdgeSet := by
      ext e
      simp [finiteGraphEdges]
    rw [he]
    simpa only [Fintype.card_fin] using h
  have ha := hside D.independentPart
  have hb := hside D.cliquePart
  obtain ⟨hka,hkb⟩ := (c4SideMatchingNumber_le_iff D T k).mp hk
  have hkaR : (DenseGraph.matchingNumber (c4WithinGraph T D.independentPart) : ℝ) ≤ k :=
    by exact_mod_cast hka
  have hkbR : (DenseGraph.matchingNumber (c4WithinGraph T D.cliquePart) : ℝ) ≤ k :=
    by exact_mod_cast hkb
  rw [hT.edgeCount_eq, Nat.cast_add]
  push_cast at ha hb
  nlinarith [mul_le_mul_of_nonneg_right hkaR (by positivity : 0 ≤ alpha*(n : ℝ)),
    mul_le_mul_of_nonneg_right hkbR (by positivity : 0 ≤ alpha*(n : ℝ))]

def c4LowDegreeDefectFinset {n : ℕ} (D : C4Division (Fin n)) (alpha : ℝ) (k : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  univ.filter fun T ↦ C4DefectSupported D T ∧ c4SideMatchingNumber D T ≤ k ∧
    ∀ v, (T.degree v : ℝ) ≤ alpha*n

def c4LowDegreeDefectPatternFinset {n : ℕ} (D : C4Division (Fin n)) (alpha : ℝ) (k : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  (c4LowDegreeDefectFinset D alpha k).filter fun T ↦ c4SideMatchingNumber D T=k

@[simp] theorem mem_c4LowDegreeDefectFinset {n k : ℕ} {D : C4Division (Fin n)}
    {alpha : ℝ} {T : SimpleGraph (Fin n)} :
    T ∈ c4LowDegreeDefectFinset D alpha k ↔ C4DefectSupported D T ∧
      c4SideMatchingNumber D T ≤ k ∧ ∀ v, (T.degree v : ℝ) ≤ alpha*n := by
  simp [c4LowDegreeDefectFinset]

@[simp] theorem mem_c4LowDegreeDefectPatternFinset {n k : ℕ} {D : C4Division (Fin n)}
    {alpha : ℝ} {T : SimpleGraph (Fin n)} :
    T ∈ c4LowDegreeDefectPatternFinset D alpha k ↔ C4DefectSupported D T ∧
      c4SideMatchingNumber D T=k ∧ ∀ v, (T.degree v : ℝ) ≤ alpha*n := by
  simp only [c4LowDegreeDefectPatternFinset, mem_filter, mem_c4LowDegreeDefectFinset]
  constructor
  · rintro ⟨⟨hT,_,hdeg⟩,hk⟩; exact ⟨hT,hk,hdeg⟩
  · rintro ⟨hT,hk,hdeg⟩; exact ⟨⟨hT,hk.le,hdeg⟩,hk⟩

end InducedStars
