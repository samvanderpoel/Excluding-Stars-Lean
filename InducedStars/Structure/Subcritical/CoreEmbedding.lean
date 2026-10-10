import InducedStars.Structure.Subcritical.Division
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Degree saturation and exact identification of component cores

Paper: the component-identification step in the proof of
`lemma:WtoWtildeMetricsK1k`.  The input is the actual injective cell-to-part
map, together with preservation of core edges.  Equal finite degrees give
neighbor closure, and connectedness identifies the whole target component.
No graph is identified from its degree alone.
-/

noncomputable section

open Function

namespace SimpleGraph.Hom

variable {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
variable [G.LocallyFinite] [H.LocallyFinite]

/-- An injective graph homomorphism preserving the degree at a vertex maps
its neighbor set onto the target neighbor set. -/
theorem mapNeighborSet_surjective_of_injective_of_degree_eq
    (f : G →g H) (hf : Injective f) (v : A)
    (hdegree : G.degree v = H.degree (f v)) :
    Surjective (f.mapNeighborSet v) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ?_).2
  constructor
  · intro a b hab
    apply Subtype.ext
    exact hf (congrArg Subtype.val hab)
  · simpa only [SimpleGraph.card_neighborSet_eq_degree] using hdegree

/-- Equal degrees force the image of an injective homomorphism to be
closed under taking neighbors. -/
theorem exists_adj_preimage_of_injective_of_degree_eq
    (f : G →g H) (hf : Injective f)
    (hdegree : ∀ v, G.degree v = H.degree (f v))
    {v : A} {w : B} (hadj : H.Adj (f v) w) :
    ∃ u, G.Adj v u ∧ f u = w := by
  obtain ⟨u, hu⟩ :=
    f.mapNeighborSet_surjective_of_injective_of_degree_eq hf v (hdegree v) ⟨w, hadj⟩
  exact ⟨u, u.property, congrArg Subtype.val hu⟩

/-- Degree saturation upgrades an injective homomorphism to an induced
embedding: extra edges between image vertices are impossible. -/
theorem map_adj_iff_of_injective_of_degree_eq
    (f : G →g H) (hf : Injective f)
    (hdegree : ∀ v, G.degree v = H.degree (f v)) (u v : A) :
    H.Adj (f u) (f v) ↔ G.Adj u v := by
  constructor
  · intro huv
    obtain ⟨w, huw, hw⟩ :=
      f.exists_adj_preimage_of_injective_of_degree_eq hf hdegree huv
    simpa only [hf hw] using huw
  · exact f.map_adj

/-- A nonempty neighbor-closed image in a preconnected graph is the entire
vertex set.  Here neighbor closure follows from equal degrees. -/
theorem surjective_of_injective_of_degree_eq_of_preconnected
    [Nonempty A] (f : G →g H) (hf : Injective f)
    (hdegree : ∀ v, G.degree v = H.degree (f v))
    (hH : H.Preconnected) : Surjective f := by
  have hwalk : ∀ {x y : B}, H.Walk x y →
      (∃ v, f v = x) → ∃ v, f v = y := by
    intro x y p
    induction p with
    | nil => exact id
    | @cons x y z hxy p ih =>
      rintro ⟨v, rfl⟩
      obtain ⟨w, _, hw⟩ :=
        f.exists_adj_preimage_of_injective_of_degree_eq hf hdegree hxy
      exact ih ⟨w, hw⟩
  let a : A := Classical.choice inferInstance
  intro b
  obtain ⟨p⟩ := hH (f a) b
  exact hwalk p ⟨a, rfl⟩

/-- An actual graph isomorphism obtained from an injective degree-preserving
homomorphism into a connected target.  Its forward map is the given map. -/
def isoOfInjectiveOfDegreeEqOfPreconnected
    [Nonempty A] (f : G →g H) (hf : Injective f)
    (hdegree : ∀ v, G.degree v = H.degree (f v))
    (hH : H.Preconnected) : G ≃g H where
  __ := Equiv.ofBijective f
    ⟨hf, f.surjective_of_injective_of_degree_eq_of_preconnected hf hdegree hH⟩
  map_rel_iff' := f.map_adj_iff_of_injective_of_degree_eq hf hdegree _ _

@[simp] theorem isoOfInjectiveOfDegreeEqOfPreconnected_apply
    [Nonempty A] (f : G →g H) (hf : Injective f)
    (hdegree : ∀ v, G.degree v = H.degree (f v))
    (hH : H.Preconnected) (v : A) :
    f.isoOfInjectiveOfDegreeEqOfPreconnected hf hdegree hH v = f v := rfl

end SimpleGraph.Hom

namespace InducedStars.SubcriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A map from a connected core preserving active pairs has all its images
in the same division component.  This conclusion uses no degree assumption. -/
theorem component_eq_of_reachable_activePart_map
    (D : SubcriticalDivision k V) {A : Type*} (Q : SimpleGraph A)
    (f : A → D.PartIndex)
    (hadj : ∀ {u v}, Q.Adj u v → D.ActivePart (f u) (f v))
    {u v : A} (hpath : Q.Reachable u v) : (f u).1 = (f v).1 := by
  obtain ⟨p⟩ := hpath
  induction p with
  | nil => rfl
  | cons h _ ih => exact (D.activePart_same_component (hadj h)).trans ih

/-- Paper: degree-saturation step in `lemma:WtoWtildeMetricsK1k`.
An injective edge-preserving map from a regular candidate core into the
global part indices identifies one whole division component.  The retained
isomorphism has exactly the original map as its global part-index map. -/
theorem exists_coreIso_of_injective_activePart_map
    (D : SubcriticalDivision k V) (Q : RegularBlockCore k)
    (f : Fin Q.order → D.PartIndex) (hf : Injective f)
    (hadj : ∀ {u v}, Q.graph.Adj u v → D.ActivePart (f u) (f v)) :
    ∃ (i : Fin D.componentCount) (e : Q.graph ≃g (D.core i).graph),
      ∀ v, f v = ⟨i, e v⟩ := by
  classical
  let v₀ : Fin Q.order := ⟨0, Q.order_pos⟩
  let i : Fin D.componentCount := (f v₀).1
  have hi (v : Fin Q.order) : (f v).1 = i :=
    D.component_eq_of_reachable_activePart_map Q.graph f hadj
      (Q.connected.preconnected v v₀)
  let g (v : Fin Q.order) : Fin (D.core i).order :=
    ⟨(f v).2.val, by simpa only [← hi v] using (f v).2.isLt⟩
  have hfg (v : Fin Q.order) : f v = ⟨i, g v⟩ := by
    refine Sigma.ext ?_ ?_
    · exact hi v
    · exact (Fin.heq_ext_iff (congrArg (fun j ↦ (D.core j).order) (hi v))).mpr rfl
  have hg : Injective g := by
    intro u v huv
    apply hf
    rw [hfg u, hfg v, huv]
  let F : Q.graph →g (D.core i).graph :=
    ⟨g, by
      intro u v huv
      have huv' := hadj huv
      rw [hfg u, hfg v, D.activePart_mk_mk] at huv'
      exact huv'⟩
  let : Nonempty (Fin Q.order) := ⟨v₀⟩
  have hdegree (v : Fin Q.order) :
      Q.graph.degree v = (D.core i).graph.degree (F v) := by
    rw [Q.degree_eq, (D.core i).degree_eq]
  refine ⟨i, F.isoOfInjectiveOfDegreeEqOfPreconnected hg hdegree
    (D.core i).connected.preconnected, ?_⟩
  exact hfg

/-- The image neighbors are exactly the mapped source neighbors, retaining
the actual cell-to-part map rather than merely an existential isomorphism. -/
theorem activePart_iff_exists_adj_preimage_of_injective_map
    (D : SubcriticalDivision k V) (Q : RegularBlockCore k)
    (f : Fin Q.order → D.PartIndex) (hf : Injective f)
    (hadj : ∀ {u v}, Q.graph.Adj u v → D.ActivePart (f u) (f v))
    (u : Fin Q.order) (b : D.PartIndex) :
    D.ActivePart (f u) b ↔ ∃ v, Q.graph.Adj u v ∧ f v = b := by
  obtain ⟨i, e, he⟩ := D.exists_coreIso_of_injective_activePart_map Q f hf hadj
  constructor
  · intro hab
    rw [he u] at hab
    obtain ⟨j, a, c, ha, rfl, hac⟩ := hab
    have hij : i = j := congrArg Sigma.fst ha
    subst j
    have hua : e u = a := by simpa using ha
    subst a
    refine ⟨e.symm c, ?_, ?_⟩
    · exact e.map_adj_iff.mp (by simpa using hac)
    · rw [he]
      simp
  · rintro ⟨v, huv, rfl⟩
    exact hadj huv

/-- Adjacency reflection for the global part-index map obtained by matching
candidate cells. -/
theorem activePart_map_iff_of_injective_map
    (D : SubcriticalDivision k V) (Q : RegularBlockCore k)
    (f : Fin Q.order → D.PartIndex) (hf : Injective f)
    (hadj : ∀ {u v}, Q.graph.Adj u v → D.ActivePart (f u) (f v))
    (u v : Fin Q.order) :
    D.ActivePart (f u) (f v) ↔ Q.graph.Adj u v := by
  rw [D.activePart_iff_exists_adj_preimage_of_injective_map Q f hf hadj]
  constructor
  · rintro ⟨w, huw, hw⟩
    simpa only [hf hw] using huw
  · exact fun huv ↦ ⟨v, huv, rfl⟩

end InducedStars.SubcriticalDivision
