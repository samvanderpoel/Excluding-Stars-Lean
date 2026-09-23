import InducedStars.Structure.Subcritical.Division
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Replacing a division component by a finite regular graph

The replacement graph need not be connected. Its connected components are
repackaged as connected regular cores with singleton parts. Every untouched
component retains its original core and parts. Empty replacement graphs are
allowed whenever another original component survives.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical

namespace InducedStars

namespace RegularBlockCore

/-- Reindex a finite connected regular graph onto a standard `Fin` core. -/
def ofFiniteConnectedRegular {k : ℕ} {W : Type*} [Fintype W] [Nonempty W]
    (Q : SimpleGraph W) (hc : Q.Connected) (hr : Q.IsRegularOfDegree (k - 2)) :
    RegularBlockCore k where
  order := Fintype.card W
  order_pos := Fintype.card_pos
  graph := Q.comap (Fintype.equivFin W).symm
  connected := (SimpleGraph.Iso.comap (Fintype.equivFin W).symm Q).connected_iff.mpr hc
  regular v := ((SimpleGraph.Iso.comap (Fintype.equivFin W).symm Q).degree_eq v).symm.trans
    (hr.degree_eq ((Fintype.equivFin W).symm v))

/-- A connected component of a finite regular graph is regular of the same degree. -/
theorem connectedComponent_regular {W : Type*} [Fintype W] (Q : SimpleGraph W)
    {d : ℕ} (hr : Q.IsRegularOfDegree d) (C : Q.ConnectedComponent) :
    C.toSimpleGraph.IsRegularOfDegree d := by
  intro v
  change (Q.induce C.supp).degree v = d
  rw [Q.degree_induce_of_neighborSet_subset]
  · exact hr.degree_eq v.1
  · intro w hw
    exact C.mem_supp_of_adj_mem_supp v.2 hw

def ofRegularComponent {k : ℕ} {W : Type*} [Fintype W]
    (Q : SimpleGraph W) (hr : Q.IsRegularOfDegree (k - 2))
    (C : Q.ConnectedComponent) : RegularBlockCore k := by
  letI : Nonempty C := ⟨⟨C.out, C.out_eq⟩⟩
  exact ofFiniteConnectedRegular C.toSimpleGraph C.connected_toSimpleGraph
    (connectedComponent_regular Q hr C)

end RegularBlockCore

namespace SubcriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Package an arbitrary finite nonempty index family using standard `Fin` indices. -/
def ofFiniteCoreFamily {I : Type*} [Fintype I] (hi : Nonempty I)
    (cores : I → RegularBlockCore k)
    (parts : (i : I) → Fin (cores i).order → Finset V)
    (hn : ∀ i j, (parts i j).Nonempty)
    (hd : Set.PairwiseDisjoint (Set.univ : Set (Σ i, Fin (cores i).order))
      (fun a ↦ parts a.1 a.2)) : SubcriticalDivision k V where
  componentCount := Fintype.card I
  componentCount_pos := Fintype.card_pos_iff.mpr hi
  core i := cores ((Fintype.equivFin I).symm i)
  parts i j := parts ((Fintype.equivFin I).symm i) j
  parts_nonempty i j := hn _ j
  parts_pairwiseDisjoint := by
    intro a _ b _ hab
    apply hd (x := ⟨(Fintype.equivFin I).symm a.1, a.2⟩)
      (y := ⟨(Fintype.equivFin I).symm b.1, b.2⟩) (Set.mem_univ _) (Set.mem_univ _)
    intro heq
    exact hab ((Equiv.sigmaCongrLeft (Fintype.equivFin I).symm).injective heq)

theorem ofFiniteCoreFamily_support {I : Type*} [Fintype I] (hi : Nonempty I)
    (cores : I → RegularBlockCore k)
    (parts : (i : I) → Fin (cores i).order → Finset V) (hn hd) (v : V) :
    v ∈ (ofFiniteCoreFamily hi cores parts hn hd).support ↔
      ∃ i j, v ∈ parts i j := by
  rw [mem_support_iff]
  change (∃ i j, v ∈ parts ((Fintype.equivFin I).symm i) j) ↔ _
  constructor
  · rintro ⟨i, j, h⟩; exact ⟨_, j, h⟩
  · rintro ⟨i, j, h⟩
    refine ⟨Fintype.equivFin I i, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact ⟨j, h⟩

theorem ofFiniteCoreFamily_samePart {I : Type*} [Fintype I] (hi : Nonempty I)
    (cores : I → RegularBlockCore k)
    (parts : (i : I) → Fin (cores i).order → Finset V) (hn hd) (x y : V) :
    (ofFiniteCoreFamily hi cores parts hn hd).SamePart x y ↔
      ∃ i j, x ∈ parts i j ∧ y ∈ parts i j := by
  change (∃ a : (ofFiniteCoreFamily hi cores parts hn hd).PartIndex,
    x ∈ (ofFiniteCoreFamily hi cores parts hn hd).part a ∧
      y ∈ (ofFiniteCoreFamily hi cores parts hn hd).part a) ↔ _
  simp only [Sigma.exists]
  change (∃ i j, x ∈ parts ((Fintype.equivFin I).symm i) j ∧
    y ∈ parts ((Fintype.equivFin I).symm i) j) ↔ _
  constructor
  · rintro ⟨i, j, h⟩; exact ⟨_, j, h⟩
  · rintro ⟨i, j, h⟩
    refine ⟨Fintype.equivFin I i, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact ⟨j, h⟩

theorem ofFiniteCoreFamily_activePair {I : Type*} [Fintype I] (hi : Nonempty I)
    (cores : I → RegularBlockCore k)
    (parts : (i : I) → Fin (cores i).order → Finset V) (hn hd) (x y : V) :
    (ofFiniteCoreFamily hi cores parts hn hd).ActivePair x y ↔
      ∃ i a b, (cores i).graph.Adj a b ∧ x ∈ parts i a ∧ y ∈ parts i b := by
  change (∃ i a b, (cores ((Fintype.equivFin I).symm i)).graph.Adj a b ∧
    x ∈ parts ((Fintype.equivFin I).symm i) a ∧
      y ∈ parts ((Fintype.equivFin I).symm i) b) ↔ _
  constructor
  · rintro ⟨i, a, b, h⟩; exact ⟨_, a, b, h⟩
  · rintro ⟨i, a, b, h⟩
    refine ⟨Fintype.equivFin I i, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact ⟨a, b, h⟩

/-- Untouched old components together with the connected components of the replacement graph. -/
abbrev ComponentReplacementIndex (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (S : Finset V) (H : SimpleGraph S) :=
  {j : Fin D.componentCount // j ≠ i} ⊕ H.ConnectedComponent

noncomputable instance componentReplacementIndexFintype (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (S : Finset V) (H : SimpleGraph S) :
    Fintype (D.ComponentReplacementIndex i S H) := Fintype.ofFinite _

def replacementSingletonVertex {S : Finset V} (H : SimpleGraph S)
    (hr : H.IsRegularOfDegree (k - 2)) (C : H.ConnectedComponent)
    (a : Fin (RegularBlockCore.ofRegularComponent H hr C).order) : V :=
  ((Fintype.equivFin C).symm a).1.1

theorem replacementSingletonVertex_mem {S : Finset V} (H : SimpleGraph S)
    (hr : H.IsRegularOfDegree (k - 2)) (C : H.ConnectedComponent)
    (a : Fin (RegularBlockCore.ofRegularComponent H hr C).order) :
    replacementSingletonVertex H hr C a ∈ S :=
  ((Fintype.equivFin C).symm a).1.2

theorem replacementSingletonVertex_injective {S : Finset V} (H : SimpleGraph S)
    (hr : H.IsRegularOfDegree (k - 2)) :
    Function.Injective (fun a : Σ C : H.ConnectedComponent,
      Fin (RegularBlockCore.ofRegularComponent H hr C).order ↦
        replacementSingletonVertex H hr a.1 a.2) := by
  rintro ⟨C, a⟩ ⟨E, b⟩ h
  have hbase : ((Fintype.equivFin C).symm a).1 = ((Fintype.equivFin E).symm b).1 :=
    Subtype.ext h
  have hCE : C = E := by
    have hC := ((Fintype.equivFin C).symm a).2
    have hE := ((Fintype.equivFin E).symm b).2
    change H.connectedComponentMk _ = C at hC
    change H.connectedComponentMk _ = E at hE
    rw [hbase] at hC
    exact hC.symm.trans hE
  subst E
  have hab : a = b := (Fintype.equivFin C).symm.injective (Subtype.ext hbase)
  subst b
  rfl

def replacementCore (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    (S : Finset V) (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2)) :
    D.ComponentReplacementIndex i S H → RegularBlockCore k
  | Sum.inl j => D.core j.1
  | Sum.inr C => RegularBlockCore.ofRegularComponent H hr C

def replacementPart (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    (S : Finset V) (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2)) :
    (j : D.ComponentReplacementIndex i S H) →
      Fin (D.replacementCore i S H hr j).order → Finset V
  | Sum.inl j, a => D.parts j.1 a
  | Sum.inr C, a => {replacementSingletonVertex H hr C a}

theorem replacementPart_nonempty (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    (S : Finset V) (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2))
    (j : D.ComponentReplacementIndex i S H) (a : Fin (D.replacementCore i S H hr j).order) :
    (D.replacementPart i S H hr j a).Nonempty := by
  cases j with
  | inl j => exact D.parts_nonempty j.1 a
  | inr C => exact Finset.singleton_nonempty _

theorem replacementPart_pairwiseDisjoint (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2)) :
    Set.PairwiseDisjoint (Set.univ : Set (Σ j, Fin (D.replacementCore i S H hr j).order))
      (fun a ↦ D.replacementPart i S H hr a.1 a.2) := by
  rintro ⟨j, a⟩ _ ⟨l, b⟩ _ hne
  apply Finset.disjoint_left.mpr
  intro x hx hy
  cases j with
  | inl j =>
    cases l with
    | inl l =>
      have hab := D.mem_part_unique (a := ⟨j.1, a⟩) (b := ⟨l.1, b⟩) hx hy
      have hjl : j = l := Subtype.ext (congrArg Sigma.fst hab)
      subst l
      have hab' : a = b := eq_of_heq (Sigma.mk.inj hab).2
      subst b
      exact hne rfl
    | inr C =>
      have hxy : x = replacementSingletonVertex H hr C b := Finset.mem_singleton.mp hy
      have hxi := hS (hxy ▸ replacementSingletonVertex_mem H hr C b)
      exact Finset.disjoint_left.mp (D.componentSupport_disjoint j.2)
        (D.mem_componentSupport.mpr ⟨a, hx⟩) hxi
  | inr C =>
    cases l with
    | inl l =>
      have hxy : x = replacementSingletonVertex H hr C a := Finset.mem_singleton.mp hx
      have hxi := hS (hxy ▸ replacementSingletonVertex_mem H hr C a)
      exact Finset.disjoint_left.mp (D.componentSupport_disjoint l.2)
        (D.mem_componentSupport.mpr ⟨b, hy⟩) hxi
    | inr E =>
      have hx' := Finset.mem_singleton.mp hx
      have hy' := Finset.mem_singleton.mp hy
      have heq := replacementSingletonVertex_injective H hr
        (a₁ := ⟨C, a⟩) (a₂ := ⟨E, b⟩) (hx'.symm.trans hy')
      have hCE : C = E := congrArg Sigma.fst heq
      subst E
      have hab : a = b := eq_of_heq (Sigma.mk.inj heq).2
      subst b
      exact hne rfl

/-- Replace `i` by the connected regular components of `H`, on singleton parts.
The nonemptiness witness is an untouched original component. -/
def replaceComponent (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2))
    (hother : ∃ j : Fin D.componentCount, j ≠ i) : SubcriticalDivision k V :=
  ofFiniteCoreFamily (by
    obtain ⟨j, hj⟩ := hother
    exact ⟨Sum.inl ⟨j, hj⟩⟩)
    (D.replacementCore i S H hr) (D.replacementPart i S H hr)
    (D.replacementPart_nonempty i S H hr) (D.replacementPart_pairwiseDisjoint i S hS H hr)

theorem replacementSingletonVertex_surjective {S : Finset V} (H : SimpleGraph S)
    (hr : H.IsRegularOfDegree (k - 2)) {x : V} (hx : x ∈ S) :
    ∃ (C : H.ConnectedComponent) (a : Fin (RegularBlockCore.ofRegularComponent H hr C).order),
      replacementSingletonVertex H hr C a = x := by
  let C := H.connectedComponentMk ⟨x, hx⟩
  let v : C := ⟨⟨x, hx⟩, rfl⟩
  refine ⟨C, (Fintype.equivFin C) v, ?_⟩
  dsimp only [replacementSingletonVertex]
  rw [Equiv.symm_apply_apply]

theorem replaceComponent_mem_support (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2)) (hother)
    (x : V) :
    x ∈ (D.replaceComponent i S hS H hr hother).support ↔
      (x ∈ D.support ∧ x ∉ D.componentSupport i) ∨ x ∈ S := by
  rw [replaceComponent, ofFiniteCoreFamily_support]
  constructor
  · rintro ⟨j, a, hx⟩
    cases j with
    | inl j =>
      exact Or.inl ⟨D.mem_support_iff.mpr ⟨j.1, a, hx⟩, fun hxi ↦
        Finset.disjoint_left.mp (D.componentSupport_disjoint j.2)
          (D.mem_componentSupport.mpr ⟨a, hx⟩) hxi⟩
    | inr C =>
      have heq : x = replacementSingletonVertex H hr C a := Finset.mem_singleton.mp hx
      exact Or.inr (heq ▸ replacementSingletonVertex_mem H hr C a)
  · rintro (⟨hs, hni⟩ | hx)
    · obtain ⟨j, a, hxa⟩ := D.mem_support_iff.mp hs
      have hji : j ≠ i := by rintro rfl; exact hni (D.mem_componentSupport.mpr ⟨a, hxa⟩)
      exact ⟨Sum.inl ⟨j, hji⟩, a, hxa⟩
    · obtain ⟨C, a, ha⟩ := replacementSingletonVertex_surjective H hr hx
      exact ⟨Sum.inr C, a, Finset.mem_singleton.mpr ha.symm⟩

theorem replaceComponent_support (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2)) (hother) :
    (D.replaceComponent i S hS H hr hother).support =
      (D.support \ D.componentSupport i) ∪ S := by
  ext x
  simp only [replaceComponent_mem_support, Finset.mem_union, Finset.mem_sdiff]

theorem replaceComponent_sparse (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2)) (hother) :
    (D.replaceComponent i S hS H hr hother).sparse =
      D.sparse ∪ (D.componentSupport i \ S) := by
  ext x
  have hfull : x ∈ D.componentSupport i → x ∈ D.support :=
    fun hx ↦ D.componentSupport_subset_support i hx
  have hsub : x ∈ S → x ∈ D.componentSupport i := fun hx ↦ hS hx
  simp only [mem_sparse, replaceComponent_mem_support, Finset.mem_union, Finset.mem_sdiff]
  tauto

theorem replaceComponent_samePart (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2)) (hother)
    (x y : V) :
    (D.replaceComponent i S hS H hr hother).SamePart x y ↔
      (D.SamePart x y ∧ x ∉ D.componentSupport i) ∨ (x = y ∧ x ∈ S) := by
  rw [replaceComponent, ofFiniteCoreFamily_samePart]
  constructor
  · rintro ⟨j, a, hx, hy⟩
    cases j with
    | inl j =>
      exact Or.inl ⟨⟨⟨j.1, a⟩, hx, hy⟩, fun hxi ↦
        Finset.disjoint_left.mp (D.componentSupport_disjoint j.2)
          (D.mem_componentSupport.mpr ⟨a, hx⟩) hxi⟩
    | inr C =>
      have hx' : x = replacementSingletonVertex H hr C a := Finset.mem_singleton.mp hx
      have hy' : y = replacementSingletonVertex H hr C a := Finset.mem_singleton.mp hy
      exact Or.inr ⟨hx'.trans hy'.symm, hx' ▸ replacementSingletonVertex_mem H hr C a⟩
  · rintro (⟨⟨a, hx, hy⟩, hni⟩ | ⟨rfl, hx⟩)
    · have hai : a.1 ≠ i := by
        intro heq
        apply hni
        rw [← heq]
        exact D.mem_componentSupport.mpr ⟨a.2, hx⟩
      exact ⟨Sum.inl ⟨a.1, hai⟩, a.2, hx, hy⟩
    · obtain ⟨C, a, ha⟩ := replacementSingletonVertex_surjective H hr hx
      exact ⟨Sum.inr C, a, Finset.mem_singleton.mpr ha.symm,
        Finset.mem_singleton.mpr ha.symm⟩

theorem replaceComponent_activePair (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2)) (hother)
    (x y : V) :
    (D.replaceComponent i S hS H hr hother).ActivePair x y ↔
      (D.ActivePair x y ∧ x ∉ D.componentSupport i) ∨ H.spanningCoe.Adj x y := by
  rw [replaceComponent, ofFiniteCoreFamily_activePair]
  constructor
  · rintro ⟨j, a, b, hab, hx, hy⟩
    cases j with
    | inl j =>
      exact Or.inl ⟨⟨j.1, a, b, hab, hx, hy⟩, fun hxi ↦
        Finset.disjoint_left.mp (D.componentSupport_disjoint j.2)
          (D.mem_componentSupport.mpr ⟨a, hx⟩) hxi⟩
    | inr C =>
      have hx' : x = replacementSingletonVertex H hr C a := Finset.mem_singleton.mp hx
      have hy' : y = replacementSingletonVertex H hr C b := Finset.mem_singleton.mp hy
      apply Or.inr
      rw [SimpleGraph.spanningCoe, SimpleGraph.map_adj]
      exact ⟨((Fintype.equivFin C).symm a).1, ((Fintype.equivFin C).symm b).1,
        hab, hx'.symm, hy'.symm⟩
  · rintro (⟨⟨j, a, b, hab, hx, hy⟩, hni⟩ | hxy)
    · have hji : j ≠ i := by rintro rfl; exact hni (D.mem_componentSupport.mpr ⟨a, hx⟩)
      exact ⟨Sum.inl ⟨j, hji⟩, a, b, hab, hx, hy⟩
    · rw [SimpleGraph.spanningCoe, SimpleGraph.map_adj] at hxy
      obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
      let C := H.connectedComponentMk u
      let u' : C := ⟨u, rfl⟩
      let v' : C := ⟨v, (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm⟩
      refine ⟨Sum.inr C, (Fintype.equivFin C) u', (Fintype.equivFin C) v', ?_, ?_, ?_⟩
      · change H.Adj ((Fintype.equivFin C).symm ((Fintype.equivFin C) u')).1
          ((Fintype.equivFin C).symm ((Fintype.equivFin C) v')).1
        simpa only [Equiv.symm_apply_apply] using huv
      · change u.1 ∈ {replacementSingletonVertex H hr C ((Fintype.equivFin C) u')}
        simp only [Finset.mem_singleton, replacementSingletonVertex, Equiv.symm_apply_apply]
        rfl
      · change v.1 ∈ {replacementSingletonVertex H hr C ((Fintype.equivFin C) v')}
        simp only [Finset.mem_singleton, replacementSingletonVertex, Equiv.symm_apply_apply]
        rfl

/-- Every untouched part occurs verbatim in the replacement division. -/
theorem replaceComponent_exists_untouched_part (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2)) (hother)
    (a : D.PartIndex) (hai : a.1 ≠ i) :
    ∃ b : (D.replaceComponent i S hS H hr hother).PartIndex,
      (D.replaceComponent i S hS H hr hother).part b = D.part a := by
  let J := D.ComponentReplacementIndex i S H
  let e : (Σ j : Fin (Fintype.card J),
      Fin (D.replacementCore i S H hr ((Fintype.equivFin J).symm j)).order) ≃
      Σ j : J, Fin (D.replacementCore i S H hr j).order :=
    Equiv.sigmaCongrLeft (β := fun j : J ↦ Fin (D.replacementCore i S H hr j).order)
      (Fintype.equivFin J).symm
  let b := e.symm ⟨Sum.inl ⟨a.1, hai⟩, a.2⟩
  refine ⟨b, ?_⟩
  have he := e.apply_symm_apply (⟨Sum.inl ⟨a.1, hai⟩, a.2⟩ :
    Σ j : J, Fin (D.replacementCore i S H hr j).order)
  have hp := congrArg (fun z : Σ j : J, Fin (D.replacementCore i S H hr j).order ↦
    D.replacementPart i S H hr z.1 z.2) he
  exact hp

end SubcriticalDivision
end InducedStars
