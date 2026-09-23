import InducedStars.Structure.Subcritical.ProfileExponents
import DenseGraph.Combinatorics.BinomialEntropy

/-!
# Rooted-pattern choices and natural free energy

Paper: `eqn:troot-bound` and `eqn:root-free-energy-identity-K1k`.
Each rooted edge has a unique root endpoint. Its exact recorded neighbor
coordinate determines whether it is present or an own-part missing edge.
All entropy and exponential weights below use natural units.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}

/-- The trimmed own part is empty outside the retained-root domain. -/
def subcriticalProfileOwnTarget (p : SubcriticalProfile D eta R₀ theta) (v : V) : Finset V :=
  if hv : v ∈ p.retainedRoots then
    D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots
  else ∅

/-- An absent row has no neighbor coordinate. A recorded zero row still
retains its actual target and a fixed zero-size choice. -/
def subcriticalProfilePresentTarget (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (a : D.PartIndex) : Finset V :=
  if (p.rows v a).isSome then D.part a \ p.roots else ∅

def subcriticalProfileOwnChoice (G : SimpleGraph V)
    (p : SubcriticalProfile D eta R₀ theta) (v : V) : Finset V :=
  (subcriticalProfileOwnTarget p v).filter fun y ↦ y ≠ v ∧ ¬ G.Adj v y

def subcriticalProfilePresentChoice (G : SimpleGraph V)
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex) : Finset V :=
  (subcriticalProfilePresentTarget p v a).filter (G.Adj v)

namespace RealizesSubcriticalProfile

variable {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}

theorem row_isSome_iff (h : RealizesSubcriticalProfile G alpha p) (v : V) (a : D.PartIndex) :
    (p.rows v a).isSome ↔
      (v ∈ p.retainedRoots ∧ D.EligibleProfileTarget eta R₀ theta v a ∧
        4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) ∨
      (v ∈ p.outsideRoots ∧ a ∈ D.retainedPartIndices eta R₀ ∧
        4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) := by
  by_cases hv : v ∈ p.retainedRoots
  · have ho := Finset.disjoint_left.mp p.roots_disjoint hv
    rw [h.retained_rows v hv a]
    simp only [hv, ho, true_and, false_and, or_false]
    split_ifs <;> simp_all
  · by_cases ho : v ∈ p.outsideRoots
    · rw [h.outside_rows v ho a]
      simp only [hv, ho, true_and, false_and, false_or]
      split_ifs <;> simp_all
    · rw [p.rows_eq_none_of_not_mem_roots (by simpa using And.intro hv ho)]
      simp [hv, ho]

theorem row_count_eq_degree_of_some (h : RealizesSubcriticalProfile G alpha p)
    {v : V} {a : D.PartIndex} {r : Fin (Fintype.card V + 1)}
    (hr : p.rows v a = some r) :
    r.val = degreeInFinset G v (D.part a \ p.roots) := by
  rcases (p.rows_valid v a r hr).1 with hv | hv
  · have he := h.retained_rows v hv.1 a
    rw [hr] at he
    split_ifs at he with hc
    · exact congrArg (fun z : Option (Fin (Fintype.card V + 1)) ↦ (z.getD 0).val) he
  · have he := h.outside_rows v hv.1 a
    rw [hr] at he
    split_ifs at he with hc
    · exact congrArg (fun z : Option (Fin (Fintype.card V + 1)) ↦ (z.getD 0).val) he

theorem own_choice_card (h : RealizesSubcriticalProfile G alpha p) (v : V) :
    (subcriticalProfileOwnChoice G p v).card = (p.ownCount v).val := by
  unfold subcriticalProfileOwnChoice subcriticalProfileOwnTarget
  split_ifs with hv
  · exact (h.own_counts v hv).symm
  · simp [p.ownCount_zero v hv]

theorem present_choice_card (h : RealizesSubcriticalProfile G alpha p)
    (v : V) (a : D.PartIndex) :
    (subcriticalProfilePresentChoice G p v a).card = p.rowCount v a := by
  cases hr : p.rows v a with
  | none => simp [subcriticalProfilePresentChoice, subcriticalProfilePresentTarget,
      SubcriticalProfile.rowCount, hr]
  | some r =>
      simpa [subcriticalProfilePresentChoice, subcriticalProfilePresentTarget,
        SubcriticalProfile.rowCount, hr, degreeInFinset] using (h.row_count_eq_degree_of_some hr).symm

/-- The exact oriented neighbor reconstruction from the profile choices. -/
theorem recorded_neighbors_iff_choices (h : RealizesSubcriticalProfile G alpha p) (v y : V) :
    y ∈ subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v ↔
      y ∈ subcriticalProfileOwnChoice G p v ∨
        ∃ a, y ∈ subcriticalProfilePresentChoice G p v a := by
  constructor
  · intro hy
    obtain ⟨hyB, hcases⟩ := (Finset.mem_filter.mp hy).2
    have hyB' : y ∉ p.roots := by rwa [h.roots_eq]
    rcases hcases with ⟨hv, hown | hrow⟩ | ⟨hv, hrow⟩
    · have hv' : v ∈ p.retainedRoots := by rwa [h.retained_roots]
      obtain ⟨hvret, hypart, hne, hG⟩ := hown
      apply Or.inl
      simp only [subcriticalProfileOwnChoice, subcriticalProfileOwnTarget, dif_pos hv',
        Finset.mem_filter, Finset.mem_sdiff]
      exact ⟨⟨hypart, hyB'⟩, hne, hG⟩
    · have hv' : v ∈ p.retainedRoots := by rwa [h.retained_roots]
      obtain ⟨a, ha, hhigh, hypart, hG⟩ := hrow
      have hrs := (h.row_isSome_iff v a).mpr (Or.inl ⟨hv', ha, hhigh⟩)
      exact Or.inr ⟨a, by simp [subcriticalProfilePresentChoice,
        subcriticalProfilePresentTarget, hrs, hypart, hyB', hG]⟩
    · have hv' : v ∈ p.outsideRoots := by rwa [h.outside_roots]
      obtain ⟨a, ha, hhigh, hypart, hG⟩ := hrow
      have hrs := (h.row_isSome_iff v a).mpr (Or.inr ⟨hv', ha, hhigh⟩)
      exact Or.inr ⟨a, by simp [subcriticalProfilePresentChoice,
        subcriticalProfilePresentTarget, hrs, hypart, hyB', hG]⟩
  · rintro (hy | ⟨a, hy⟩)
    · unfold subcriticalProfileOwnChoice subcriticalProfileOwnTarget at hy
      split_ifs at hy with hv
      · obtain ⟨⟨hypart, hyB⟩, hne, hG⟩ := by
          simpa only [Finset.mem_filter, Finset.mem_sdiff] using hy
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, Or.inl ⟨?_, Or.inl ⟨_, hypart, hne, hG⟩⟩⟩
        · rwa [← h.roots_eq]
        · rwa [← h.retained_roots]
      · simpa using hy
    · unfold subcriticalProfilePresentChoice subcriticalProfilePresentTarget at hy
      split_ifs at hy with hrs
      · obtain ⟨⟨hypart, hyB⟩, hG⟩ := by
          simpa only [Finset.mem_filter, Finset.mem_sdiff] using hy
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · rwa [← h.roots_eq]
        rcases (h.row_isSome_iff v a).mp hrs with ⟨hv, ha, hhigh⟩ | ⟨hv, ha, hhigh⟩
        · exact Or.inl ⟨by rwa [← h.retained_roots], Or.inr ⟨a, ha, hhigh, hypart, hG⟩⟩
        · exact Or.inr ⟨by rwa [← h.outside_roots], a, ha, hhigh, hypart, hG⟩
      · simpa using hy

end RealizesSubcriticalProfile

/-- Explicit product code: own missing neighbors and all recorded present rows. -/
def subcriticalRootChoiceCode (G : SimpleGraph V)
    (p : SubcriticalProfile D eta R₀ theta) :
    (V → Finset V) × (V → D.PartIndex → Finset V) :=
  (subcriticalProfileOwnChoice G p, subcriticalProfilePresentChoice G p)

/-- The finite fixed-size product containing every rooted pattern code. -/
def subcriticalRootChoiceCodeFinset (p : SubcriticalProfile D eta R₀ theta) :
    Finset ((V → Finset V) × (V → D.PartIndex → Finset V)) :=
  (Fintype.piFinset fun v ↦
    (subcriticalProfileOwnTarget p v).powersetCard (p.ownCount v).val) ×ˢ
    (Fintype.piFinset fun v ↦ Fintype.piFinset fun a ↦
      (subcriticalProfilePresentTarget p v a).powersetCard (p.rowCount v a))

theorem subcriticalRootChoiceCode_mem {G : SimpleGraph V}
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p) :
    subcriticalRootChoiceCode G p ∈ subcriticalRootChoiceCodeFinset p := by
  simp only [subcriticalRootChoiceCode, subcriticalRootChoiceCodeFinset,
    Finset.mem_product, Fintype.mem_piFinset, Finset.mem_powersetCard]
  exact ⟨fun v ↦ ⟨Finset.filter_subset _ _, h.own_choice_card v⟩,
    fun v a ↦ ⟨Finset.filter_subset _ _, h.present_choice_card v a⟩⟩

theorem subcriticalRootChoiceCode_determines_rooted {G G' : SimpleGraph V}
    {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (h' : RealizesSubcriticalProfile G' alpha p)
    (heq : subcriticalRootChoiceCode G p = subcriticalRootChoiceCode G' p) :
    subcriticalRootedDefectGraph G D eta R₀ theta alpha =
      subcriticalRootedDefectGraph G' D eta R₀ theta alpha := by
  have ho := congrArg Prod.fst heq
  have hr := congrArg Prod.snd heq
  ext x y
  simp only [subcriticalRootedDefectGraph_adj, h.recorded_neighbors_iff_choices,
    h'.recorded_neighbors_iff_choices]
  change (_ ∨ _) ∨ (_ ∨ _) ↔ (_ ∨ _) ∨ (_ ∨ _)
  rw [show subcriticalProfileOwnChoice G p = subcriticalProfileOwnChoice G' p from ho,
    show subcriticalProfilePresentChoice G p = subcriticalProfilePresentChoice G' p from hr]

/-- The requested injection retains the actual graph witness only to choose
a coordinate representative. Equal coordinates force equal rooted patterns. -/
def subcriticalRootedPatternChoiceEmbedding (F : Finset (SimpleGraph V))
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) :
    ↥(subcriticalRootedDefectPatternFinset F alpha p) ↪
      ↥(subcriticalRootChoiceCodeFinset p) := by
  let g : ↥(subcriticalRootedDefectPatternFinset F alpha p) → SimpleGraph V :=
    fun T ↦ ((mem_subcriticalRootedDefectPatternFinset F alpha p T).mp T.property).choose
  have hg (T : ↥(subcriticalRootedDefectPatternFinset F alpha p)) :
      g T ∈ subcriticalProfileClassGraphFinset F alpha p ∧
        subcriticalRootedDefectGraph (g T) D eta R₀ theta alpha = T.val :=
    ((mem_subcriticalRootedDefectPatternFinset F alpha p T).mp T.property).choose_spec
  refine ⟨fun T ↦ ⟨subcriticalRootChoiceCode (g T) p,
    subcriticalRootChoiceCode_mem (mem_subcriticalProfileClassGraphFinset.mp (hg T).1).2⟩, ?_⟩
  intro T T' heq
  apply Subtype.ext
  rw [← (hg T).2, ← (hg T').2]
  exact subcriticalRootChoiceCode_determines_rooted
    (mem_subcriticalProfileClassGraphFinset.mp (hg T).1).2
    (mem_subcriticalProfileClassGraphFinset.mp (hg T').1).2
    (congrArg Subtype.val heq)

theorem subcriticalRootedPattern_card_le_code (F : Finset (SimpleGraph V))
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) :
    (subcriticalRootedDefectPatternFinset F alpha p).card ≤
      (subcriticalRootChoiceCodeFinset p).card := by
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
    (subcriticalRootedPatternChoiceEmbedding F alpha p)
    (subcriticalRootedPatternChoiceEmbedding F alpha p).injective

theorem subcriticalRootChoiceCodeFinset_card (p : SubcriticalProfile D eta R₀ theta) :
    (subcriticalRootChoiceCodeFinset p).card =
      (∏ v, (subcriticalProfileOwnTarget p v).card.choose (p.ownCount v).val) *
      ∏ v, ∏ a : D.PartIndex,
        (subcriticalProfilePresentTarget p v a).card.choose (p.rowCount v a) := by
  simp only [subcriticalRootChoiceCodeFinset, Finset.card_product,
    Fintype.card_piFinset, Finset.card_powersetCard]

private theorem own_choice_root_nonroot (G : SimpleGraph V)
    (p : SubcriticalProfile D eta R₀ theta) (v y : V)
    (hy : y ∈ subcriticalProfileOwnChoice G p v) :
    v ∈ p.roots ∧ y ∉ p.roots := by
  unfold subcriticalProfileOwnChoice subcriticalProfileOwnTarget at hy
  split_ifs at hy with hv
  · exact ⟨Finset.mem_union_left _ hv, (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2⟩
  · simpa using hy

private theorem own_choice_clique (G : SimpleGraph V)
    (p : SubcriticalProfile D eta R₀ theta) (v y : V)
    (hy : y ∈ subcriticalProfileOwnChoice G p v) :
    s(v, y) ∈ retainedCliquePotentialEdges D eta R₀ := by
  unfold subcriticalProfileOwnChoice subcriticalProfileOwnTarget at hy
  split_ifs at hy with hv
  · obtain ⟨hypart, hne, _⟩ := Finset.mem_filter.mp hy
    exact (mk_mem_retainedCliquePotentialEdges_iff D eta R₀ v y).mpr
      ⟨hne.symm, ⟨_, D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv),
        (Finset.mem_sdiff.mp hypart).1⟩, p.retainedRoots_subset hv⟩
  · simpa using hy

private def ownRootChoiceGraph (G : SimpleGraph V)
    (p : SubcriticalProfile D eta R₀ theta) : SimpleGraph V where
  Adj v y := y ∈ subcriticalProfileOwnChoice G p v ∨ v ∈ subcriticalProfileOwnChoice G p y
  symm := ⟨by intro v y hy; exact hy.symm⟩
  loopless := ⟨by
    intro v hv
    have h := own_choice_root_nonroot G p v v (hv.elim id id)
    exact h.2 h.1⟩

private theorem ownRootChoiceGraph_edges {G : SimpleGraph V}
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p) :
    finiteGraphEdges (ownRootChoiceGraph G p) =
      finiteGraphEdges (subcriticalRootedDefectGraph G D eta R₀ theta alpha) ∩
        retainedCliquePotentialEdges D eta R₀ := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    simp only [mk_mem_finiteGraphEdges, Finset.mem_inter]
    change (_ ∨ _) ↔ _
    constructor
    · rintro (hown | hown)
      · exact ⟨Or.inl ((h.recorded_neighbors_iff_choices x y).mpr (Or.inl hown)),
          own_choice_clique G p x y hown⟩
      · refine ⟨Or.inr ((h.recorded_neighbors_iff_choices y x).mpr (Or.inl hown)), ?_⟩
        rw [Sym2.eq_swap]
        exact own_choice_clique G p y x hown
    · rintro ⟨hroot, hclique⟩
      have hs := ((mk_mem_retainedCliquePotentialEdges_iff D eta R₀ x y).mp hclique).2.1
      have hdef := (subcriticalDefectGraph_adj_iff G D).mp
        (subcriticalRootedDefectGraph_le G D eta R₀ theta alpha hroot).1
      have hnG : ¬ G.Adj x y := hdef.1.2.elim (fun hm ↦ hm.2)
        (fun hp ↦ (hp.1 hs).elim)
      rcases hroot with hy | hx
      · rcases (h.recorded_neighbors_iff_choices x y).mp hy with ho | ⟨a, hp⟩
        · exact Or.inl ho
        · exact (hnG (Finset.mem_filter.mp hp).2).elim
      · rcases (h.recorded_neighbors_iff_choices y x).mp hx with ho | ⟨a, hp⟩
        · exact Or.inr ho
        · exact (hnG (Finset.mem_filter.mp hp).2.symm).elim

/-- Negative rooted edges are exactly the own-part missing coordinates. -/
theorem RealizesSubcriticalProfile.rooted_missing_count_eq {G : SimpleGraph V}
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p) :
    (finiteGraphEdges (subcriticalRootedDefectGraph G D eta R₀ theta alpha) ∩
      retainedCliquePotentialEdges D eta R₀).card =
        ∑ v ∈ p.retainedRoots, (p.ownCount v).val := by
  rw [← ownRootChoiceGraph_edges h,
    card_finiteGraphEdges_eq_sum_recordedNeighbors (ownRootChoiceGraph G p) p.roots
      (subcriticalProfileOwnChoice G p) (own_choice_root_nonroot G p)
      (fun _ _ ↦ Iff.rfl)]
  simp_rw [h.own_choice_card]
  rw [SubcriticalProfile.roots, Finset.sum_union p.roots_disjoint]
  have ho : ∑ v ∈ p.outsideRoots, (p.ownCount v).val = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [p.ownCount_zero v (Finset.disjoint_right.mp p.roots_disjoint hv)]
    rfl
  rw [ho, add_zero]

/-- Profile-determined signed mass: present row counts minus own missing counts. -/
def subcriticalProfileRootSignedSize (p : SubcriticalProfile D eta R₀ theta) : ℤ :=
  (∑ v ∈ p.roots, ∑ a : D.PartIndex, p.rowCount v a : ℕ) -
    (∑ v ∈ p.retainedRoots, (p.ownCount v).val : ℕ)

theorem RealizesSubcriticalProfile.rooted_signedSize_eq {G : SimpleGraph V}
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p) :
    subcriticalSignedDefectSize D eta R₀
      (subcriticalRootedDefectGraph G D eta R₀ theta alpha) =
        subcriticalProfileRootSignedSize p := by
  have hmass : p.rootedEdgeMass =
      (∑ v ∈ p.roots, ∑ a : D.PartIndex, p.rowCount v a) +
        ∑ v ∈ p.retainedRoots, (p.ownCount v).val := by
    simp only [SubcriticalProfile.rootedEdgeMass, SubcriticalProfile.roots,
      Finset.sum_union p.roots_disjoint, Finset.sum_add_distrib]
    omega
  rw [subcriticalSignedDefectSize, h.rooted_edge_count_eq, h.rooted_missing_count_eq,
    hmass, subcriticalProfileRootSignedSize, Nat.cast_add]
  ring

theorem subcriticalRootedPattern_signedSize_eq (F : Finset (SimpleGraph V))
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) {T : SimpleGraph V}
    (hT : T ∈ subcriticalRootedDefectPatternFinset F alpha p) :
    subcriticalSignedDefectSize D eta R₀ T = subcriticalProfileRootSignedSize p := by
  obtain ⟨G, hG, rfl⟩ := (mem_subcriticalRootedDefectPatternFinset F alpha p T).mp hT
  exact (mem_subcriticalProfileClassGraphFinset.mp hG).2.rooted_signedSize_eq

theorem subcriticalProfileOwnTarget_capacity (p : SubcriticalProfile D eta R₀ theta)
    (v : V) : (p.ownCount v).val ≤ (subcriticalProfileOwnTarget p v).card := by
  unfold subcriticalProfileOwnTarget
  split_ifs with hv
  · exact p.ownCount_capacity v hv
  · simp [p.ownCount_zero v hv]

theorem subcriticalProfilePresentTarget_capacity (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (a : D.PartIndex) :
    p.rowCount v a ≤ (subcriticalProfilePresentTarget p v a).card := by
  cases hr : p.rows v a with
  | none => simp [subcriticalProfilePresentTarget, SubcriticalProfile.rowCount, hr]
  | some r =>
    simpa [subcriticalProfilePresentTarget, SubcriticalProfile.rowCount, SubcriticalProfile.roots, hr]
      using (p.rows_valid v a r hr).2

/-- The product has no coordinates outside the roots: all those factors are
one. Recorded zero rows contribute their exact binomial coefficient one. -/
theorem subcriticalRootChoiceCodeFinset_card_eq_root_product
    (p : SubcriticalProfile D eta R₀ theta) :
    (subcriticalRootChoiceCodeFinset p).card =
      ∏ v ∈ p.roots,
        ((subcriticalProfileOwnTarget p v).card.choose (p.ownCount v).val) *
          ∏ a : D.PartIndex,
            (subcriticalProfilePresentTarget p v a).card.choose (p.rowCount v a) := by
  rw [subcriticalRootChoiceCodeFinset_card, ← Finset.prod_mul_distrib]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro v _ hv
  have hvret : v ∉ p.retainedRoots := fun h ↦ hv (Finset.mem_union_left _ h)
  simp [subcriticalProfileOwnTarget, hvret, p.ownCount_zero v hvret,
    subcriticalProfilePresentTarget, p.rows_eq_none_of_not_mem_roots hv,
    SubcriticalProfile.rowCount]

/-- Paper: `eqn:troot-bound`. The product is grouped by root; outside roots
have own factor one, and absent rows have factor one. This is precisely the
product over recorded rows and retained-root missing-edge choices. -/
theorem subcriticalRootedPattern_card_le_choose_product
    (F : Finset (SimpleGraph V)) (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) :
    (subcriticalRootedDefectPatternFinset F alpha p).card ≤
      ∏ v ∈ p.roots,
        ((subcriticalProfileOwnTarget p v).card.choose (p.ownCount v).val) *
          ∏ a : D.PartIndex,
            (subcriticalProfilePresentTarget p v a).card.choose (p.rowCount v a) := by
  rw [← subcriticalRootChoiceCodeFinset_card_eq_root_product]
  exact subcriticalRootedPattern_card_le_code F alpha p

/-- Unsigned coordinate entropy at one root, before the signed exponential
weight is applied. This is a finite counting exponent, measured in nats. -/
def subcriticalRootChoiceEntropyNat (p : SubcriticalProfile D eta R₀ theta) (v : V) : ℝ :=
  DenseGraph.binomialEntropyPerspective (subcriticalProfileOwnTarget p v).card
      (p.ownCount v).val +
    ∑ a : D.PartIndex, DenseGraph.binomialEntropyPerspective
      (subcriticalProfilePresentTarget p v a).card (p.rowCount v a)

theorem subcriticalRootChoiceCodeFinset_card_le_exp
    (p : SubcriticalProfile D eta R₀ theta) :
    ((subcriticalRootChoiceCodeFinset p).card : ℝ) ≤
      Real.exp (∑ v ∈ p.roots, subcriticalRootChoiceEntropyNat p v) := by
  rw [subcriticalRootChoiceCodeFinset_card_eq_root_product, Nat.cast_prod]
  rw [Real.exp_sum]
  apply Finset.prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _)
  intro v _
  rw [Nat.cast_mul, Nat.cast_prod, subcriticalRootChoiceEntropyNat, Real.exp_add,
    Real.exp_sum]
  exact mul_le_mul
    (DenseGraph.choose_le_exp_binomialEntropyPerspective (subcriticalProfileOwnTarget_capacity p v))
    (Finset.prod_le_prod (fun _ _ ↦ Nat.cast_nonneg _)
      (fun a _ ↦ DenseGraph.choose_le_exp_binomialEntropyPerspective
        (subcriticalProfilePresentTarget_capacity p v a)))
    (by positivity) (Real.exp_pos _).le

private theorem present_entropy_eq_perspective_sub (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (a : D.PartIndex) :
    subcriticalProfilePresentRowEntropyNat p v a =
      DenseGraph.binomialEntropyPerspective (subcriticalProfilePresentTarget p v a).card
        (p.rowCount v a) - subcriticalLogOddsNat k * p.rowCount v a := by
  cases hr : p.rows v a with
  | none => simp [subcriticalProfilePresentRowEntropyNat, subcriticalProfilePresentTarget,
      SubcriticalProfile.rowCount, DenseGraph.binomialEntropyPerspective, hr]
  | some r => simp [subcriticalProfilePresentRowEntropyNat, subcriticalProfilePresentTarget,
      SubcriticalProfile.rowCount, DenseGraph.binomialEntropyPerspective, hr]

private theorem own_entropy_eq_perspective_add (p : SubcriticalProfile D eta R₀ theta)
    (v : V) :
    subcriticalProfileOwnMissingEntropyNat p v =
      DenseGraph.binomialEntropyPerspective (subcriticalProfileOwnTarget p v).card
        (p.ownCount v).val + subcriticalLogOddsNat k * (p.ownCount v).val := by
  unfold subcriticalProfileOwnMissingEntropyNat subcriticalProfileOwnTarget
  split_ifs with hv
  · rfl
  · simp [p.ownCount_zero v hv, DenseGraph.binomialEntropyPerspective]

private theorem ownCount_sum_roots (p : SubcriticalProfile D eta R₀ theta) :
    ∑ v ∈ p.roots, (p.ownCount v).val = ∑ v ∈ p.retainedRoots, (p.ownCount v).val := by
  rw [SubcriticalProfile.roots, Finset.sum_union p.roots_disjoint]
  have ho : ∑ v ∈ p.outsideRoots, (p.ownCount v).val = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp [p.ownCount_zero v (Finset.disjoint_right.mp p.roots_disjoint hv)]
  rw [ho, add_zero]

/-- Exact finite entropy accounting: weighting all coordinates by their
signed defect count gives exactly the already-defined root entropy. -/
theorem subcriticalRootChoiceEntropyNat_sub_signedSize
    (p : SubcriticalProfile D eta R₀ theta) :
    (∑ v ∈ p.roots, subcriticalRootChoiceEntropyNat p v) -
      subcriticalLogOddsNat k * (subcriticalProfileRootSignedSize p : ℝ) =
        ∑ v ∈ p.roots, subcriticalProfileRootEntropyNat p v := by
  have hsigma : (subcriticalProfileRootSignedSize p : ℝ) =
      (∑ v ∈ p.roots, ∑ a : D.PartIndex, (p.rowCount v a : ℝ)) -
        ∑ v ∈ p.roots, ((p.ownCount v).val : ℝ) := by
    simp only [subcriticalProfileRootSignedSize, Int.cast_sub, Int.cast_natCast]
    rw [← ownCount_sum_roots]
    simp only [Nat.cast_sum]
  rw [hsigma]
  simp only [subcriticalRootChoiceEntropyNat, subcriticalProfileRootEntropyNat,
    present_entropy_eq_perspective_sub, own_entropy_eq_perspective_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Paper: `eqn:root-free-energy-identity-K1k`, corrected consistently to
natural-exponential units by exact conversion from the paper's base-two units. Empty families, roots and target sizes
are included, and no asymptotic or positivity-of-count assumption is used. -/
theorem subcriticalRootFreeEnergy_le
    (F : Finset (SimpleGraph V)) (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) :
    (∑ T ∈ subcriticalRootedDefectPatternFinset F alpha p,
      Real.exp (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ T : ℝ))) ≤
        Real.exp (∑ v ∈ p.roots, subcriticalProfileRootEntropyNat p v) := by
  have hcount : ((subcriticalRootedDefectPatternFinset F alpha p).card : ℝ) ≤
      Real.exp (∑ v ∈ p.roots, subcriticalRootChoiceEntropyNat p v) :=
    (Nat.cast_le.mpr (subcriticalRootedPattern_card_le_code F alpha p)).trans
      (subcriticalRootChoiceCodeFinset_card_le_exp p)
  calc
    _ = ((subcriticalRootedDefectPatternFinset F alpha p).card : ℝ) *
        Real.exp (-subcriticalLogOddsNat k * (subcriticalProfileRootSignedSize p : ℝ)) := by
      rw [Finset.sum_congr rfl (fun T hT ↦ by rw [subcriticalRootedPattern_signedSize_eq F alpha p hT])]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (∑ v ∈ p.roots, subcriticalRootChoiceEntropyNat p v) *
        Real.exp (-subcriticalLogOddsNat k * (subcriticalProfileRootSignedSize p : ℝ)) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, ← subcriticalRootChoiceEntropyNat_sub_signedSize]
      congr 1
      ring

end InducedStars
