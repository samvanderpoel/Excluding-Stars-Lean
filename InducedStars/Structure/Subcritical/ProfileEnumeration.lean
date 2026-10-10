import InducedStars.Structure.Subcritical.ProfileComplexity

/-!
# Finite profile encoding and uniform enumeration

Paper: Lemma `lemma:NtaunmWUpperBdK1k`, profile counting step.
Only stored scalar data are encoded: b, ell, and one visible-index row of
optional counts and tail symbols per root. In particular, `none` and `some 0`
remain distinct. No graph, neighbor subset, or matching is encoded.
-/

noncomputable section
open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- The finite alphabet for one root. Coordinates use only visible parts,
even when the total division index type grows with the graph order. -/
abbrev SubcriticalProfileRootCode (D : SubcriticalDivision k V) (theta : ℝ) :=
  V × ({a // a ∈ D.visiblePartIndices theta} → Option (Fin (Fintype.card V + 1))) ×
    Fin (Fintype.card V + 1) ×
    ({a // a ∈ D.visiblePartIndices theta} → Option SubcriticalTailDirection)

def subcriticalProfileRootEntry (p : SubcriticalProfile D eta R₀ theta) (v : V) :
    SubcriticalProfileRootCode D theta :=
  (v, fun a ↦ p.rows v a.val, p.ownCount v, fun a ↦ p.tails v a.val)

def subcriticalProfileRootEncoding (p : SubcriticalProfile D eta R₀ theta) :
    Finset (SubcriticalProfileRootCode D theta) :=
  p.roots.image (subcriticalProfileRootEntry p)

theorem card_subcriticalProfileRootEncoding (p : SubcriticalProfile D eta R₀ theta) :
    (subcriticalProfileRootEncoding p).card = p.roots.card := by
  apply Finset.card_image_of_injective
  intro v w h
  exact congrArg Prod.fst h

def subcriticalProfileEncoding (p : SubcriticalProfile D eta R₀ theta) :
    ℕ × ℕ × Finset (SubcriticalProfileRootCode D theta) :=
  (p.b, p.ell, subcriticalProfileRootEncoding p)

namespace SubcriticalProfile

theorem retainedRoots_eq_filter_roots (p : SubcriticalProfile D eta R₀ theta) :
    p.retainedRoots = p.roots.filter (fun v ↦ v ∈ D.retainedVertices eta R₀) := by
  ext v
  simp only [Finset.mem_filter, mem_roots]
  constructor
  · intro hv
    exact ⟨Or.inl hv, p.retainedRoots_subset hv⟩
  · rintro ⟨hv | hv, hret⟩
    · exact hv
    · exact ((D.mem_nonretainedVertices eta R₀ v).mp (p.outsideRoots_subset hv) hret).elim

theorem outsideRoots_eq_sdiff_retainedRoots (p : SubcriticalProfile D eta R₀ theta) :
    p.outsideRoots = p.roots \ p.retainedRoots := by
  ext v
  simp only [Finset.mem_sdiff, mem_roots]
  constructor
  · intro hv
    exact ⟨Or.inr hv, fun hret ↦ Finset.disjoint_left.mp p.roots_disjoint hret hv⟩
  · rintro ⟨hv | hv, hnot⟩
    · exact (hnot hv).elim
    · exact hv

theorem rows_eq_none_of_not_visible (p : SubcriticalProfile D eta R₀ theta)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (v : V) {a : D.PartIndex} (ha : a ∉ D.visiblePartIndices theta) :
    p.rows v a = none := by
  cases he : p.rows v a with
  | none => rfl
  | some r =>
    rcases (p.rows_valid v a r he).1 with h | h
    · obtain ⟨hv, htarget⟩ := h.2
      exact (ha ((D.mem_eligibleVisibleTargets eta R₀ theta v hv a).mp htarget).1).elim
    · exact (ha (hret h.2)).elim

theorem tails_eq_none_of_not_visible (p : SubcriticalProfile D eta R₀ theta)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (v : V) {a : D.PartIndex} (ha : a ∉ D.visiblePartIndices theta) :
    p.tails v a = none := by
  cases he : p.tails v a with
  | none => rfl
  | some t =>
    obtain ⟨hv, hactive⟩ := p.tails_valid v a t he
    have hsame := SubcriticalDivision.activePart_same_component hactive
    have hown := D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv)
    have haRet : a ∈ D.retainedPartIndices eta R₀ := by
      rw [D.mem_retainedPartIndices] at hown ⊢
      rwa [← hsame]
    exact (ha (hret haRet)).elim

end SubcriticalProfile

private theorem rootEntry_eq_of_encoding_eq
    {p q : SubcriticalProfile D eta R₀ theta}
    (h : subcriticalProfileRootEncoding p = subcriticalProfileRootEncoding q)
    {v : V} (hv : v ∈ p.roots) :
    v ∈ q.roots ∧ subcriticalProfileRootEntry p v = subcriticalProfileRootEntry q v := by
  have hm : subcriticalProfileRootEntry p v ∈ subcriticalProfileRootEncoding q := by
    rw [← h]
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hm
  have hwv : w = v := congrArg Prod.fst he
  subst w
  exact ⟨hw, he.symm⟩

/-- Injectivity uses the normalized values outside the root and visible
target domains. The retained/outside split is recovered from the division. -/
theorem subcriticalProfileEncoding_injective
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta) :
    Function.Injective (subcriticalProfileEncoding (D := D) (eta := eta)
      (R₀ := R₀) (theta := theta)) := by
  intro p q h
  obtain ⟨hb, hell, he⟩ := (show p.b = q.b ∧ p.ell = q.ell ∧
      subcriticalProfileRootEncoding p = subcriticalProfileRootEncoding q from
    by simpa only [subcriticalProfileEncoding, Prod.mk.injEq] using h)
  have hroot : p.roots = q.roots := by
    ext v
    exact ⟨fun hv ↦ (rootEntry_eq_of_encoding_eq he hv).1,
      fun hv ↦ (rootEntry_eq_of_encoding_eq he.symm hv).1⟩
  have hretRoot : p.retainedRoots = q.retainedRoots := by
    rw [p.retainedRoots_eq_filter_roots, q.retainedRoots_eq_filter_roots, hroot]
  have houtRoot : p.outsideRoots = q.outsideRoots := by
    rw [p.outsideRoots_eq_sdiff_retainedRoots, q.outsideRoots_eq_sdiff_retainedRoots,
      hroot, hretRoot]
  have hrows : p.rows = q.rows := by
    funext v a
    by_cases hv : v ∈ p.roots
    · by_cases ha : a ∈ D.visiblePartIndices theta
      · have hh := congrArg (fun e : SubcriticalProfileRootCode D theta ↦ e.2.1 ⟨a, ha⟩)
          (rootEntry_eq_of_encoding_eq he hv).2
        exact hh
      · rw [p.rows_eq_none_of_not_visible hret v ha, q.rows_eq_none_of_not_visible hret v ha]
    · rw [p.rows_eq_none_of_not_mem_roots hv,
        q.rows_eq_none_of_not_mem_roots (by rwa [← hroot])]
  have hown : p.ownCount = q.ownCount := by
    funext v
    by_cases hv : v ∈ p.roots
    · exact congrArg (fun e : SubcriticalProfileRootCode D theta ↦ e.2.2.1)
        (rootEntry_eq_of_encoding_eq he hv).2
    · have hvret : v ∉ p.retainedRoots := fun h ↦ hv (Finset.mem_union_left _ h)
      rw [p.ownCount_zero v hvret, q.ownCount_zero v (by rwa [← hretRoot])]
  have htails : p.tails = q.tails := by
    funext v a
    by_cases hv : v ∈ p.roots
    · by_cases ha : a ∈ D.visiblePartIndices theta
      · exact congrArg (fun e : SubcriticalProfileRootCode D theta ↦ e.2.2.2 ⟨a, ha⟩)
          (rootEntry_eq_of_encoding_eq he hv).2
      · rw [p.tails_eq_none_of_not_visible hret v ha, q.tails_eq_none_of_not_visible hret v ha]
    · have hvret : v ∉ p.retainedRoots := fun h ↦ hv (Finset.mem_union_left _ h)
      rw [p.tails_eq_none_of_not_mem_retainedRoots hvret,
        q.tails_eq_none_of_not_mem_retainedRoots (by rwa [← hretRoot])]
  cases p
  cases q
  simp only at hb hell hretRoot houtRoot hrows hown htails
  subst_vars
  rfl

/-- The exact root-alphabet size, including all three optional tail symbols. -/
theorem card_subcriticalProfileRootCode (D : SubcriticalDivision k V) (theta : ℝ) :
    Fintype.card (SubcriticalProfileRootCode D theta) =
      Fintype.card V * ((Fintype.card V + 2) ^ (D.visiblePartIndices theta).card *
        ((Fintype.card V + 1) * 3 ^ (D.visiblePartIndices theta).card)) := by
  have htail : Fintype.card SubcriticalTailDirection = 2 := by decide
  simp only [SubcriticalProfileRootCode, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_option, Fintype.card_fin, Fintype.card_coe, htail]

/-- An explicit raw product bound. The cubic polynomial accounts separately
for b and ell; root data are encoded by a set of at most r alphabet symbols. -/
theorem subcriticalProfilesOfComplexity_card_le_raw
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (r : ℕ)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta) :
    (subcriticalProfilesOfComplexity D eta R₀ theta r).card ≤
      (Fintype.card V ^ 2 + 1) * (Fintype.card V + 1) *
        (Fintype.card (SubcriticalProfileRootCode D theta) + 1) ^ r := by
  let target := Finset.range (Fintype.card V ^ 2 + 1) ×ˢ
    (Finset.range (Fintype.card V + 1) ×ˢ
      DenseGraph.smallSubsetFinset (Finset.univ : Finset (SubcriticalProfileRootCode D theta)) r)
  have hmap : Set.MapsTo (subcriticalProfileEncoding (D := D) (eta := eta)
      (R₀ := R₀) (theta := theta))
      (↑(subcriticalProfilesOfComplexity D eta R₀ theta r)) (↑target) := by
    intro p hp
    have hr := (mem_subcriticalProfilesOfComplexity D eta R₀ theta r p).mp hp
    have hb : p.b ≤ Fintype.card V ^ 2 :=
      p.b_le.trans ((Nat.choose_le_pow _ 2).trans
        (Nat.pow_le_pow_left (Finset.card_le_univ _) 2))
    have he : p.ell ≤ Fintype.card V := by have := p.two_mul_ell_le; omega
    have hroot : p.roots.card ≤ r := by unfold subcriticalProfileComplexity at hr; omega
    change subcriticalProfileEncoding p ∈ target
    simp only [target, subcriticalProfileEncoding, Finset.mem_product, Finset.mem_range,
      DenseGraph.mem_smallSubsetFinset, Finset.subset_univ, true_and,
      card_subcriticalProfileRootEncoding]
    exact ⟨by omega, by omega, hroot⟩
  have hcount := Finset.card_le_card_of_injOn subcriticalProfileEncoding hmap
    (subcriticalProfileEncoding_injective hret).injOn
  have hsmall := DenseGraph.card_smallSubsetFinset_le_pow
    (Finset.univ : Finset (SubcriticalProfileRootCode D theta)) r
  simp only [target, Finset.card_product, Finset.card_range] at hcount
  simp only [Finset.card_univ] at hsmall
  apply hcount.trans
  rw [mul_assoc]
  exact Nat.mul_le_mul_left (Fintype.card V ^ 2 + 1)
    (Nat.mul_le_mul_left (Fintype.card V + 1) hsmall)

/-- The root alphabet grows polynomially with a degree depending only on
the visible-index bound. The extra unit is for the small-set encoding. -/
theorem card_subcriticalProfileRootCode_add_one_le
    (D : SubcriticalDivision k V) (theta : ℝ) (Qvis : ℕ)
    (hvis : (D.visiblePartIndices theta).card ≤ Qvis) :
    Fintype.card (SubcriticalProfileRootCode D theta) + 1 ≤
      (Fintype.card V + 1) ^ (4 * Qvis + 3) := by
  let n := Fintype.card V
  let q := (D.visiblePartIndices theta).card
  have hn : 1 ≤ n := D.componentCount_pos.trans_le D.componentCount_le_card
  have hb : 1 ≤ n + 1 := by omega
  have hrow : (n + 2) ^ q ≤ (n + 1) ^ (2 * q) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by nlinarith) q
  have htail : 3 ^ q ≤ (n + 1) ^ (2 * q) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by nlinarith) q
  have hcode : Fintype.card (SubcriticalProfileRootCode D theta) ≤
      (n + 1) ^ (4 * q + 2) := by
    rw [card_subcriticalProfileRootCode]
    change n * ((n + 2) ^ q * ((n + 1) * 3 ^ q)) ≤ _
    calc
      _ ≤ (n + 1) ^ 1 * ((n + 1) ^ (2 * q) *
          ((n + 1) ^ 1 * (n + 1) ^ (2 * q))) := by
        simp only [pow_one]
        exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul hrow (Nat.mul_le_mul_left _ htail))
      _ = _ := by simp only [← pow_add]; congr 1 <;> omega
  have hone : 1 ≤ (n + 1) ^ (4 * q + 2) := Nat.one_le_pow _ _ hb
  calc
    _ ≤ 2 * (n + 1) ^ (4 * q + 2) := by omega
    _ ≤ (n + 1) * (n + 1) ^ (4 * q + 2) := Nat.mul_le_mul_right _ (by omega)
    _ = (n + 1) ^ (4 * q + 3) := by
      rw [show 4 * q + 3 = (4 * q + 2) + 1 by omega, pow_succ]
      exact Nat.mul_comm _ _
    _ ≤ (n + 1) ^ (4 * Qvis + 3) := Nat.pow_le_pow_right hb (by dsimp [q]; omega)

/-- Uniform polynomial exponent for stored root/row/tail profile data. -/
def subcriticalProfileEnumerationConstant (Qvis : ℕ) : ℕ := 4 * Qvis + 6

theorem subcriticalProfileEnumerationConstant_pos (Qvis : ℕ) :
    0 < subcriticalProfileEnumerationConstant Qvis := by
  unfold subcriticalProfileEnumerationConstant
  omega

/-- Paper: Lemma `lemma:NtaunmWUpperBdK1k`, uniform profile enumeration.
This bounds all syntactically valid profiles, hence also those with nonempty
graph classes. It holds even for r=0, with the b-coordinate factor retained. -/
theorem subcriticalProfilesOfComplexity_card_le
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (r Qvis : ℕ)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hvis : (D.visiblePartIndices theta).card ≤ Qvis) :
    (subcriticalProfilesOfComplexity D eta R₀ theta r).card ≤
      (Fintype.card V + 1) ^ (subcriticalProfileEnumerationConstant Qvis * (r + 1)) := by
  have hcode := card_subcriticalProfileRootCode_add_one_le D theta Qvis hvis
  have hraw := subcriticalProfilesOfComplexity_card_le_raw D eta R₀ theta r hret
  have hb : Fintype.card V ^ 2 + 1 ≤ (Fintype.card V + 1) ^ 2 := by nlinarith
  have hbase : 1 ≤ Fintype.card V + 1 := by omega
  calc
    _ ≤ (Fintype.card V + 1) ^ 2 * (Fintype.card V + 1) ^ 1 *
        ((Fintype.card V + 1) ^ (4 * Qvis + 3)) ^ r := by
      exact hraw.trans (Nat.mul_le_mul
        (by simpa only [pow_one] using Nat.mul_le_mul_right (Fintype.card V + 1) hb)
        (Nat.pow_le_pow_left hcode r))
    _ = (Fintype.card V + 1) ^ (3 + (4 * Qvis + 3) * r) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hbase (by
      unfold subcriticalProfileEnumerationConstant
      nlinarith)

/-- Uniform enumeration with index bounds derived from genuine finite part
geometry. The constant depends only on theta, never on the division or order. -/
theorem subcriticalProfilesOfComplexity_card_le_uniform
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (r : ℕ)
    (hR : 1 ≤ R₀) (htheta : 0 < theta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ)))
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ)) :
    (subcriticalProfilesOfComplexity D eta R₀ theta r).card ≤
      (Fintype.card V + 1) ^
        (subcriticalProfileEnumerationConstant (subcriticalVisibleIndexBound theta) * (r + 1)) :=
  subcriticalProfilesOfComplexity_card_le D eta R₀ theta r
    (subcriticalVisibleIndexBound theta)
    (D.retainedPartIndices_subset_visiblePartIndices hR htheta.le hcutoff)
    (subcriticalVisiblePartIndices_card_le D htheta hvisible)

end InducedStars
