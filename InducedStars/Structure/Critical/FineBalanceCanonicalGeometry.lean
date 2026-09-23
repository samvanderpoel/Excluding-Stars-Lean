import InducedStars.Structure.Critical.CanonicalSparse

/-!
# Cardinal conditions for the canonical fixed-sparse transfer

An equitable displayed cover of the complement of a small sparse set has
large main parts.  This elementary numerical lemma supplies the two strict
inequalities needed to identify that sparse set with the canonical one.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- A fixed radius sufficient for the elementary canonical-sparse argument. -/
def criticalFineBalanceGeometryRadius (k : ℕ) : ℝ :=
  1 / (16 * (k : ℝ) * ((k - 1 : ℕ) : ℝ))

theorem criticalFineBalanceGeometryRadius_pos
    {k : ℕ} (hk : 3 ≤ k) : 0 < criticalFineBalanceGeometryRadius k := by
  unfold criticalFineBalanceGeometryRadius
  have hr : 0 < k - 1 := by omega
  positivity

private theorem balanced_part_large_after_sparse
    {k n s e a : ℕ} (hk : 3 ≤ k) (hn : 16 * k * (k - 1) ≤ n)
    (hs : (s : ℝ) ≤ criticalFineBalanceGeometryRadius k * n)
    (he : (e : ℝ) ≤ criticalFineBalanceGeometryRadius k * n)
    (ha : ((n : ℝ) - s) / ((k - 1 : ℕ) : ℝ) - 1 ≤ a) :
    n < k * (a - (e + 1)) := by
  let r : ℝ := (k - 1 : ℕ)
  let K : ℝ := k
  let N : ℝ := n
  have hK : (3 : ℝ) ≤ K := by dsimp [K]; exact_mod_cast hk
  have hr : 0 < r := by dsimp [r]; exact_mod_cast (by omega : 0 < k - 1)
  have hKr : K = r + 1 := by
    dsimp [K, r]
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hN : 16 * K * r ≤ N := by dsimp [K, r, N]; exact_mod_cast hn
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hden : 0 < 16 * K * r := by positivity
  have hs' : (s : ℝ) ≤ N / (16 * K * r) := by
    simpa [criticalFineBalanceGeometryRadius, K, r, N, one_div,
      div_eq_mul_inv, mul_comm] using hs
  have he' : (e : ℝ) ≤ N / (16 * K * r) := by
    simpa [criticalFineBalanceGeometryRadius, K, r, N, one_div,
      div_eq_mul_inv, mul_comm] using he
  have hsdiv : (s : ℝ) / r ≤ (s : ℝ) := by
    apply (div_le_iff₀ hr).2
    have hr1 : 1 ≤ r := by linarith
    simpa using mul_le_mul_of_nonneg_left hr1 (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have ha' : N / r - (s : ℝ) / r - 1 ≤ (a : ℝ) := by
    simpa [N, r, sub_div] using ha
  have hdiff : N / r - 2 * (N / (16 * K * r)) - 2 ≤
      (a : ℝ) - ((e : ℝ) + 1) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff (by linarith : 0 ≤ K)
  have hcalc : K * (N / r - 2 * (N / (16 * K * r)) - 2) =
      N + 7 * N / (8 * r) - 2 * K := by
    have hK0 : K ≠ 0 := by linarith
    field_simp
    nlinarith [hKr]
  rw [hcalc] at hmul
  have hlarge : 2 * K < 7 * N / (8 * r) := by
    apply (lt_div_iff₀ (by positivity : 0 < 8 * r)).2
    nlinarith
  have hsub : (a : ℝ) - ((e : ℝ) + 1) ≤ (a - (e + 1) : ℕ) := by
    have hnat : a ≤ a - (e + 1) + (e + 1) := by omega
    have hreal : (a : ℝ) ≤ (a - (e + 1) : ℕ) + ((e : ℝ) + 1) := by
      exact_mod_cast hnat
    linarith
  have hmulsub := mul_le_mul_of_nonneg_left hsub (by linarith : 0 ≤ K)
  have hfinal : N < K * (a - (e + 1) : ℕ) := by linarith
  dsimp [N, K] at hfinal
  exact_mod_cast hfinal

/-- Explicit numerical conditions sufficient for the two canonical sparse
inclusions.  The lower bound for a displayed part follows from exact balance
on its `n - s` support vertices. -/
theorem criticalFineBalance_canonical_card_conditions
    {k n : ℕ} (hk : 3 ≤ k) (hn : 16 * k * (k - 1) ≤ n)
    (D E : SupercriticalDivision k (Fin n))
    (hs : (D.sparse.card : ℝ) ≤ criticalFineBalanceGeometryRadius k * n)
    (he : (E.sparse.card : ℝ) ≤ criticalFineBalanceGeometryRadius k * n)
    (hEparts : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤ (E.parts i).card)
    (hDparts : ∀ i : Fin (k - 1),
      ((n : ℝ) - D.sparse.card) / ((k - 1 : ℕ) : ℝ) - 1 ≤
        (D.parts i).card) :
    (∀ i : Fin (k - 1), 2 * D.sparse.card < (E.parts i).card) ∧
      (∀ i : Fin (k - 1), n < k * ((D.parts i).card - (E.sparse.card + 1))) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hnR : (0 : ℝ) < n := by
    have hkNat : 0 < k := by omega
    have hrNat : 0 < k - 1 := by omega
    have : 0 < n := lt_of_lt_of_le (by positivity) hn
    exact_mod_cast this
  constructor
  · intro i
    have hs' : (D.sparse.card : ℝ) ≤
        (n : ℝ) / (16 * (k : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
      simpa [criticalFineBalanceGeometryRadius, one_div, div_eq_mul_inv, mul_comm] using hs
    have hden : 0 < 16 * (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by positivity
    have htwice : 2 * ((n : ℝ) / (16 * (k : ℝ) * ((k - 1 : ℕ) : ℝ))) <
        (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) := by
      rw [← mul_div_assoc]
      apply (div_lt_div_iff₀ hden (by positivity)).2
      nlinarith [mul_pos hnR hr]
    have hi := hEparts i
    have hlt : 2 * (D.sparse.card : ℝ) < (E.parts i).card := by linarith
    exact_mod_cast hlt
  · intro i
    exact balanced_part_large_after_sparse hk hn hs he (hDparts i)

/-- Coarse canonical size control at one fixed cut radius.  The radius is
chosen independently of the subsequently fixed sparse set and of its graph.
In particular this does not assume fine balance in order to prove it. -/
theorem exists_criticalFineBalanceCanonicalGeometry
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) (hn : k - 1 ≤ n),
        cutDist (graphGraphon G)
          (Wstar k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)) < τ →
        (((canonicalSupercriticalDivision G (by simpa using hn)).sparse.card : ℝ) ≤
            criticalFineBalanceGeometryRadius k * n) ∧
          ∀ i : Fin (k - 1),
            (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
              ((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  let α : ℝ := 1 / (200 * (k : ℝ))
  have hα : 0 < α := by dsimp [α]; positivity
  have hαupper : α < 1 / (100 * (k : ℝ)) := by
    dsimp [α]
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  let ρ := supercriticalOffDiagonal k (gammaK k)
  have hρ : 0 < ρ := supercriticalOffDiagonal_pos hk
    le_rfl
  have hρone : ρ < 1 := supercriticalOffDiagonal_lt_one hk
    (gammaK_lt_one hk)
  let δ : ℝ := min (criticalFineBalanceGeometryRadius k)
    (min (α / 200) (min (ρ / 6) (min ((1 - ρ) / 6)
      (1 / (2 * ((k - 1 : ℕ) : ℝ))))))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (criticalFineBalanceGeometryRadius_pos hk)
      (lt_min (by positivity) (lt_min (by positivity)
        (lt_min (by positivity) (by positivity))))
  have hδgeom : δ ≤ criticalFineBalanceGeometryRadius k := min_le_left _ _
  have hδother := min_le_right (criticalFineBalanceGeometryRadius k)
    (min (α / 200) (min (ρ / 6) (min ((1 - ρ) / 6)
      (1 / (2 * ((k - 1 : ℕ) : ℝ))))))
  change δ ≤ _ at hδother
  have hδα : δ < α / 100 := lt_of_le_of_lt
    (hδother.trans (min_le_left _ _)) (by linarith)
  have hδρ := hδother.trans (min_le_right _ _)
  have hρlower : 3 * δ < ρ := by
    have := hδρ.trans (min_le_left _ _)
    linarith
  have hδlast := hδρ.trans (min_le_right _ _)
  have hρupper : ρ + 3 * δ < 1 := by
    have := hδlast.trans (min_le_left _ _)
    linarith
  have hδpart : δ ≤ 1 / (2 * ((k - 1 : ℕ) : ℝ)) :=
    hδlast.trans (min_le_right _ _)
  let hγ := gammaK_mem_supercritical_Ico k hk
  let hαI : α ∈ Ioo (0 : ℝ) (1 / (100 * k : ℝ)) := ⟨hα, hαupper⟩
  let τ := supercriticalCloseStructureCutRadius k hk (gammaK k) hγ
    α hαI δ hδ hδα hρlower hρupper 1 zero_lt_one
  refine ⟨τ, supercriticalCloseStructureCutRadius_pos k hk (gammaK k) hγ
    α hαI δ hδ hδα hρlower hρupper 1 zero_lt_one, ?_⟩
  filter_upwards [eventually_ge_atTop
    (supercriticalCloseStructureVertexThreshold k hk (gammaK k) hγ
      α hαI δ hδ hδα hρlower hρupper 1 zero_lt_one)] with n hn0
  intro G hn hclose
  obtain ⟨A⟩ := supercriticalCloseStructure k hk (gammaK k) hγ
    α hαI δ hδ hδα hρlower hρupper 1 zero_lt_one hn0 G hclose
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · have hsmall := A.sparse_card_le
    have hδn := mul_le_mul_of_nonneg_right hδgeom hnR
    have : (0 : ℝ) ≤ δ * n := mul_nonneg hδ.le hnR
    linarith
  · intro i
    have hpart := (abs_le.mp (A.part_card_close i)).1
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 :=
      by simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ k))
    rw [← hcast] at hpart
    have hδn := mul_le_mul_of_nonneg_right hδpart hnR
    have hsplit : (n : ℝ) / ((k - 1 : ℕ) : ℝ) =
        2 * ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) := by ring
    have heq : 1 / (2 * ((k - 1 : ℕ) : ℝ)) * (n : ℝ) =
        (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) := by ring
    rw [heq] at hδn
    linarith

/-- An equitable displayed clean cover of a small fixed sparse set uses the
same sparse set as the canonical division, provided the graph is close to
the critical optimizer.  The part-size lower bound is deliberately only a
floor bound, so every exactly balanced displayed support cover qualifies. -/
theorem eventually_canonical_sparse_eq_of_close_balanced_displayed
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) (hn : k - 1 ≤ n)
        (D : SupercriticalDivision k (Fin n)),
        cutDist (graphGraphon G)
          (Wstar k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)) < τ →
        supercriticalDefectGraph G D = ⊥ →
        (D.sparse.card : ℝ) ≤ criticalFineBalanceGeometryRadius k * n →
        (∀ i : Fin (k - 1),
          (n - D.sparse.card) / (k - 1) ≤ (D.parts i).card) →
        (canonicalSupercriticalDivision G (by simpa using hn)).sparse = D.sparse := by
  obtain ⟨τ, hτ, hgeom⟩ := exists_criticalFineBalanceCanonicalGeometry k hk
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hgeom, eventually_ge_atTop (16 * k * (k - 1))] with
      n hnGeom hnLarge
  intro G hn D hclose hclean hs hparts
  obtain ⟨he, hEparts⟩ := hnGeom G hn hclose
  have hsNat : D.sparse.card ≤ n := by
    simpa using Finset.card_le_univ D.sparse
  have hDparts : ∀ i : Fin (k - 1),
      ((n : ℝ) - D.sparse.card) / ((k - 1 : ℕ) : ℝ) - 1 ≤
        (D.parts i).card := by
    intro i
    have hrNat : 0 < k - 1 := by omega
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hrNat
    have hdiv : n - D.sparse.card <
        ((n - D.sparse.card) / (k - 1) + 1) * (k - 1) :=
      (Nat.div_lt_iff_lt_mul hrNat).mp (Nat.lt_succ_self _)
    have hdivR : ((n - D.sparse.card : ℕ) : ℝ) <
        (((n - D.sparse.card) / (k - 1) : ℕ) + (1 : ℝ)) *
          ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hdiv
    rw [Nat.cast_sub hsNat] at hdivR
    have hratio := (div_lt_iff₀ hr).2 hdivR
    have hi : (((n - D.sparse.card) / (k - 1) : ℕ) : ℝ) ≤
        (D.parts i).card := by exact_mod_cast hparts i
    linarith
  obtain ⟨hleft, hright⟩ := criticalFineBalance_canonical_card_conditions
    hk hnLarge D (canonicalSupercriticalDivision G (by simpa using hn))
    hs he hEparts hDparts
  exact canonicalSupercriticalDivision_sparse_eq_of_clean
    G D hk (by simpa using hn) hclean hleft
      (by simpa only [Fintype.card_fin] using hright)

end InducedStars
