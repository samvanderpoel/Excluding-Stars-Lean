import InducedStars.Structure.Supercritical.CoverMultiplicity

/-! # Vertex-label invariance of unique ordered clique covers -/

noncomputable section
open Finset Set
namespace InducedStars
variable {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]

theorem SupercriticalDivision.relabel_isFull (D : SupercriticalDivision k V)
    (e : V ≃ W) (hD : D.IsFull) : (D.relabel e).IsFull := by
  rw [SupercriticalDivision.isFull_iff_support_eq_univ]
  ext w
  simp only [D.mem_relabel_support, D.support_eq_univ hD, Finset.mem_univ]

theorem fullDivisionsEquivalent_of_relabel {D E : SupercriticalDivision k V}
    (e : V ≃ W) (h : FullDivisionsEquivalent (D.relabel e) (E.relabel e)) :
    FullDivisionsEquivalent D E := by
  obtain ⟨sigma, hs⟩ := h
  refine ⟨sigma, SupercriticalDivision.ext_parts ?_⟩
  funext i
  ext v
  have hp := congrArg (fun F : SupercriticalDivision k W ↦ e v ∈ F.parts i) hs
  simpa only [SupercriticalDivision.mem_relabel_part, Equiv.symm_apply_apply,
    SupercriticalDivision.reindexParts_parts] using (Iff.of_eq hp)

theorem HasUniqueCoMultipartiteCover.of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : HasUniqueCoMultipartiteCover k G) (e : G ≃g H) :
    HasUniqueCoMultipartiteCover k H := by
  classical
  obtain ⟨D, hD, hcl, huniq⟩ := hG
  have htransport (F : SupercriticalDivision k W)
      (hF : ∀ i, H.IsClique (F.parts i : Set W)) :
      ∀ i, G.IsClique ((F.relabel e.toEquiv.symm).parts i : Set V) := by
    intro i x hx y hy hxy
    have hx' : e x ∈ F.parts i := (F.mem_relabel_part _ _ _).mp hx
    have hy' : e y ∈ F.parts i := (F.mem_relabel_part _ _ _).mp hy
    exact e.map_rel_iff.mp (hF i hx' hy' (fun h ↦ hxy (e.injective h)))
  refine ⟨D.relabel e.toEquiv, D.relabel_isFull _ hD, ?_, ?_⟩
  · intro i x hx y hy hxy
    have hx' := (D.mem_relabel_part e.toEquiv i x).mp hx
    have hy' := (D.mem_relabel_part e.toEquiv i y).mp hy
    have h := hcl i hx' hy' (fun hh ↦ hxy (e.toEquiv.symm.injective hh))
    exact e.symm.map_rel_iff.mp h
  · intro F hF hclF
    have hh := huniq (F.relabel e.toEquiv.symm) (F.relabel_isFull _ hF)
      (htransport F hclF)
    obtain ⟨sigma, hs⟩ := hh
    refine ⟨sigma, SupercriticalDivision.ext_parts ?_⟩
    funext i
    ext w
    have hp := congrArg (fun A : SupercriticalDivision k V ↦ A.parts i) hs
    have hm := Finset.ext_iff.mp hp (e.symm w)
    rw [SupercriticalDivision.reindexParts_parts, SupercriticalDivision.mem_relabel_part]
    simp only [SupercriticalDivision.mem_relabel_part,
      SupercriticalDivision.reindexParts_parts, Equiv.symm_symm,
      Equiv.apply_symm_apply] at hm
    change (w ∈ F.parts i ↔ e.toEquiv.symm w ∈ D.parts (sigma.symm i))
    change (e.toEquiv (e.toEquiv.symm w) ∈ F.parts i ↔
      e.toEquiv.symm w ∈ D.parts (sigma.symm i)) at hm
    simpa only [Equiv.apply_symm_apply] using hm

end InducedStars
