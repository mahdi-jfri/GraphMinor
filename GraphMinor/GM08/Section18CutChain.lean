module

public import GraphMinor.GM08.Section14

/-!
# Undoing extra lifts by vertex identifications

When we cut a surface along a schism, a vertex on the schism has several
lifts. In the cut graft, one lift keeps the old label and the others get new
labels. The map `π` sends each new label to the old one. Here we show that
the old graft comes back from the cut graft by one vertex identification per
new label. This is the last step of the cut case on page 287 of VIII.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Graph

universe u v

/-- Let `π` fix every vertex of `Y` outside a finite set `R` of roots, and send
each member of `R` to a root outside `R`. If `X` is the image of `Y` under `π`,
with the roots of `Y` outside `R ∪ π(R)`, then `X` comes from `Y` by `|R|`
vertex identifications. We identify one member `r` of `R` with `π r` at a time;
`π r` stays a root while another member of `R` still maps to it. -/
theorem obtainedByVertexIdChain_of_retraction {α : Type u} {β : Type v} (n : ℕ) :
    ∀ (Y X : Graft α β) (π : α → α) (R : Set α), R.Finite → R.ncard = n →
      X.G = Y.G.map π → (∀ x ∈ V(Y.G), x ∉ R → π x = x) → R ⊆ Y.T →
      (∀ r ∈ R, π r ∈ Y.T ∧ π r ∉ R) → X.T = Y.T \ (R ∪ π '' R) →
      ObtainedByVertexIdChain n Y X := by
  classical
  induction n with
  | zero =>
    intro Y X π R hR hn hG hfix _ _ hT
    have hR0 : R = ∅ := (ncard_eq_zero hR).mp hn
    subst hR0
    have hGY : X.G = Y.G := by
      rw [hG]
      exact (map_eq_of_eqOn (g := id) fun x hx => hfix x hx (notMem_empty x)).trans map_id
    have hTY : X.T = Y.T := by simp [hT]
    rw [Graft.ext hGY hTY]
    exact ObtainedByVertexIdChain.zero _
  | succ n ih =>
    intro Y X π R hR hn hG hfix hRT hπR hT
    obtain ⟨r, hr⟩ : R.Nonempty := nonempty_of_ncard_ne_zero (by omega)
    set p := π r with hp
    have hpT : p ∈ Y.T := (hπR r hr).1
    have hpR : p ∉ R := (hπR r hr).2
    have hrT : r ∈ Y.T := hRT hr
    have hrp : r ≠ p := fun h => hpR (h ▸ hr)
    have hpV : p ∈ V(Y.G) := Y.T_subset hpT
    have hπp : π p = p := hfix p hpV hpR
    let f := identifyVerticesFun r p p
    have hfr : f r = p := by simp [f]
    have hfp : f p = p := by simp [f]
    let T₁ : Set α := (Y.T \ {r, p}) ∪ {q | q = p ∧ ∃ r' ∈ R, r' ≠ r ∧ π r' = p}
    have hT₁V : T₁ ⊆ V(Y.G.map f) := by
      intro q hq
      rcases hq with ⟨hq, hqrp⟩ | ⟨hqp, -⟩
      · refine ⟨q, Y.T_subset hq, ?_⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hqrp
        exact identifyVerticesFun_of_ne hqrp.1 hqrp.2
      · exact ⟨p, hpV, hfp.trans hqp.symm⟩
    let Y₁ : Graft α β :=
      { G := Y.G.map f
        T := T₁
        T_subset := hT₁V
        finite_G := ⟨Y.finite_G.1.image f, Y.finite_G.2⟩ }
    have hstep : ObtainedByVertexIdChain 1 Y Y₁ := by
      refine ObtainedByVertexIdChain.step (ObtainedByVertexIdChain.zero Y) r p hrT hpT hrp rfl ?_
      by_cases hex : ∃ r' ∈ R, r' ≠ r ∧ π r' = p
      · right
        ext q
        simp only [Y₁, T₁, mem_union, mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => h.imp id fun h => h.1, fun h => h.imp id fun h => ⟨h, hex⟩⟩
      · left
        ext q
        simp only [Y₁, T₁, mem_union, mem_ofPred_eq]
        exact ⟨fun h => h.elim id fun h => (hex h.2).elim, Or.inl⟩
    have hfin : (R \ {r}).Finite := hR.sdiff
    have hcard : (R \ {r}).ncard = n := by
      rw [ncard_sdiff_singleton_of_mem hr]
      omega
    have hrest : ObtainedByVertexIdChain n Y₁ X := by
      refine ih Y₁ X π (R \ {r}) hfin hcard ?_ ?_ ?_ ?_ ?_
      · change X.G = (Y.G.map f).map π
        rw [map_map, hG]
        refine map_eq_of_eqOn fun x hx => ?_
        by_cases hx' : x = r ∨ x = p
        · rcases hx' with rfl | rfl
          · exact ((congrArg π hfr).trans (hπp.trans hp)).symm
          · exact (congrArg π hfp).symm
        · rw [not_or] at hx'
          simp [f, identifyVerticesFun_of_ne hx'.1 hx'.2]
      · rintro x ⟨w, hw, rfl⟩ hxR
        by_cases hw' : w = r ∨ w = p
        · rcases hw' with rfl | rfl
          · rw [hfr]; exact hπp
          · rw [hfp]; exact hπp
        · rw [not_or] at hw'
          rw [show f w = w from identifyVerticesFun_of_ne hw'.1 hw'.2] at hxR ⊢
          exact hfix w hw fun hwR => hxR ⟨hwR, hw'.1⟩
      · rintro r' ⟨hr', hr'r⟩
        refine Or.inl ⟨hRT hr', ?_⟩
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨hr'r, fun h => hpR (h ▸ hr')⟩
      · rintro r' ⟨hr', hr'r⟩
        refine ⟨?_, fun h => (hπR r' hr').2 h.1⟩
        by_cases hq : π r' = p
        · exact Or.inr ⟨hq, r', hr', hr'r, hq⟩
        · refine Or.inl ⟨(hπR r' hr').1, ?_⟩
          simp only [mem_insert_iff, mem_singleton_iff, not_or]
          exact ⟨fun h => (hπR r' hr').2 (h ▸ hr), hq⟩
      · rw [hT]
        ext q
        simp only [Y₁, T₁, mem_sdiff, mem_union, mem_image, mem_ofPred_eq, mem_insert_iff,
          mem_singleton_iff, not_or, not_exists, not_and]
        constructor
        · rintro ⟨hq, hqR, hqπ⟩
          have hqr : q ≠ r := fun h => hqR (h ▸ hr)
          have hqp : q ≠ p := fun h => hqπ r hr h.symm
          exact ⟨Or.inl ⟨hq, hqr, hqp⟩, fun h _ => hqR h, fun x hx => hqπ x hx.1⟩
        · rintro ⟨hq | ⟨rfl, r', hr', hr'r, hr'p⟩, hqR, hqπ⟩
          · refine ⟨hq.1, fun h => hqR h hq.2.1, fun x hx hxq => ?_⟩
            by_cases hxr : x = r
            · subst hxr; exact hq.2.2 hxq.symm
            · exact hqπ x ⟨hx, hxr⟩ hxq
          · exact (hqπ r' ⟨hr', hr'r⟩ hr'p).elim
    have h := hstep.trans hrest
    rwa [Nat.add_comm] at h

end GraphMinor.GM08
