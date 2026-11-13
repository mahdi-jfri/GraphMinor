module

public import GraphMinor.Compute.CrossingClassPathLabels

/-!
# A path with prescribed allowed inner vertices

This file assembles label initialization, the single-source search, and parent tracing for the
two path searches at the end of Section 5.2 of `docs/crossing/crossing_extractor.tex`. The returned
path has all its inner vertices in the supplied list. A component bridge supplies its component
list, and a chord supplies the empty list.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.Compute.TwoPaths

/-- Initialize the allowed set, free the start, mark the target, and search for a path. -/
def bridgeAllowedPathProg : Cmd :=
  .seq bridgeLabelProg
    (.seq (.write aLab (.reg rPx) (.const 0))
      (.seq (.write aLab (.reg rPy) (.const 3))
        (.seq (.alloc aSrc (.const 1))
          (.seq (.write aSrc (.const 0) (.reg rPx)) bridgePathSearchProg))))

/-- Search within the supplied allowed vertices and endpoints.
Reachability is stated as a walk to a neighbor of the target, avoiding the target. -/
theorem bridgeAllowedPathProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (A : List (Fin n)) (x y : Fin n) (s : State)
    (hxy : x ≠ y)
    (hreach : ∃ z : Fin n, G.Adj z y ∧ ∃ W : G.Walk x z,
      ∀ v ∈ W.support, v ≠ y ∧ (v = x ∨ v ∈ A))
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hlen : A.length < 2 ^ w)
    (hadj : IsAdjList G aStart aEnd aEnt lists s)
    (hent : (s.arrs aEnt).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hrx : s.regs rPx = x.1) (hry : s.regs rPy = y.1)
    (hA : s.arrs aBridgeAllowed = A.map Fin.val) :
    ∃ (s' : State) (t : ℕ) (P : G.Walk x y), Exec w bridgeAllowedPathProg s s' t ∧
      t ≤ 100 + 58 * n + 12 * A.length + 29 * totalAdjEntries lists ∧
      P.IsPath ∧ (∀ v ∈ P.support, v ≠ x → v ≠ y → v ∈ A) ∧
      s'.arrs aPath = P.support.map Fin.val ∧
      (∀ r, r ≠ rBridgeLabel → r < 60 ∨ 77 ≤ r → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ aLab → a ≠ aPar → a ≠ aQue → a ≠ aPath → a ≠ aSrc →
        s'.arrs a = s.arrs a) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hlab₁, hr₁, ha₁⟩ :=
    bridgeLabelProg_exec A s hrn hA (by omega) hn hlen
  have hrx₁ : s₁.regs rPx = x.1 := (hr₁ _ (by decide)).trans hrx
  have hry₁ : s₁.regs rPy = y.1 := (hr₁ _ (by decide)).trans hry
  have hrn₁ : s₁.regs 40 = n := (hr₁ _ (by decide)).trans hrn
  let s₂ := s₁.writeArr aLab x.1 0
  have hex₂ : Exec w (.write aLab (.reg rPx) (.const 0)) s₁ s₂ 3 :=
    .write (reg_eval hrx₁ (lt_trans x.2 hn)) (by simp [checkWord])
      (by rw [hlab₁]; simp)
  let s₃ := s₂.writeArr aLab y.1 3
  have hex₃ : Exec w (.write aLab (.reg rPy) (.const 3)) s₂ s₃ 3 :=
    .write (reg_eval hry₁ (lt_trans y.2 hn)) (by simp [checkWord]; omega)
      (by simp [s₂, hlab₁])
  let L := Function.update (Function.update (bridgeLabels A) x 0) y 3
  have hlab₃ : s₃.arrs aLab = List.ofFn L := by
    simp only [s₃, s₂, State.writeArr_arrs_self, hlab₁]
    rw [ofFn_set x, ofFn_set y]
  let s₄ := s₃.setArr aSrc (List.replicate 1 0)
  have hex₄ : Exec w (.alloc aSrc (.const 1)) s₃ s₄ 2 :=
    .alloc (m := 1) (by simp [checkWord, show 1 < 2 ^ w from lt_trans (by decide) hw])
  let s₅ := s₄.writeArr aSrc 0 x.1
  have hex₅ : Exec w (.write aSrc (.const 0) (.reg rPx)) s₄ s₅ 3 :=
    .write (by simp [checkWord]) (reg_eval hrx₁ (lt_trans x.2 hn)) (by simp [s₄])
  have hregs₅ : ∀ r, s₅.regs r = s₁.regs r := fun _ => rfl
  have harrs₅ : ∀ a, a ≠ aLab → a ≠ aSrc → s₅.arrs a = s₁.arrs a := by
    intro a h1 h2
    simp [s₅, s₄, s₃, s₂, State.writeArr, h1, h2]
  have hadj₅ : IsAdjList G aStart aEnd aEnt lists s₅ :=
    hadj.of_arrs_eq
      ((harrs₅ _ (by decide) (by decide)).trans (ha₁ _ (by decide)))
      ((harrs₅ _ (by decide) (by decide)).trans (ha₁ _ (by decide)))
      ((harrs₅ _ (by decide) (by decide)).trans (ha₁ _ (by decide)))
  have hL : ∀ v, L v ≤ 3 := by
    intro v
    simp only [L, Function.update_apply, bridgeLabels]
    split_ifs <;> omega
  have hxL : L x = 0 := by simp [L, hxy]
  have hyL : L y = 3 := by simp [L]
  have htarget : ∀ v, L v = 3 → v = y := by
    intro v h
    by_contra hne
    simp only [L, Function.update_of_ne hne, Function.update_apply, bridgeLabels] at h
    split_ifs at h; contradiction
  have hreachL : ∃ z : Fin n, G.Adj z y ∧ ∃ W : G.Walk x z,
      ∀ v ∈ W.support, L v = 0 := by
    obtain ⟨z, hzy, W, hW⟩ := hreach
    refine ⟨z, hzy, W, fun v hv => ?_⟩
    obtain ⟨hvy, hvx | hvA⟩ := hW v hv
    · subst hvx; exact hxL
    · simp [L, Function.update_apply, hvy, bridgeLabels, hvA]
  obtain ⟨s₆, t₆, P, hex₆, ht₆, hP, hfree, hout, hr₆, ha₆⟩ :=
    bridgePathSearchProg_exec G lists L x y s₅ hL hxL hyL htarget hreachL hw hn hadj₅
      (by rw [harrs₅ _ (by decide) (by decide), ha₁ _ (by decide)]; exact hent)
      hrn₁ hry₁ (by simpa [s₅, s₄, State.writeArr] using hlab₃)
      (by simp [s₅, s₄, State.writeArr])
  refine ⟨s₆, _, P, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hP, ?_, hout, ?_, ?_⟩
  · intro v hv hvx hvy
    have h := hfree v hv hvy
    simpa [L, Function.update_of_ne hvy, Function.update_of_ne hvx, bridgeLabels] using h
  · intro r hne hr
    rw [hr₆ r hr, hregs₅ r, hr₁ r hne]
  · intro a h1 h2 h3 h4 h5
    rw [ha₆ a h1 h2 h3 h4, harrs₅ a h1 h5, ha₁ a h1]

end GraphMinor.Compute
