module

public import GraphMinor.Compute.TwoPathsPath

/-!
# Searching inside a selected bridge

Section 5.2 of `docs/crossing/crossing_extractor.tex` searches inside a component bridge together
with its two
selected endpoints. This file proves the search and parent-tracing step for a supplied set of
free vertices. The caller supplies labels: free vertices have label zero and the target is the
only vertex with label three. All other vertices are blocked.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.HP25 GraphMinor.Compute.TwoPaths

/-- Search from the supplied source array, attach the target to the search tree, and trace the
path to the target in register `rPy`. -/
def bridgePathSearchProg : Cmd :=
  .seq (searchProg aStart aEnd aEnt)
    (.seq (.write aPar (.reg rPy) (.reg rHitPar)) (traceProg aPath rPy))

/-- A search with a single target returns a simple path whose other vertices are free.
The reachability hypothesis is a walk through free vertices to a neighbor of the target. -/
theorem bridgePathSearchProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (L : Fin n → ℕ) (x y : Fin n) (s : State)
    (hL : ∀ v, L v ≤ 3) (hx : L x = 0) (hy : L y = 3)
    (honly : ∀ v, L v = 3 → v = y)
    (hreach : ∃ z : Fin n, G.Adj z y ∧ ∃ W : G.Walk x z, ∀ v ∈ W.support, L v = 0)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hadj : IsAdjList G aStart aEnd aEnt lists s)
    (hent : (s.arrs aEnt).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hry : s.regs rPy = y.1)
    (hlab : s.arrs aLab = List.ofFn L) (hsrc : s.arrs aSrc = [x.1]) :
    ∃ (s' : State) (t : ℕ) (P : G.Walk x y), Exec w bridgePathSearchProg s s' t ∧
      t ≤ 61 + 45 * n + 29 * totalAdjEntries lists ∧
      P.IsPath ∧ (∀ v ∈ P.support, v ≠ y → L v = 0) ∧
      s'.arrs aPath = P.support.map Fin.val ∧
      (∀ r, r < 60 ∨ 77 ≤ r → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ aLab → a ≠ aPar → a ≠ aQue → a ≠ aPath → s'.arrs a = s.arrs a) := by
  obtain ⟨s₁, t₁, items, hex₁, ht₁, hsi⟩ :=
    searchProg_exec G lists aStart aEnd aEnt (by decide) (by decide) (by decide)
      L hL [x.1] (by simp) s hadj hent hrn hw hn (by simpa only [List.length_singleton] using (show 1 < 2 ^ w from lt_trans (by decide) hw)) hlab hsrc
  obtain ⟨z, hzy, W, hW⟩ := hreach
  have hzi : z.1 ∈ items := hsi.mem_of_walk (u := x) (by simp) W hW
  have hhit : s₁.regs rHit ≠ n := fun h => hsi.noHit h hzi hzy hy
  obtain ⟨v, u, _, hpu, hLv, hu, huv⟩ := hsi.hit_of_ne hhit
  have hv : v = y := honly v hLv
  subst hv
  have hyi : v.1 ∉ items := by
    intro h
    have := hsi.free v h
    omega
  obtain ⟨p, hpar, hpok⟩ := hsi.par
  have hxy : x ≠ v := by intro h; rw [h, hy] at hx; omega
  let s₂ := s₁.writeArr aPar v.1 u.1
  have hex₂ : Exec w (.write aPar (.reg rPy) (.reg rHitPar)) s₁ s₂ 3 :=
    .write (reg_eval ((hsi.frame.1 rPy (by decide)).trans hry) (lt_trans v.2 hn))
      (reg_eval hpu (lt_trans u.2 hn)) (by rw [hpar]; simp)
  have hpar₂ : s₂.arrs aPar = List.ofFn (Function.update p v u.1) := by
    simp only [s₂, State.writeArr, State.setArr_arrs, ite_true, hpar]
    exact ofFn_set v _
  obtain ⟨s₃, t₃, r, P, hex₃, ht₃, hP, hr, hPs, _, hout, hregs, harrs⟩ :=
    traceProg_exec (hpok.snoc hyi (by simp [Ne.symm (Fin.val_injective.ne hxy)]) hu huv)
      hn aPath (by decide) rPy (by decide) (by decide) s₂ v (by simp)
      (by change s₁.regs rPy = v.1; exact (hsi.frame.1 rPy (by decide)).trans hry)
      (by change s₁.regs 40 = n; exact (hsi.frame.1 40 (by decide)).trans hrn) hpar₂
  have hrx : r = x := Fin.ext (by simpa using hr)
  subst hrx
  refine ⟨s₃, _, P, .seq hex₁ (.seq hex₂ hex₃), ?_, hP, ?_, hout, ?_, ?_⟩
  · simp only [List.length_singleton] at ht₁
    omega
  · intro z hz hzv
    have hzi' : z.1 ∈ items := by
      rcases List.mem_append.mp (hPs z hz) with h | h
      · exact h
      · exact False.elim (hzv (Fin.ext (by simpa using h)))
    exact hsi.free z hzi'
  · intro r hr
    have h1 : r ≠ TwoPaths.rCur := by dsimp only [TwoPaths.rCur, Reg] at *; omega
    have h2 : r ≠ TwoPaths.rCnt := by dsimp only [TwoPaths.rCnt, Reg] at *; omega
    rw [hregs r h1 h2]
    change s₁.regs r = s.regs r
    exact hsi.frame.1 r (hr.imp id (fun h => le_trans (by decide) h))
  · intro a h1 h2 h3 h4
    rw [harrs a h4]
    change (s₁.writeArr aPar v.1 u.1).arrs a = s.arrs a
    rw [State.writeArr_arrs_ne _ _ _ h2]
    exact hsi.frame.2 a h1 h2 h3

end GraphMinor.Compute
