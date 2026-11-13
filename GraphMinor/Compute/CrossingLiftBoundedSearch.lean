module

public import GraphMinor.Compute.CrossingLiftShrinkGraph
public import GraphMinor.Compute.CrossingLiftSearchBuild

/-!
# Running the search with the inferred vertex count

The ambient finite type need not have its size in a register. The stored count may be any
smaller bound covering all recorded endpoints and component vertices. Interpreting the same
words on that smaller type permits the existing search, and inclusion returns a path in
the original graph with exactly the words written by the program.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph

/-- The graph-building search needs only a stored bound covering the recorded labels.
Its hypotheses are the recorded graph and component, endpoint labels below that bound,
ordinary allowed-path reachability, memory layout and word bounds. -/
theorem liftBuildSearchProg_exec_bounded {w N M : ℕ} (G : SimpleGraph (Fin N))
    (hMN : M ≤ N) (E : List (Fin N × Fin N)) (C : List (Fin N)) (u v : Fin N)
    (hEM : ∀ p ∈ E, p.1.val < M ∧ p.2.val < M) (hCM : ∀ x ∈ C, x.val < M)
    (huM : u.val < M) (hvM : v.val < M)
    (edges component R A : ℕ) (heA : edges < A) (hcA : component < A) (s : State)
    (hE : E.Nodup) (hgraph : ∀ a b, (a, b) ∈ E ↔ G.Adj a b)
    (he : s.arrs edges = E.flatMap encPair) (hc : s.arrs component = C.map Fin.val)
    (hn : s.regs (R + 40) = M) (hu : s.regs (R + 74) = u.val)
    (hv : s.regs (R + 75) = v.val)
    (hreach : ∃ W : G.Walk u v, ∀ x ∈ W.support, x ≠ u → x ≠ v → x ∈ C)
    (hw : 32 * (N + C.length + E.length + 1) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (W : G.Walk u v), Exec w (liftBuildSearchProg edges component R A) s s' t ∧
      t ≤ 400 * (N + C.length + E.length + 1) ∧ W.IsPath ∧
      (∀ x ∈ W.support, x ≠ u → x ≠ v → x ∈ C) ∧
      s'.arrs (A + 66) = W.support.map Fin.val ∧
      (∀ a < A, s'.arrs a = s.arrs a) ∧ (∀ q < R, s'.regs q = s.regs q) := by
  let inc := Fin.castLE hMN
  let H := G.comap inc
  let E' := liftShrinkEdges E hEM
  let C' := liftShrinkList C hCM
  let u' : Fin M := ⟨u.val, huM⟩
  let v' : Fin M := ⟨v.val, hvM⟩
  have hu' : inc u' = u := Fin.ext rfl
  have hv' : inc v' = v := Fin.ext rfl
  have hinj : Function.Injective inc := by
    intro a b heq
    exact Fin.ext (congrArg (fun x : Fin N => x.val) heq)
  have hreach' : ∃ W : H.Walk u' v', ∀ x ∈ W.support, x ≠ u' → x ≠ v' → x ∈ C' := by
    obtain ⟨W, hW⟩ := hreach
    have hbound : ∀ x ∈ W.support, x.val < M := by
      intro x hx
      by_cases hxu : x = u
      · exact hxu ▸ huM
      by_cases hxv : x = v
      · exact hxv ▸ hvM
      exact hCM x (hW x hx hxu hxv)
    obtain ⟨W', hW'⟩ := liftBoundedWalk G hMN W u' v' hu' hv' hbound
    refine ⟨W', ?_⟩
    intro x hx hxu hxv
    apply (liftShrinkList_mem C hCM hMN x).mpr
    have hxW : inc x ∈ W.support := by rw [← hW']; exact List.mem_map_of_mem hx
    exact hW _ hxW
      (fun heq => hxu (hinj (heq.trans hu'.symm)))
      (fun heq => hxv (hinj (heq.trans hv'.symm)))
  have hE' : E'.Nodup := liftShrinkEdges_nodup E hEM hMN hE
  have hgraph' : ∀ a b, (a, b) ∈ E' ↔ H.Adj a b := liftShrinkEdges_adj G E hEM hMN hgraph
  have hel : E'.length = E.length := liftShrinkEdges_length E hEM
  have hcl : C'.length = C.length := liftShrinkList_length C hCM
  have he' : s.arrs edges = E'.flatMap encPair := he.trans (liftShrinkEdges_values E hEM).symm
  have hc' : s.arrs component = C'.map Fin.val := hc.trans (liftShrinkList_values C hCM).symm
  obtain ⟨s', t, W', hex, ht, hp, hallowed, ho, ha, hr⟩ := liftBuildSearchProg_exec (w := w)
    H E' C' u' v' edges component R A heA hcA s hE' hgraph' he' hc' hn hu hv hreach'
    (by rw [hel, hcl]; omega)
  let W : G.Walk u v := (W'.map (Hom.comap inc G)).copy hu' hv'
  have hsupport : W.support = W'.support.map inc := by
    exact (Walk.support_copy (W'.map (Hom.comap inc G)) hu' hv').trans
      (Walk.support_map _ _)
  have hpW : W.IsPath := by
    rw [Walk.isPath_def, hsupport]
    exact hp.support_nodup.map hinj
  refine ⟨s', t, W, hex, ?_, hpW, ?_, ?_, ha, hr⟩
  · rw [hel, hcl] at ht; omega
  · intro x hx hxu hxv
    rw [hsupport, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (liftShrinkList_mem C hCM hMN y).mp
      (hallowed y hy (fun heq => hxu (congrArg inc heq |>.trans hu'))
        (fun heq => hxv (congrArg inc heq |>.trans hv')))
  · rw [hsupport, List.map_map]
    exact ho

end GraphMinor.Compute.Crossing
