module

public import GraphMinor.Compute.TwoPathsUndoProg
public import GraphMinor.Compute.TwoPathsExtSplice

/-!
# The undo program on a chain of collapse steps

`t2UndoProg_exec` (`TwoPathsUndoProg.lean`) works on lists of numbers. A `T2Chain` on `Fin N` has
steps with vertices in `Fin N`, and the program sees their numbers (`stepsVal`). This file shows
that the splice commutes with an injective map of the vertices (`spliceT2All_map`,
`SpliceAllOK.map`). Then `undoT2Chain_splice` gives the run on a chain:

* `t2UndoProg_chain`: for a valid crossing `cr` of the collapsed graph, `t2UndoProg` writes the
  vertex lists of the crossing `undoT2Chain chain cr` of the input graph, in time linear in `N`,
  the length of the records and the lengths of the two paths.
-/

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

@[expose] public section

section Map

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}

theorem listHasEdge_map (hf : Function.Injective f) (y z : α) (l : List α) :
    listHasEdge (f y) (f z) (l.map f) = listHasEdge y z l := by
  unfold listHasEdge
  rw [← List.map_tail, List.zip_map, List.any_map]
  congr 1
  funext p
  simp [hf.eq_iff]

theorem t2Uses_map (hf : Function.Injective f) (y z : α) (N l : List α) :
    t2Uses (f y) (f z) (N.map f) (l.map f) = t2Uses y z N l := by
  simp only [t2Uses, List.isEmpty_map, listHasEdge_map hf]

theorem idxOf_map (hf : Function.Injective f) (a : α) : ∀ l : List α,
    (l.map f).idxOf (f a) = l.idxOf a
  | [] => rfl
  | b :: l => by
    by_cases h : b = a
    · subst h; simp
    · rw [List.map_cons, List.idxOf_cons_ne _ (fun e => h (hf e)), List.idxOf_cons_ne _ h,
        idxOf_map hf a l]

theorem rule2PocketChain_map (hf : Function.Injective f) (y z : α) (N l : List α) :
    rule2PocketChain (f y) (f z) (N.map f) (l.map f) = (rule2PocketChain y z N l).map f := by
  unfold rule2PocketChain
  rw [idxOf_map hf, idxOf_map hf]
  split_ifs <;> simp [List.map_take, List.map_drop, List.map_reverse]

theorem spliceT2Lists_map (hf : Function.Injective f) (y z : α) (N Q R : List α) :
    spliceT2Lists (f y) (f z) (N.map f) (Q.map f) (R.map f) =
      ((spliceT2Lists y z N Q R).1.map f, (spliceT2Lists y z N Q R).2.map f) := by
  unfold spliceT2Lists
  rw [t2Uses_map hf, t2Uses_map hf]
  split_ifs <;> simp [rule2PocketChain_map hf]

/-- A step with its vertices mapped by `f`. -/
def mapStep (f : α → β) (r : α × α × List α) : β × β × List β := (f r.1, f r.2.1, r.2.2.map f)

theorem spliceT2All_map (hf : Function.Injective f) : ∀ (l : List (α × α × List α)) (Q R : List α),
    spliceT2All (l.map (mapStep f)) (Q.map f, R.map f) =
      ((spliceT2All l (Q, R)).1.map f, (spliceT2All l (Q, R)).2.map f)
  | [], _, _ => rfl
  | (y, z, N) :: l, Q, R => by
    simp only [List.map_cons, mapStep, spliceT2All]
    rw [spliceT2Lists_map hf]
    exact spliceT2All_map hf l _ _

theorem SpliceOK.map (hf : Function.Injective f) {y z : α} {N Q R : List α}
    (h : SpliceOK y z N Q R) : SpliceOK (f y) (f z) (N.map f) (Q.map f) (R.map f) := by
  obtain ⟨hQ, hR, hQR, hN⟩ := h
  refine ⟨hQ.map hf, hR.map hf, ?_, ?_⟩
  · intro x hx hx'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hx'
    exact hQR hu (hf he ▸ hv)
  · intro huse
    rw [t2Uses_map hf, t2Uses_map hf] at huse
    obtain ⟨hNnd, hy, hz, hx⟩ := hN huse
    refine ⟨hNnd.map hf, ?_, ?_, ?_⟩
    · rw [List.mem_map]; rintro ⟨u, hu, he⟩; exact hy (hf he ▸ hu)
    · rw [List.mem_map]; rintro ⟨u, hu, he⟩; exact hz (hf he ▸ hu)
    · intro x hxN
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hxN
      refine ⟨?_, ?_⟩
      · rw [List.mem_map]; rintro ⟨v, hv, he⟩; exact (hx u hu).1 (hf he ▸ hv)
      · rw [List.mem_map]; rintro ⟨v, hv, he⟩; exact (hx u hu).2 (hf he ▸ hv)

theorem SpliceAllOK.map (hf : Function.Injective f) : ∀ {l : List (α × α × List α)} {Q R : List α},
    SpliceAllOK l (Q, R) → SpliceAllOK (l.map (mapStep f)) (Q.map f, R.map f)
  | [], Q, R, h => by
    obtain ⟨hQ, hR, hQR⟩ := h
    refine ⟨hQ.map hf, hR.map hf, ?_⟩
    intro x hx hx'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hx'
    exact hQR hu (hf he ▸ hv)
  | (y, z, N) :: l, Q, R, h => by
    refine ⟨SpliceOK.map hf h.1, ?_⟩
    have := SpliceAllOK.map hf (l := l) (Q := (spliceT2Lists y z N Q R).1)
      (R := (spliceT2Lists y z N Q R).2) h.2
    simp only [mapStep]
    rw [spliceT2Lists_map hf]
    exact this

end Map

theorem stepsVal_eq {N : ℕ} (l : List (Fin N × Fin N × List (Fin N))) :
    stepsVal l = l.map (mapStep Fin.val) := by
  unfold stepsVal mapStep; rfl

variable {w N : ℕ}

/-- **The undo program on a chain of collapse steps.** For a valid crossing `cr` of the collapsed
graph, `t2UndoProg` writes the vertex lists of the crossing `undoT2Chain chain cr` of the input
graph, in at most `120 + 40 (N + |aT2Rec| + |Q| + |R|)` steps. -/
theorem t2UndoProg_chain {C A B : List (Fin N)} {a b : Fin N} {k : ℕ} {G H : SimpleGraph (Fin N)}
    (chain : T2Chain (Fin N) C A B a b k G H) {cr : CrossingWalks H C} (hcr : cr.Valid)
    (hw : 1 < 2 ^ w) {st : State} (hV : st.regs rUdV = N)
    (hrec : st.arrs aT2Rec = encodeT2 (stepsVal (t2Steps chain)))
    (hQ : st.arrs aUdQ = cr.Q.support.map Fin.val) (hR : st.arrs aUdR = cr.R.support.map Fin.val)
    (hVw : 2 * N + 1 < 2 ^ w) (hEw : (st.arrs aT2Rec).length + 3 < 2 ^ w) :
    ∃ crG, undoT2Chain chain cr = some crG ∧ crG.Valid ∧ crG.u₁ = cr.u₁ ∧ crG.v₁ = cr.v₁ ∧
      crG.u₂ = cr.u₂ ∧ crG.v₂ = cr.v₂ ∧
      ∃ st' c, Exec w t2UndoProg st st' c ∧
        c ≤ 120 + 40 * (N + (st.arrs aT2Rec).length + cr.Q.support.length +
          cr.R.support.length) ∧
        Keeps undoRegs undoArrs st st' ∧ st'.arrs aUdQ = crG.Q.support.map Fin.val ∧
        st'.arrs aUdR = crG.R.support.map Fin.val := by
  obtain ⟨crG, hun, hv, e1, e2, e3, e4, hsp, hok⟩ := undoT2Chain_splice chain hcr
  have hrev : (t2Steps chain).reverse.map (mapStep Fin.val) = (stepsVal (t2Steps chain)).reverse :=
    by rw [stepsVal_eq, List.map_reverse]
  have hok' := SpliceAllOK.map Fin.val_injective hok
  rw [hrev] at hok'
  -- the bounds hold since every vertex is in `Fin N`
  have hb : UndoBounds N (stepsVal (t2Steps chain)) (cr.Q.support.map Fin.val)
      (cr.R.support.map Fin.val) := by
    refine ⟨fun r hr => ?_, fun v hv => ?_, fun v hv => ?_⟩
    · rw [stepsVal_eq] at hr
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp hr
      simp only [mapStep]
      exact ⟨e.1.2, e.2.1.2, fun x hx => by
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx; exact u.2⟩
    · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hv; exact u.2
    · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hv; exact u.2
  rw [hrec] at hEw
  obtain ⟨st', c, hex, hc, hk, hQ', hR'⟩ := t2UndoProg_exec hw hok' hb hV hrec hQ hR hVw hEw
  have hmap := spliceT2All_map Fin.val_injective (t2Steps chain).reverse cr.Q.support
    cr.R.support
  rw [hrev] at hmap
  refine ⟨crG, hun, hv, e1, e2, e3, e4, st', c, hex, ?_, hk, ?_, ?_⟩
  · rw [hrec]; simpa using hc
  · rw [hQ', hmap, ← hsp]
  · rw [hR', hmap, ← hsp]

end

end GraphMinor.Compute.TwoPaths
