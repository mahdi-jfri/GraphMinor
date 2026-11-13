module

public import GraphMinor.Compute.GM06BfsPath
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Breadth-first search after a padded CSR construction

The candidate builder for Sections 12--13 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) reserves a polynomial entries buffer. BFS uses only its
written prefix. This file copies that prefix to the canonical list encoding before running the
verified BFS. Thus the returned path is exactly the pure BFS output, including its neighbour order.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The canonical entries length is the directed adjacency count. -/
theorem gm06EncodeLists_entries_length {n : ℕ} (lists : Fin n → List ℕ) :
    (encodeLists lists).2.2.length = totalAdjEntries lists := by
  simp only [encodeLists, List.length_flatten, List.map_ofFn, List.sum_ofFn,
    totalAdjEntries, Function.comp_apply]

/-- Copy the written entries prefix through scratch 613 and back to 622. -/
def gm06TrimCSRProg : Cmd :=
  .seq (gm13TabulateProg 650 (.reg 655) (.read 622 (.reg 650)) 613)
    (gm13TabulateProg 650 (.len 613) (.read 613 (.reg 650)) 622)

/-- Canonicalizing a constructed entries buffer preserves its exact
prefix, and changes only the entries array, scratch and copy index. -/
theorem gm06TrimCSRProg_exec {w cap : ℕ} (entries : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : entries.length < 2 ^ w)
    (hwords : ∀ x ∈ entries, x < 2 ^ w)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 622 655 entries cap s) :
    ∃ sf t, Exec w gm06TrimCSRProg s sf t ∧ t ≤ 12 + 28 * entries.length ∧
      Keeps [650] [613, 622] s sf ∧ sf.arrs 622 = entries := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm13TabulateProg_exec
    650 (.reg 655) (.read 622 (.reg 650)) 613 entries s hw hlen
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 655 (by decide)).trans hbuf.2) hlen)
    (fun st i hi hk hr => by
      have ha : st.arrs 622 = entries ++ List.replicate cap 0 := (hk.2 622 (by decide)).trans hbuf.1
      have he := GraphMinor.Compute.Crossing.eval_read (a := 622)
        (GraphMinor.Compute.Crossing.eval_reg hr (hi.trans hlen))
        (by simp only [ha, List.length_append]; omega)
        (by simpa only [ha, List.getElem_append_left hi] using hwords _ (List.getElem_mem hi))
      simpa only [ha, List.getElem_append_left hi] using he)
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm13TabulateProg_exec
    650 (.len 613) (.read 613 (.reg 650)) 622 entries s₁ hw hlen
    (fun st hk => GraphMinor.Compute.Crossing.eval_len ((hk.2 613 (by decide)).trans hd₁) hlen)
    (fun st i hi hk hr => by
      have ha := (hk.2 613 (by decide)).trans hd₁
      have he := GraphMinor.Compute.Crossing.eval_read (a := 613)
        (GraphMinor.Compute.Crossing.eval_reg hr (hi.trans hlen))
        (by simpa only [ha] using hi) (by simpa only [ha] using hwords _ (List.getElem_mem hi))
      simpa only [ha] using he)
  refine ⟨sf, t₁ + tf, .seq he₁ hef, ?_,
    (hk₁.mono (fun _ h => h) (by simp)).trans hkf (fun _ h => h) (by simp), hdf⟩
  simp only [Expr.cost] at ht₁ htf
  omega

/-- Canonicalize the entries buffer, then run BFS_PATH. -/
def gm06BfsBufferedProg : Cmd := .seq gm06TrimCSRProg gm06BfsPathProg

/-- The buffered search returns the exact pure BFS result, with linear
time in the vertex and adjacency sizes. The padding is never input to
its pure specification. -/
theorem gm06BfsBufferedProg_exec {w n cap : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lists : Fin n → List ℕ) (hG : IsAdjListFamily G lists) (u v : Fin n) (s : State)
    (hw : n + 4 < 2 ^ w) (hlen : (encodeLists lists).2.2.length < 2 ^ w)
    (h620 : s.regs 620 = n) (h644 : s.regs 644 = u.val) (h645 : s.regs 645 = v.val)
    (hgs : s.arrs 620 = (encodeLists lists).1) (hge : s.arrs 621 = (encodeLists lists).2.1)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 622 655 (encodeLists lists).2.2 cap s) :
    ∃ sf t, Exec w gm06BfsBufferedProg s sf t ∧
      t ≤ 168 + 67 * n + 57 * totalAdjEntries lists ∧
      Keeps ([650] ++ List.range' 630 14 ++ [646, 647]) ([613, 622] ++ List.range' 630 5) s sf ∧
      gm06BfsPathResult sf = gm06BfsPathWords G lists u v ∧
      (sf.regs 646 = 0 ∨ sf.regs 646 = 1) := by
  have hwords : ∀ x ∈ (encodeLists lists).2.2, x < 2 ^ w := by
    intro x hx
    obtain ⟨row, hr, hx⟩ := List.mem_flatten.mp hx
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hr
    exact ((hG u).1 x hx).trans (by omega)
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06TrimCSRProg_exec _ s (by omega) hlen hwords hbuf
  obtain ⟨sf, tf, hef, htf, hkf, hdf, hflag⟩ := gm06BfsPathProg_exec G lists hG u v s₁
    ((hk₁.1 620 (by decide)).trans h620) ((hk₁.1 644 (by decide)).trans h644)
    ((hk₁.1 645 (by decide)).trans h645) ((hk₁.2 620 (by decide)).trans hgs)
    ((hk₁.2 621 (by decide)).trans hge) hd₁ hw hlen
  refine ⟨sf, t₁ + tf, .seq he₁ hef, ?_,
    (hk₁.mono (by simp) (by simp)).trans hkf (by
      intro r hr
      simp only [List.mem_append] at hr ⊢
      tauto) (by intro a ha; exact List.mem_append_right _ ha), hdf, hflag⟩
  have hentries := gm06EncodeLists_entries_length lists
  rw [hentries] at ht₁
  omega

end GraphMinor.Compute
