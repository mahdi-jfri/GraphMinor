module

public import GraphMinor.Compute.CrossingOpsSparsifyFrames

/-!
# The dense branch of sparsification

The command computes the four apex forests, selects the extra edges and cycle
edges, installs the retained graph, and appends its deletion record. Each phase
uses the same fixed scratch layout for all ambient graph sizes.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- The branch used when the graph has more than sixteen edges per active vertex. -/
def sparsifyDenseProg (a : InstArrs) (a_rec r_rec A R : ℕ) : Cmd :=
  .seq (sparsifyForestsProg a A R)
    (.seq (sparsifyRetainProg a A R)
      (.seq (installAdjProg a.st a.en a.ent (A + 70) R)
        (.seq (.assign (R + 8) (.len a.alive))
          (deletionAppendProg a_rec r_rec (A + 80) R))))

private theorem csr_mem_list (a : InstArrs) (x : ℕ)
    (h : x ∈ [a.st, a.en, a.ent]) : x ∈ a.list := by
  simp only [InstArrs.list, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem recBuf_preserved {N : ℕ} {x r k : ℕ}
    {recs : List (CrossRecord (Fin N))} {s z : State}
    (h : IsRecBufAt x r recs k s) (ha : z.arrs x = s.arrs x) (hr : z.regs r = s.regs r) :
    IsRecBufAt x r recs k z := by
  simpa only [IsRecBufAt, ha, hr] using h

/-- The dense branch returns the full sparsification data and the installed graph,
with one appended deletion record. Its hypotheses are exactly the local dense
case, encoded inputs, separation, free capacity, and a word bound. -/
theorem sparsifyDenseProg_exec {w N : ℕ} (a : InstArrs) (a_rec r_rec A R : ℕ)
    (hok : ArrsOk (a.list ++ [a_rec]) A) (hrr : r_rec < R)
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {recs : List (CrossRecord (Fin N))} {k : ℕ} {s : State}
    (hinst : IsInstanceAt a G S D s) (hcyc : HP25.IsCycleList G D)
    (hdense : 16 * S.card < G.edgeSet.ncard) (hbuf : IsRecBufAt a_rec r_rec recs k s)
    (hk : 2 ≤ k) (hw : 40 * instSize N G + (s.arrs a_rec).length + 4 < 2 ^ w) :
    ∃ s' t, Exec w (sparsifyDenseProg a a_rec r_rec A R) s s' t ∧
      t ≤ 3000 * instSize N G ∧ KeepsBelow R A [r_rec] (a.list ++ [a_rec]) s s' ∧
      (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
      ∃ Fs E₀, IsSparsifyData G (↑S) D Fs E₀ ∧
        IsInstanceAt a (sparsifyGraph G D Fs E₀) S D s' ∧
        IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.del (sparsifyGraph G D Fs E₀) S]) (k - 2) s' := by
  classical
  have hsz : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hoka : ArrsOk a.list A := ⟨(List.nodup_append.mp hok.1).1,
    fun x hx => hok.2 x (List.mem_append_left _ hx)⟩
  have hrecA : a_rec < A := hok.2 _ (by simp)
  have hrecnot : a_rec ∉ a.list := by
    have hh := (List.nodup_append.mp hok.1).2.2
    intro hm
    exact hh a_rec hm a_rec (by simp) rfl
  obtain ⟨lists, hadj⟩ := hinst.2.2.1
  obtain ⟨s1, t1, ess, he1, ht1, hlen, hseq, hflen, hp, ha1⟩ :=
    sparsifyForestsProg_exec (w := w) a A R hoka hinst hcyc (by omega)
  have hi1 := hinst.of_arrs_eq (fun x hx => ha1 x (hoka.2 x hx))
  have hadj1 := hadj.of_arrs_eq (ha1 _ (hoka.2 _ (by simp [InstArrs.list])))
    (ha1 _ (hoka.2 _ (by simp [InstArrs.list]))) (ha1 _ (hoka.2 _ (by simp [InstArrs.list])))
  obtain ⟨s2, t2, he2, ht2, ⟨newLists, hadj2⟩, hent2, hsub, hfin, hcard, ha2⟩ :=
    sparsifyRetainProg_exec (w := w) a A R hoka hi1 hadj1 hcyc hdense hlen hp (by omega)
  let E₀ := edgePrefixSet lists (3 * S.card - 5)
  let Fs := apexForests ess
  let H := sparsifyGraph G D Fs E₀
  have hHG : H ≤ G := fun _ _ h => h.1
  have hEH : H.edgeSet.ncard ≤ G.edgeSet.ncard := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hHG)
  have hi2 := hi1.of_arrs_eq (fun x hx => ha2 x (hoka.2 x hx))
  have hokB : ArrsOk a.list (A + 70) := ⟨hoka.1, fun x hx => (hoka.2 x hx).trans (by omega)⟩
  obtain ⟨s3, t3, he3, ht3, hi3, ha3, hr3⟩ := installAdjProg_instance_exec (w := w)
    a (A + 70) R hokB hi2 (fun u v hh => hinst.1 (hHG hh)) hadj2 hent2 (by omega)
  have ha12 : ∀ x, x < A → s2.arrs x = s.arrs x :=
    fun x hx => (ha2 x hx).trans (ha1 x hx)
  have hrec3 : s3.arrs a_rec = s.arrs a_rec := by
    rw [ha3 _ (by intro hh; apply hrecnot; exact csr_mem_list a _ hh), ha12 _ hrecA]
  have hrrec3 : s3.regs r_rec = s.regs r_rec :=
    (hr3 _ (Or.inl hrr)).trans ((sparsifyRetainProg_regs he2 hrr).trans
      (sparsifyForestsProg_regs he1 hrr))
  have hb3 := recBuf_preserved hbuf hrec3 hrrec3
  let s4 := s3.setReg (R + 8) N
  have he4 : Exec w (.assign (R + 8) (.len a.alive)) s3 s4 2 := by
    apply Exec.assign
    simpa using eval_len (w := w) hi3.2.1 (by simp; omega)
  have hb4 : IsRecBufAt a_rec r_rec recs k s4 :=
    recBuf_preserved hb3 rfl (by simp [s4, State.setReg_regs_ne, show r_rec ≠ R + 8 by omega])
  obtain ⟨s5, t5, he5, ht5, hb5, hl5, ha5, hr5⟩ := deletionAppendProg_exec (w := w)
    a_rec r_rec (A + 80) R (by omega) hrr (G := H) (S := S) hb4
    (by simp [s4]) hk (by dsimp [s4]; rw [hrec3]; omega)
  have hi5 : IsInstanceAt a H S D s5 := hi3.of_arrs_eq (fun x hx => by
    have hxA := hoka.2 x hx
    have hxrec : x ≠ a_rec := fun hh => hrecnot (hh ▸ hx)
    exact (ha5 x hxrec (by omega)).trans rfl)
  refine ⟨s5, t1 + (t2 + (t3 + (2 + t5))), .seq he1 (.seq he2 (.seq he3 (.seq he4 he5))),
    by omega, ⟨?_, ?_⟩, hl5.trans (congrArg List.length hrec3), Fs, E₀,
    ⟨hseq, hflen, hsub, hfin, ?_⟩, hi5, hb5⟩
  · intro r hr hne
    have hner : r ≠ r_rec := by simpa using hne
    rw [hr5 _ hr hner]
    dsimp [s4]
    rw [State.setReg_regs_ne _ _ (show r ≠ R + 8 by omega), hr3 _ (Or.inl hr),
      sparsifyRetainProg_regs he2 hr, sparsifyForestsProg_regs he1 hr]
  · intro x hx hnot
    have hxrec : x ≠ a_rec := by intro hh; apply hnot; simp [hh]
    have hxlist : x ∉ a.list := fun hh => hnot (List.mem_append_left _ hh)
    have hxout : x ∉ [a.st, a.en, a.ent] := by
      intro hh; apply hxlist; exact csr_mem_list a _ hh
    rw [ha5 x hxrec (by omega)]
    dsimp [s4]
    rw [ha3 x hxout, ha12 x hx]
  · simpa only [Set.ncard_coe_finset] using hcard

end GraphMinor.Compute.Crossing
