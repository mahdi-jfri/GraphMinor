module

public import GraphMinor.Compute.SpecsCrossing

/-!
# The subprograms of the crossing extractor, with the records in a buffer

`SpecsCrossing.lean` keeps the records in an array that holds exactly their encodings
(`IsRecordsAt`), and asks that a contraction, a replacement or a sparsification append a record in
`C (N + |E(G)| + 1)` steps. This cannot be met. An array of the Word RAM changes its length only
by an allocation, and an allocation costs the new length (`Exec.length_eq_or_le` in
`CrossingOpsRecord.lean`). So an append to an array that holds exactly the records costs at least
the length of all the records. That length is not bounded by the size of the instance: the
records of the contractions list old neighbourhoods, so after `N` contractions they may hold about
`N²` entries, and `N` appends would then cost about `N³` steps.

This file states the same subprograms with the records in a **buffer** (`IsRecBufAt`): an array
whose prefix holds the encodings, oldest first, followed by `k` free entries, all `0`, with the
length of the prefix in a register `r_rec`. An append writes the new encoding into the free
entries and moves `r_rec`, so it costs only the length of the new encoding. The array is
allocated once, by the top level, with enough free entries for all the records.

## The capacity

Every claim below that appends records asks for at least as many free entries as its time bound,
and promises to use at most that many: an append of a record of length `ℓ` takes at least `ℓ`
steps. So the total length of the records is at most the total time of the subprograms that
append them, which is `O((N + 1)(N + |E(G)| + 1))` for an input graph `G` (initial cleaning
`C (N + 1) (N + |E(G)| + 1)`, then the loop `C (N + 1) (N + |E(G')| + 1)` with
`|E(G')| ≤ |E(G)| + 3N`). The top level therefore allocates the buffer with
`C' (N + 1) (N + |E(G)| + 1)` entries for a constant `C'` fixed by the constants of
`InitialCleaningRecProgClaim` and `LoopRecProgClaim`; the allocation costs the same, which is
within the time `O(N (N + |E(G)|))` of the extractor.

## The claims

Each claim is the claim of `SpecsCrossing.lean` with the same name without `Rec`, with these
changes only:
* `IsRecordsAt a_rec recs s` becomes `IsRecBufAt a_rec r_rec recs k s`, for a register
  `r_rec < r_base` that the program may change;
* a claim that appends asks `C * T ≤ k`, where `C * T` is its time bound, and gives the records
  in the same array with `k'` free entries, `k ≤ k' + C * T`, and the same array length;
* the length bounds on `a_rec` of `InitialCleaningProgClaim`, `RestoreProgClaim` and
  `LoopProgClaim` are replaced by this bound on the free entries;
* `TrialRecProgClaim` gives the records of the trial in a buffer `a_trec`, `r_trec` that it
  allocates itself;
* `LiftRecProgClaim` takes time `C (r + (|recs| + 1) (N + 1))`, where `r` is the length of the
  prefix of records.

The copy of an instance is `CopyInstanceRecProgClaim`, which adds to `CopyInstanceProgClaim` that
`D` is a cycle: without it the claim is false (`not_copyInstanceProgClaim` in
`CrossingOpsCopy.lean`), since the array of `D` can then be longer than `C (N + |E(G)| + 1)`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### The records in a buffer -/

/-- **The records in a buffer**: the array `x` holds the encodings of `recs`, oldest first,
followed by `k` entries `0`, and the register `r` holds the length of the encodings. -/
def IsRecBufAt {N : ℕ} (x r : ℕ) (recs : List (CrossRecord (Fin N))) (k : ℕ) (s : State) :
    Prop :=
  ∃ ls : List (List ℕ), List.Forall₂ IsRecordEnc recs ls ∧
    s.arrs x = ls.flatten ++ List.replicate k 0 ∧ s.regs r = ls.flatten.length

/-! ### The subprograms -/

/-- **The copy of an instance** (Section 10: "copy the current instance"), for an instance whose
`D` is a cycle. -/
def CopyInstanceRecProgClaim : Prop :=
  ∀ (a b : InstArrs) (a_base r_base : ℕ), ArrsOk (a.list ++ b.list) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (s : State),
      wordSize c (instSize N G) ≤ w → IsInstanceAt a G S D s → HP25.IsCycleList G D →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧ KeepsBelow r_base a_base [] b.list s s' ∧
        IsInstanceAt b G S D s'

/-- **The replacement** (Section 3), with the records in a buffer: "The *replacement* deletes $A$
and adds every missing edge of the clique on $S$." -/
def ReplaceRecProgClaim : Prop :=
  ∀ (a : InstArrs) (a_del a_bd a_rep a_rec r_rec a_base r_base : ℕ),
    ArrsOk (a.list ++ [a_del, a_bd, a_rep, a_rec]) a_base → r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (r : ReplRecord (Fin N)) (recs : List (CrossRecord (Fin N)))
      (S' : Finset (Fin N)) (k : ℕ) (s : State),
      wordSize c (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → r.graph = G → r.verts = S → r.IsValid D →
      (S' : Set (Fin N)) = r.newVerts →
      IsSetListAt a_del r.deleted s → IsSetListAt a_bd (r.boundary : Set (Fin N)) s →
      IsSetListAt a_rep r.rep s →
      IsRecBufAt a_rec r_rec recs k s → C * instSize N G ≤ k →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s' ∧
        IsInstanceAt a r.newGraph S' D s' ∧
        ∃ k', IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.repl r]) k' s' ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧ k ≤ k' + C * instSize N G

/-- **The contraction** (Section 9), with the records in a buffer: "Contract $uv$ to a new vertex
$w$, suppressing loops and duplicate edges." -/
def ContractRecProgClaim : Prop :=
  ∀ (a : InstArrs) (a_rec r_rec a_base r_base : ℕ), ArrsOk (a.list ++ [a_rec]) a_base →
    r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (G : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (u v : Fin N) (recs : List (CrossRecord (Fin N)))
      (k : ℕ) (s : State),
      wordSize c (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → IsTrialEdge G D u v →
      s.regs r_base = u.val → s.regs (r_base + 1) = v.val →
      IsRecBufAt a_rec r_rec recs k s → C * instSize N G ≤ k →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s' ∧
        IsInstanceAt a (contractGraph G u v) (S.erase u) (contractCycle D u) s' ∧
        ∃ k', IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.contr
          { graph := G, verts := (S : Set (Fin N)), cycle := D, u := u, v := v }]) k' s' ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧ k ≤ k' + C * instSize N G

/-- **Initial cleaning** (Section 4), with the records in a buffer. -/
def InitialCleaningRecProgClaim : Prop :=
  ∀ (a : InstArrs) (a_rec r_rec a_base r_base : ℕ), ArrsOk (a.list ++ [a_rec]) a_base →
    r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (recs₀ : List (CrossRecord (Fin N))) (k : ℕ) (s : State),
      wordSize c ((N + 1) * instSize N G + (s.arrs a_rec).length) ≤ w →
      IsInstanceAt a G S D s → HP25.IsCycleList G D → IsRecBufAt a_rec r_rec recs₀ k s →
      C * (N + 1) * instSize N G ≤ k →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * (N + 1) * instSize N G ∧
        KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s' ∧
        ∃ (G' : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (recs : List (CrossRecord (Fin N)))
          (k' : ℕ),
          IsInstanceAt a G' S' D s' ∧ IsClean G' (S' : Set (Fin N)) D ∧
          IsHistoryFin G S D recs G' S' D ∧ ContractionsLong recs ∧
          IsRecBufAt a_rec r_rec (recs₀ ++ recs) k' s' ∧
          G'.edgeSet.ncard ≤ G.edgeSet.ncard + 3 * N ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧ k ≤ k' + C * (N + 1) * instSize N G

/-- **Sparsification** (Section 7.2), with the records in a buffer: "If $M\le16N$, we do
nothing." -/
def SparsifyRecProgClaim : Prop :=
  ∀ (a : InstArrs) (a_rec r_rec a_base r_base : ℕ), ArrsOk (a.list ++ [a_rec]) a_base →
    r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (recs : List (CrossRecord (Fin N))) (k : ℕ) (s : State),
      wordSize c (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → IsRecBufAt a_rec r_rec recs k s → C * instSize N G ≤ k →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s' ∧
        (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
        ((G.edgeSet.ncard ≤ 16 * S.card ∧ IsInstanceAt a G S D s' ∧
            IsRecBufAt a_rec r_rec recs k s') ∨
          (16 * S.card < G.edgeSet.ncard ∧
            ∃ (Fs : List (SimpleGraph (Option (Fin N)))) (E₀ : Set (Sym2 (Fin N))) (k' : ℕ),
              IsSparsifyData G (S : Set (Fin N)) D Fs E₀ ∧
              IsInstanceAt a (sparsifyGraph G D Fs E₀) S D s' ∧
              IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.del (sparsifyGraph G D Fs E₀) S]) k'
                s' ∧ k ≤ k' + C * instSize N G))

/-- **Restoration** (Section 9.2), with the records in a buffer: "We process the fixed list $M$,
once for each marker." -/
def RestoreRecProgClaim : Prop :=
  ∀ (a : InstArrs) (a_mk a_rec r_rec a_base r_base : ℕ),
    ArrsOk (a.list ++ [a_mk, a_rec]) a_base → r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (H : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (v : Fin N) (M : List (Fin N))
      (recs : List (CrossRecord (Fin N))) (k : ℕ) (s : State),
      wordSize c ((M.length + 1) * instSize N H + (s.arrs a_rec).length) ≤ w →
      IsInstanceAt a H S D s → HP25.IsCycleList H D → v ∈ S →
      RootedConn (apex H D) (apexVerts (S : Set (Fin N))) none 3 →
      RootedConn (apex H D) (restoreVerts (S : Set (Fin N)) v) none 2 →
      s.regs r_base = v.val → s.arrs a_mk = M.map Fin.val → IsRecBufAt a_rec r_rec recs k s →
      C * (M.length + 1) * instSize N H ≤ k →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * (M.length + 1) * instSize N H ∧
        KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s' ∧
        ∃ (H' : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (rs : List (ReplRecord (Fin N)))
          (k' : ℕ),
          IsRestoreRun D v M H (S : Set (Fin N)) H' (S' : Set (Fin N)) rs ∧
          IsInstanceAt a H' S' D s' ∧
          IsRecBufAt a_rec r_rec (recs ++ rs.map CrossRecord.repl) k' s' ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
          k ≤ k' + C * (M.length + 1) * instSize N H

/-- **One trial** (Section 10, step 4), with the records of the trial in a buffer `a_trec`,
`r_trec` that the trial allocates. -/
def TrialRecProgClaim : Prop :=
  ∀ (prog : Cmd) (Cp cp_w : ℕ), IsPlanarityProg prog Cp cp_w →
  ∀ (a b : InstArrs) (a_trec r_trec a_Q a_R a_base r_base : ℕ),
    ArrsOk (a.list ++ b.list ++ [a_trec, a_Q, a_R]) a_base → r_trec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (K : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (u v : Fin N) (s : State),
      wordSize c ((N + 1) * instSize N K) ≤ w → IsInstanceAt a K S D s →
      HP25.IsCycleList K D → IsClean K (S : Set (Fin N)) D → IsTrialEdge K D u v →
      (u ∈ D → 4 < D.length) → s.regs r_base = u.val → s.regs (r_base + 1) = v.val →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * ((K.neighborSet u).ncard + 1) * instSize N K ∧
        KeepsBelow r_base a_base [r_trec] (b.list ++ [a_trec, a_Q, a_R]) s s' ∧
        ∃ (H : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (recs : List (CrossRecord (Fin N)))
          (k' : ℕ),
          IsInstanceAt b H S' (contractCycle D u) s' ∧
          IsHistoryFin K S D recs H S' (contractCycle D u) ∧ ContractionsLong recs ∧
          IsRecBufAt a_trec r_trec recs k' s' ∧ IsClean H (S' : Set (Fin N)) (contractCycle D u) ∧
          H.edgeSet.ncard ≤ K.edgeSet.ncard + 3 * (K.neighborSet u).ncard ∧
          ((s'.regs r_base = 2 ∧ IsCrossingPairAt H (contractCycle D u) a_Q a_R s') ∨
            (s'.regs r_base = 0 ∧ Nonempty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂) ∨
            (s'.regs r_base = 1 ∧ IsEmpty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂))

/-- **The loop** (Section 10), with the records in a buffer: "We repeat the following iteration
while in the last state." -/
def LoopRecProgClaim : Prop :=
  ∀ (prog : Cmd) (Cp cp_w : ℕ), IsPlanarityProg prog Cp cp_w →
  ∀ (a : InstArrs) (a_rec r_rec a_Q a_R a_base r_base : ℕ),
    ArrsOk (a.list ++ [a_rec, a_Q, a_R]) a_base → r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (K : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (recs₀ : List (CrossRecord (Fin N))) (k : ℕ)
      (s : State),
      wordSize c ((N + 1) * instSize N K + (s.arrs a_rec).length) ≤ w →
      IsInstanceAt a K S D s → HP25.IsCycleList K D → IsClean K (S : Set (Fin N)) D →
      IsEmpty (HP25.PlaneEmbedding K (S : Set (Fin N))) → HP25.IsCrossed K D →
      IsRecBufAt a_rec r_rec recs₀ k s → C * (N + 1) * instSize N K ≤ k →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * (N + 1) * instSize N K ∧
        KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec, a_Q, a_R]) s s' ∧
        ∃ (K' : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (D' : List (Fin N))
          (recs : List (CrossRecord (Fin N))) (k' : ℕ),
          IsHistoryFin K S D recs K' S' D' ∧ ContractionsLong recs ∧
          IsRecBufAt a_rec r_rec (recs₀ ++ recs) k' s' ∧ IsCrossingPairAt K' D' a_Q a_R s' ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧ k ≤ k' + C * (N + 1) * instSize N K

/-- **The lifts** (Section 11 and Lemma 1), with the records in a buffer: "Reversing all
accepted operations gives two disjoint $C$-paths in the original graph, with alternating ends." The
time counts the length `s.regs r_rec` of the prefix of records, not the free entries. -/
def LiftRecProgClaim : Prop :=
  ∀ (a_rec r_rec a_Q a_R a_base r_base : ℕ), ArrsOk [a_rec, a_Q, a_R] a_base → r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)]
      (recs : List (CrossRecord (Fin N))) (k : ℕ) (L₁ L₂ : List (Fin N)) (s : State),
      wordSize c ((s.arrs a_rec).length + (recs.length + 1) * (N + 1)) ≤ w →
      IsRecBufAt a_rec r_rec recs k s → s.arrs a_Q = L₁.map Fin.val →
      s.arrs a_R = L₂.map Fin.val → L₁.length ≤ N → L₂.length ≤ N →
      (∃ P, IsLift recs (L₁, L₂) P) →
      ∃ s' t, Exec w P s s' t ∧
        t ≤ C * (s.regs r_rec + (recs.length + 1) * (N + 1)) ∧
        KeepsBelow r_base a_base [] [a_Q, a_R] s s' ∧
        ∃ P', IsLift recs (L₁, L₂) P' ∧ s'.arrs a_Q = P'.1.map Fin.val ∧
          s'.arrs a_R = P'.2.map Fin.val

end GraphMinor.Compute.Crossing
