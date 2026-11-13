module

public import GraphMinor.Compute.Algorithm92Lift
public import GraphMinor.Compute.Algorithm92Runs

/-!
# Graph Minors XIII, (9.2): compressing a union of paths (`Algorithm92Compress.lean`)

The algorithm of (9.2) (page 101) searches in `H ∪ F`, which has bounded size "exept for divalent
vertices". We describe `H ∪ F` by a list `Ps` of paths of `G` and a set `S` of *nodes* that holds
the two ends of every path (`IsPathSystem`). A vertex of a path that is not a node lies in only one
path. Every maximal block of non-nodes of a path (a *run*, see `Algorithm92Runs.lean`) is then
replaced by a single vertex.

* `cBlob y` is the run of `y` (or `[y]` for a node), `cRep y` is its last vertex, and `cPrev y`,
  `cNext y` are the nodes just before and just after the run.
* `cVerts` is the set of nodes and of the last vertices of the runs; these are the vertices of the
  compressed graph. Two of them are adjacent (`CAdj`) when some edge of a path joins their runs.
* `isBlobMap_cBlobMap`: after numbering `cVerts` by `Fin N`, the runs form a blob map
  (`BlobMap.IsBlobMap`) from the compressed graph `cGraph` to `G`. So an answer found in the
  compressed graph lifts to `G` (`Algorithm92Lift.lean`).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {n : ℕ}

theorem isSimpleWalkList_iff_consec {G : MultiDigraph n} :
    ∀ {L : List (Fin n)}, IsSimpleWalkList G L ↔ ∀ u v, Consec L u v → G.toSimpleGraph.Adj u v
  | [] => by
    simp only [IsSimpleWalkList, true_iff]
    rintro u v ⟨A, B, h⟩
    cases A <;> simp at h
  | [a] => by
    simp only [IsSimpleWalkList, true_iff]
    rintro u v ⟨A, B, h⟩
    cases A with
    | nil => simp at h
    | cons x A => cases A <;> simp at h
  | a :: b :: rest => by
    simp only [IsSimpleWalkList]
    rw [isSimpleWalkList_iff_consec]
    constructor
    · rintro ⟨hab, hrest⟩ u v ⟨A, B, h⟩
      cases A with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        rw [← h.1, ← h.2.1]; exact hab
      | cons x A =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact hrest u v ⟨A, B, h.2⟩
    · intro h
      exact ⟨h a b ⟨[], rest, rfl⟩, fun u v huv => h u v (huv.cons a)⟩

theorem isSimpleWalkList_infix {G : MultiDigraph n} {L M : List (Fin n)}
    (hM : IsSimpleWalkList G M) (hLM : L <:+: M) : IsSimpleWalkList G L :=
  isSimpleWalkList_iff_consec.mpr fun u v huv =>
    isSimpleWalkList_iff_consec.mp hM u v (huv.infix hLM)

/-- The node test of the node set `S`, as a Boolean. -/
abbrev nodeB (S : Finset (Fin n)) (y : Fin n) : Bool := decide (y ∈ S)

/-- A list `Ps` of paths of `G` with a node set `S`: each path has no repeated vertex, is a walk of
`G`, and starts and ends at a node; and a vertex that is not a node lies on at most one path. -/
structure IsPathSystem (G : MultiDigraph n) (S : Finset (Fin n)) (Ps : List (List (Fin n))) :
    Prop where
  nodup : ∀ P ∈ Ps, P.Nodup
  walk : ∀ P ∈ Ps, IsSimpleWalkList G P
  head_mem : ∀ P ∈ Ps, ∀ a, P.head? = some a → a ∈ S
  getLast_mem : ∀ P ∈ Ps, ∀ c, P.getLast? = some c → c ∈ S
  unique : ∀ P ∈ Ps, ∀ Q ∈ Ps, ∀ y, y ∉ S → y ∈ P → y ∈ Q → P = Q

variable (S : Finset (Fin n)) (Ps : List (List (Fin n)))

/-- The first path of `Ps` through `y`. -/
def pathOf (y : Fin n) : Option (List (Fin n)) :=
  Ps.find? (fun P => decide (y ∈ P))

/-- The blob of `y`: `[y]` for a node, and the run of `y` in its path otherwise. -/
def cBlob (y : Fin n) : List (Fin n) :=
  if y ∈ S then [y] else
    match pathOf Ps y with
    | some P => run (nodeB S) P y
    | none => [y]

theorem cBlob_ne_nil (y : Fin n) : cBlob S Ps y ≠ [] := by
  unfold cBlob
  split_ifs
  · simp
  · split
    · unfold run; simp
    · simp

/-- The vertex that stands for the blob of `y`: its last vertex. -/
def cRep (y : Fin n) : Fin n :=
  (cBlob S Ps y).getLast (cBlob_ne_nil S Ps y)

/-- The node before the run of `y`. -/
def cPrev (y : Fin n) : Fin n :=
  match pathOf Ps y with
  | some P => runPrev (nodeB S) P y
  | none => y

/-- The node after the run of `y`. -/
def cNext (y : Fin n) : Fin n :=
  match pathOf Ps y with
  | some P => runNext (nodeB S) P y
  | none => y

/-- `y` lies on some path of `Ps`. -/
def OnPath (y : Fin n) : Prop := ∃ P ∈ Ps, y ∈ P

/-- `y` and `z` follow each other on some path of `Ps`. -/
def CEdge (y z : Fin n) : Prop := ∃ P ∈ Ps, Consec P y z ∨ Consec P z y

/-- Adjacency in the compressed graph: two distinct vertices whose blobs are joined by an edge of
a path. -/
def CAdj (u v : Fin n) : Prop :=
  u ≠ v ∧ ∃ y z, CEdge Ps y z ∧ cRep S Ps y = u ∧ cRep S Ps z = v

open Classical in
/-- The vertices of the compressed graph: the nodes and the last vertices of the runs. -/
noncomputable def cVerts : Finset (Fin n) :=
  Finset.univ.filter (fun y => y ∈ S ∨ (OnPath Ps y ∧ cRep S Ps y = y))

variable {S Ps}

theorem CEdge.symm {y z : Fin n} (h : CEdge Ps y z) : CEdge Ps z y := by
  obtain ⟨P, hP, h⟩ := h
  exact ⟨P, hP, h.symm⟩

theorem CAdj.symm {u v : Fin n} (h : CAdj S Ps u v) : CAdj S Ps v u := by
  obtain ⟨huv, y, z, hyz, hy, hz⟩ := h
  exact ⟨huv.symm, z, y, hyz.symm, hz, hy⟩

theorem CEdge.onPath_left {y z : Fin n} (h : CEdge Ps y z) : OnPath Ps y := by
  obtain ⟨P, hP, h | h⟩ := h
  · exact ⟨P, hP, h.mem_left⟩
  · exact ⟨P, hP, h.mem_right⟩

theorem CEdge.onPath_right {y z : Fin n} (h : CEdge Ps y z) : OnPath Ps z :=
  h.symm.onPath_left

theorem cBlob_of_mem_S {y : Fin n} (hy : y ∈ S) : cBlob S Ps y = [y] := by
  simp [cBlob, hy]

theorem cRep_of_mem_S {y : Fin n} (hy : y ∈ S) : cRep S Ps y = y := by
  simp [cRep, cBlob_of_mem_S hy]

section PathSystem

variable {G : MultiDigraph n} (hP : IsPathSystem G S Ps)
include hP

theorem IsPathSystem.pathOf_eq {P : List (Fin n)} (hPs : P ∈ Ps) {y : Fin n} (hyP : y ∈ P)
    (hyS : y ∉ S) : pathOf Ps y = some P := by
  unfold pathOf
  cases hf : Ps.find? (fun P => decide (y ∈ P)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simpa using hyP) (hf P hPs)
  | some Q =>
    have hQ : Q ∈ Ps := List.mem_of_find?_eq_some hf
    have hyQ : y ∈ Q := by simpa using List.find?_some hf
    rw [hP.unique Q hQ P hPs y hyS hyQ hyP]

theorem IsPathSystem.CEdge.adj {y z : Fin n} (h : CEdge Ps y z) : G.toSimpleGraph.Adj y z := by
  obtain ⟨P, hPs, h | h⟩ := h
  · exact isSimpleWalkList_iff_consec.mp (hP.walk P hPs) y z h
  · exact (isSimpleWalkList_iff_consec.mp (hP.walk P hPs) z y h).symm

/-- **The run of a non-node.** A vertex `y ∉ S` on a path `P` of `Ps` lies in a block
`P = A ++ a :: R ++ c :: B` with nodes `a`, `c` and no node in `R`; every vertex of `R` has blob
`R`, previous node `a` and next node `c`. -/
theorem IsPathSystem.exists_run {P : List (Fin n)} (hPs : P ∈ Ps) {y : Fin n} (hyP : y ∈ P)
    (hyS : y ∉ S) :
    ∃ A a R c B, P = A ++ a :: R ++ c :: B ∧ a ∈ S ∧ c ∈ S ∧ (∀ z ∈ R, z ∉ S) ∧ y ∈ R ∧
      ∀ z ∈ R, cBlob S Ps z = R ∧ cPrev S Ps z = a ∧ cNext S Ps z = c := by
  obtain ⟨A, a, R, c, B, hdec, ha, hc, hR, hy⟩ :=
    exists_decomp (s := nodeB S) hyP (by simpa using hyS)
      (fun a h => by simpa using hP.head_mem P hPs a h)
      (fun c h => by simpa using hP.getLast_mem P hPs c h)
  have hR' : ∀ z ∈ R, z ∉ S := fun z hz => by simpa using hR z hz
  refine ⟨A, a, R, c, B, hdec, by simpa using ha, by simpa using hc, hR', hy, fun z hz => ?_⟩
  have hzP : z ∈ P := by rw [hdec]; simp [hz]
  have hpath := hP.pathOf_eq hPs hzP (hR' z hz)
  have hnd := hP.nodup P hPs
  refine ⟨?_, ?_, ?_⟩
  · simp only [cBlob, hR' z hz, ite_false, hpath]
    exact run_eq_of_decomp hnd hdec ha hc hR hz
  · simp only [cPrev, hpath]
    exact runPrev_eq_of_decomp hnd hdec ha hR hz
  · simp only [cNext, hpath]
    exact runNext_eq_of_decomp hnd hdec hc hR hz

theorem IsPathSystem.cRep_not_mem {y : Fin n} (hy : OnPath Ps y) (hyS : y ∉ S) :
    cRep S Ps y ∉ S ∧ OnPath Ps (cRep S Ps y) ∧ cRep S Ps (cRep S Ps y) = cRep S Ps y ∧
      cRep S Ps y ∈ cBlob S Ps y := by
  obtain ⟨P, hPs, hyP⟩ := hy
  obtain ⟨A, a, R, c, B, hdec, -, -, hR, hyR, hrun⟩ := hP.exists_run hPs hyP hyS
  have hRne : R ≠ [] := List.ne_nil_of_mem hyR
  have hrep : cRep S Ps y = R.getLast hRne := by
    simp only [cRep, (hrun y hyR).1]
  have hlast : R.getLast hRne ∈ R := List.getLast_mem hRne
  refine ⟨?_, ⟨P, hPs, ?_⟩, ?_, ?_⟩
  · rw [hrep]; exact hR _ hlast
  · rw [hrep, hdec]; simp [hlast]
  · rw [hrep]
    simp only [cRep, (hrun _ hlast).1]
  · rw [hrep, (hrun y hyR).1]; exact hlast

theorem IsPathSystem.mem_S_of_cRep_mem_S {y : Fin n} (hy : OnPath Ps y) (hyS : cRep S Ps y ∈ S) :
    y ∈ S := by
  by_contra h
  exact (hP.cRep_not_mem hy h).1 hyS

theorem IsPathSystem.cRep_mem_cVerts {y : Fin n} (hy : y ∈ S ∨ OnPath Ps y) :
    cRep S Ps y ∈ cVerts S Ps := by
  classical
  unfold cVerts
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hyS : y ∈ S
  · rw [cRep_of_mem_S hyS]; exact Or.inl hyS
  · have hy' : OnPath Ps y := hy.resolve_left hyS
    obtain ⟨-, h2, h3, -⟩ := hP.cRep_not_mem hy' hyS
    exact Or.inr ⟨h2, h3⟩

omit hP in
theorem mem_cVerts_iff {v : Fin n} :
    v ∈ cVerts S Ps ↔ v ∈ S ∨ (OnPath Ps v ∧ cRep S Ps v = v) := by
  classical
  unfold cVerts
  simp

/-- The vertices of the blob of a vertex `v` of the compressed graph are the vertices whose
representative is `v`. -/
theorem IsPathSystem.mem_cBlob_iff {v : Fin n} (hv : v ∈ cVerts S Ps) {y : Fin n} :
    y ∈ cBlob S Ps v ↔ (y ∈ S ∨ OnPath Ps y) ∧ cRep S Ps y = v := by
  by_cases hvS : v ∈ S
  · rw [cBlob_of_mem_S hvS, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨Or.inl hvS, cRep_of_mem_S hvS⟩
    · rintro ⟨hy, hyr⟩
      by_cases hyS : y ∈ S
      · rw [cRep_of_mem_S hyS] at hyr; exact hyr
      · exact absurd (hyr ▸ hvS) (hP.cRep_not_mem (hy.resolve_left hyS) hyS).1
  · obtain ⟨hvP, hvr⟩ := (mem_cVerts_iff.mp hv).resolve_left hvS
    obtain ⟨P, hPs, hvP'⟩ := hvP
    obtain ⟨A, a, R, c, B, hdec, -, -, hR, hvR, hrun⟩ := hP.exists_run hPs hvP' hvS
    rw [(hrun v hvR).1]
    have hRne : R ≠ [] := List.ne_nil_of_mem hvR
    have hvlast : R.getLast hRne = v := by
      rw [← hvr]; simp only [cRep, (hrun v hvR).1]
    constructor
    · intro hyR
      refine ⟨Or.inr ⟨P, hPs, by rw [hdec]; simp [hyR]⟩, ?_⟩
      simp only [cRep, (hrun y hyR).1, hvlast]
    · rintro ⟨hy, hyr⟩
      have hyS : y ∉ S := fun hyS => by
        rw [cRep_of_mem_S hyS] at hyr; exact hvS (hyr ▸ hyS)
      obtain ⟨Q, hQs, hyQ⟩ := hy.resolve_left hyS
      obtain ⟨A', a', R', c', B', hdec', -, -, -, hyR', hrun'⟩ := hP.exists_run hQs hyQ hyS
      have hR'ne : R' ≠ [] := List.ne_nil_of_mem hyR'
      have hlast' : R'.getLast hR'ne ∈ R' := List.getLast_mem hR'ne
      have hv' : v = R'.getLast hR'ne := by
        rw [← hyr]; simp only [cRep, (hrun' y hyR').1]
      have hvR' : v ∈ R' := hv' ▸ hlast'
      have : R' = R := by
        rw [← (hrun' v hvR').1]
        exact ((hrun v hvR).1)
      rw [← this]; exact hyR'

/-- The neighbours along the paths of a vertex `y` of a run `R` (between the nodes `a` and `c`)
are in `R`, or are `a` or `c`. -/
theorem IsPathSystem.cEdge_mem_run {P A R B : List (Fin n)} {a c y z : Fin n} (hPs : P ∈ Ps)
    (hdec : P = A ++ a :: R ++ c :: B) (hyR : y ∈ R) (hyS : y ∉ S) (hyz : CEdge Ps y z) :
    z ∈ R ∨ z = a ∨ z = c := by
  obtain ⟨Q, hQs, hQ⟩ := hyz
  have hyP : y ∈ P := by rw [hdec]; simp [hyR]
  have hyQ : y ∈ Q := by rcases hQ with h | h; exacts [h.mem_left, h.mem_right]
  have hQP : Q = P := hP.unique Q hQs P hPs y hyS hyQ hyP
  subst hQP
  have hnd := hP.nodup Q hPs
  obtain ⟨R₁, R₂, rfl⟩ := List.append_of_mem hyR
  rcases hQ with h | h
  · have hsplit : Q = (A ++ a :: R₁) ++ y :: (R₂ ++ c :: B) := by rw [hdec]; simp
    have := h.eq_of_split hnd hsplit
    cases R₂ with
    | nil => simp at this; exact Or.inr (Or.inr this.symm)
    | cons w R₂ => simp at this; subst this; left; simp
  · have hsplit : Q = (A ++ a :: R₁) ++ y :: (R₂ ++ c :: B) := by rw [hdec]; simp
    rcases List.eq_nil_or_concat' R₁ with rfl | ⟨L', w, rfl⟩
    · have := h.eq_of_split' hnd hsplit
      simp at this; exact Or.inr (Or.inl this.symm)
    · have hsplit' : Q = ((A ++ a :: L') ++ [w]) ++ y :: (R₂ ++ c :: B) := by rw [hsplit]; simp
      have := h.eq_of_split' hnd hsplit'
      rw [List.getLast?_concat] at this
      cases this
      left; simp

end PathSystem

/-! ### The compressed graph on `Fin N` -/

section Numbered

variable (S Ps)

variable {N : ℕ} (e : Fin N → Fin n) (ι : Fin n → Fin N)

open Classical in
/-- The compressed graph on `Fin N`, when `e` numbers the vertices of `cVerts`. -/
noncomputable def cGraph : MultiDigraph N where
  edgeMult i j := if CAdj S Ps (e i) (e j) then 1 else 0

/-- The blob map of the compression: the blob of `i` is the blob of `e i`, a node stands for
itself, and the two ends of a middle are the nodes around its run. -/
def cBlobMap : BlobMap N n where
  blob i := cBlob S Ps (e i)
  isNode i := decide (e i ∈ S)
  node i := e i
  ends i := (ι (cPrev S Ps (e i)), ι (cNext S Ps (e i)))

variable {e ι}

theorem cGraph_adj {i j : Fin N} :
    (cGraph S Ps e).toSimpleGraph.Adj i j ↔ CAdj S Ps (e i) (e j) := by
  classical
  simp only [MultiDigraph.toSimpleGraph_adj, cGraph]
  constructor
  · rintro ⟨-, h | h⟩
    · split_ifs at h with hc
      · exact hc
      · simp at h
    · split_ifs at h with hc
      · exact hc.symm
      · simp at h
  · intro h
    refine ⟨fun hij => h.1 (by rw [hij]), Or.inl ?_⟩
    simp [h]

/-- **The runs form a blob map.** If `e` is injective with image in `cVerts`, and `ι` is a left
inverse of `e` on `cVerts`, then `cBlobMap` is a blob map from `cGraph` to `G`. -/
theorem isBlobMap_cBlobMap {G : MultiDigraph n} (hP : IsPathSystem G S Ps)
    (he : Function.Injective e) (hev : ∀ i, e i ∈ cVerts S Ps)
    (hι : ∀ y ∈ cVerts S Ps, e (ι y) = y) :
    (cBlobMap S Ps e ι).IsBlobMap (cGraph S Ps e) G := by
  -- the run of a middle `e i`
  have hmid : ∀ i, e i ∉ S → ∃ P ∈ Ps, ∃ A a R c B, P = A ++ a :: R ++ c :: B ∧ a ∈ S ∧ c ∈ S ∧
      (∀ z ∈ R, z ∉ S) ∧ ∃ hRne : R ≠ [], R.getLast hRne = e i ∧ cBlob S Ps (e i) = R ∧
        cPrev S Ps (e i) = a ∧ cNext S Ps (e i) = c := by
    intro i hiS
    obtain ⟨hon, hrep⟩ := (mem_cVerts_iff.mp (hev i)).resolve_left hiS
    obtain ⟨P, hPs, hiP⟩ := hon
    obtain ⟨A, a, R, c, B, hdec, ha, hc, hR, hiR, hrun⟩ := hP.exists_run hPs hiP hiS
    have hRne : R ≠ [] := List.ne_nil_of_mem hiR
    refine ⟨P, hPs, A, a, R, c, B, hdec, ha, hc, hR, hRne, ?_, (hrun _ hiR).1, (hrun _ hiR).2.1,
      (hrun _ hiR).2.2⟩
    rw [← hrep]; simp only [cRep, (hrun _ hiR).1]
  have hιS : ∀ y ∈ S, e (ι y) = y := fun y hy => hι y (mem_cVerts_iff.mpr (Or.inl hy))
  refine
    { disjoint := ?_, ne_nil := ?_, nodup := ?_, walk := ?_, blob_node := ?_, ends_node := ?_,
      adj_mid := ?_, head_adj := ?_, getLast_adj := ?_, adj_node := ?_ }
  · intro u v huv y hyu hyv
    have h1 := ((hP.mem_cBlob_iff (hev u)).mp hyu).2
    have h2 := ((hP.mem_cBlob_iff (hev v)).mp hyv).2
    exact huv (he (h1.symm.trans h2))
  · intro v; exact cBlob_ne_nil S Ps (e v)
  · intro v
    by_cases hvS : e v ∈ S
    · change (cBlob S Ps (e v)).Nodup
      rw [cBlob_of_mem_S hvS]; exact List.nodup_singleton _
    · obtain ⟨P, hPs, A, a, R, c, B, hdec, -, -, -, -, -, hbl, -⟩ := hmid v hvS
      change (cBlob S Ps (e v)).Nodup
      rw [hbl]
      have hnd := hP.nodup P hPs
      rw [hdec] at hnd
      exact hnd.sublist (List.IsInfix.sublist ⟨A ++ [a], c :: B, by simp⟩)
  · intro v
    by_cases hvS : e v ∈ S
    · change IsSimpleWalkList G (cBlob S Ps (e v))
      rw [cBlob_of_mem_S hvS]; trivial
    · obtain ⟨P, hPs, A, a, R, c, B, hdec, -, -, -, -, -, hbl, -⟩ := hmid v hvS
      change IsSimpleWalkList G (cBlob S Ps (e v))
      rw [hbl]
      exact isSimpleWalkList_infix (hP.walk P hPs) ⟨A ++ [a], c :: B, by rw [hdec]; simp⟩
  · intro v hv
    have hvS : e v ∈ S := by simpa [cBlobMap] using hv
    exact cBlob_of_mem_S hvS
  · intro v hv
    have hvS : e v ∉ S := by simpa [cBlobMap] using hv
    obtain ⟨P, hPs, A, a, R, c, B, hdec, ha, hc, -, -, -, -, hpr, hnx⟩ := hmid v hvS
    simp only [cBlobMap, hpr, hnx, hιS a ha, hιS c hc, ha, hc, decide_true, true_and]
    intro hac
    have hac' : a = c := by rw [← hιS a ha, ← hιS c hc, hac]
    have hnd := hP.nodup P hPs
    rw [hdec, hac'] at hnd
    simp [List.nodup_append] at hnd
  · intro v w hv hvw
    have hvS : e v ∉ S := by simpa [cBlobMap] using hv
    obtain ⟨P, hPs, A, a, R, c, B, hdec, ha, hc, hR, hRne, hlast, hbl, hpr, hnx⟩ := hmid v hvS
    obtain ⟨hne, y, z, hyz, hy, hz⟩ := (cGraph_adj S Ps).mp hvw
    have hyb : y ∈ cBlob S Ps (e v) :=
      (hP.mem_cBlob_iff (hev v)).mpr ⟨Or.inr hyz.onPath_left, hy⟩
    rw [hbl] at hyb
    have hyS : y ∉ S := hR y hyb
    simp only [cBlobMap, hpr, hnx]
    rcases hP.cEdge_mem_run hPs hdec hyb hyS hyz with hzR | rfl | rfl
    · exfalso
      apply hne
      rw [← hy, ← hz]
      simp only [cRep]
      obtain ⟨A', a', R', c', B', -, -, -, -, -, hrun⟩ := hP.exists_run hPs
        (by rw [hdec]; simp [hyb] : y ∈ P) hyS
      have e1 := (hP.mem_cBlob_iff (hev v)).mpr ⟨Or.inr hyz.onPath_left, hy⟩
      have e2 : z ∈ cBlob S Ps (e v) := by rw [hbl]; exact hzR
      have hzv := ((hP.mem_cBlob_iff (hev v)).mp e2).2
      rw [← hy] at hzv
      exact congrArg (fun L => L) (by simpa [cRep] using hzv.symm)
    · left
      rw [cRep_of_mem_S ha] at hz
      rw [hz]; exact (he (hι _ (hev w))).symm
    · right
      rw [cRep_of_mem_S hc] at hz
      rw [hz]; exact (he (hι _ (hev w))).symm
  · intro v hv
    have hvS : e v ∉ S := by simpa [cBlobMap] using hv
    obtain ⟨P, hPs, A, a, R, c, B, hdec, ha, -, -, hRne, -, hbl, hpr, -⟩ := hmid v hvS
    simp only [cBlobMap]
    have : (cBlob S Ps (e v)).head (cBlob_ne_nil S Ps (e v)) = R.head hRne := by
      simp only [hbl]
    rw [this, hpr, hιS a ha]
    have hcon : Consec P a (R.head hRne) := by
      refine ⟨A, R.tail ++ c :: B, ?_⟩
      rw [hdec]
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hRne
      simp
    exact (IsPathSystem.CEdge.adj hP ⟨P, hPs, Or.inl hcon⟩).symm
  · intro v hv
    have hvS : e v ∉ S := by simpa [cBlobMap] using hv
    obtain ⟨P, hPs, A, a, R, c, B, hdec, -, hc, -, hRne, -, hbl, -, hnx⟩ := hmid v hvS
    simp only [cBlobMap]
    have : (cBlob S Ps (e v)).getLast (cBlob_ne_nil S Ps (e v)) = R.getLast hRne := by
      simp only [hbl]
    rw [this, hnx, hιS c hc]
    have hcon : Consec P (R.getLast hRne) c := by
      refine ⟨A ++ a :: R.dropLast, B, ?_⟩
      rw [hdec]
      conv_lhs => rw [← List.dropLast_append_getLast hRne]
      simp
    exact IsPathSystem.CEdge.adj hP ⟨P, hPs, Or.inl hcon⟩
  · intro u v hu hv huv
    have huS : e u ∈ S := by simpa [cBlobMap] using hu
    have hvS : e v ∈ S := by simpa [cBlobMap] using hv
    obtain ⟨-, y, z, hyz, hy, hz⟩ := (cGraph_adj S Ps).mp huv
    have hyS := hP.mem_S_of_cRep_mem_S hyz.onPath_left (hy ▸ huS)
    have hzS := hP.mem_S_of_cRep_mem_S hyz.onPath_right (hz ▸ hvS)
    rw [cRep_of_mem_S hyS] at hy
    rw [cRep_of_mem_S hzS] at hz
    simp only [cBlobMap]
    rw [← hy, ← hz]
    exact IsPathSystem.CEdge.adj hP hyz

end Numbered

end Alg92

end GraphMinor.Compute
