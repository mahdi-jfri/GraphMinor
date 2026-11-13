module

public import GraphMinor.Compute.GM06FindLabelExact
public import GraphMinor.Compute.GM06CandidateEdges
public import GraphMinor.Compute.GM06LoopErasure

/-!
# Recovering directed edge labels from a BFS vertex path

Sections 12--13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) return
a path with ordinary edge labels. BFS can use simple adjacency lists,
since loops never extend a simple path and parallel edges have the
same reachability effect. For consecutive returned vertices, scan
the retained permanent darts and choose the last dart with those
ordered endpoints. A positive pair key distinguishes that ordered
pair from the zero key of an excluded dart.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A positive key for an ordered pair of permanent vertex labels. -/
def gm06PairKey (n u v : ℕ) : ℕ := 1 + u * n + v

/-- Every proper ordered pair fits in a quadratic key space. -/
theorem gm06PairKey_lt {n u v : ℕ} (hu : u < n) (hv : v < n) :
    gm06PairKey n u v < 1 + n * n := by
  have hm : u * n + n ≤ n * n := by
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right n (by omega : u + 1 ≤ n)
  unfold gm06PairKey
  omega

/-- Ordered pairs have distinct keys in the bounded vertex space. -/
theorem gm06PairKey_injective {n u v x y : ℕ} (hv : v < n) (hy : y < n) (h : gm06PairKey n u v = gm06PairKey n x y) : u = x ∧ v = y := by
  have he : u * n + v = x * n + y := by unfold gm06PairKey at h; omega
  have hmod := congrArg (· % n) he
  have hvy : v = y := by
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hy] using hmod
  have hmul : u * n = x * n := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega : 0 < n) hmul, hvy⟩

/-- The key of each permanent dart, with zero for an excluded dart. -/
def gm06DartPairKeys (n : ℕ) (origins active : List ℕ) : List ℕ :=
  (List.range origins.length).map (fun d => if d ∈ active then
    gm06PairKey n (origins[d]?.getD 0) (gm06CutNeighbourHead origins d) else 0)

/-- Key positions retain the permanent dart labels. -/
theorem gm06DartPairKeys_length (n : ℕ) (origins active : List ℕ) :
    (gm06DartPairKeys n origins active).length = origins.length := by
  simp only [gm06DartPairKeys, List.length_map, List.length_range]

/-- Each key is read at exactly its permanent dart index. -/
theorem gm06DartPairKeys_get {n d : ℕ} (origins active : List ℕ) (hd : d < origins.length) :
    (gm06DartPairKeys n origins active)[d]?.getD 0 =
      if d ∈ active then gm06PairKey n (origins[d]?.getD 0) (gm06CutNeighbourHead origins d) else 0 := by
  have hi : d < (gm06DartPairKeys n origins active).length := by
    simpa only [gm06DartPairKeys_length] using hd
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.getD_some, gm06DartPairKeys, List.getElem_map, List.getElem_range]

/-- Every key fits in the quadratic pair-key space, also for loops
and for inactive permanent dart slots. -/
theorem gm06DartPairKeys_bounds {n m : ℕ} (origins active : List ℕ)
    (hlen : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n) :
    ∀ key ∈ gm06DartPairKeys n origins active, key < 1 + n * n := by
  intro key hkey
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hkey
  have hd' := List.mem_range.mp hd
  have hm : gm06DartMate d < origins.length := by
    rw [hlen]
    exact gm06DartMate_lt (hlen ▸ hd')
  have hv : origins[d]?.getD 0 < n := by
    simpa only [List.getElem?_eq_getElem hd', Option.getD_some] using hvalues _ (List.getElem_mem hd')
  have hh : gm06CutNeighbourHead origins d < n := by
    simpa only [gm06CutNeighbourHead, List.getElem?_eq_getElem hm, Option.getD_some] using
      hvalues _ (List.getElem_mem hm)
  split_ifs
  · exact gm06PairKey_lt hv hh
  · omega

/-- Select one retained directed dart for an ordered vertex pair. -/
def gm06PathDart (n : ℕ) (origins active : List ℕ) (u v : ℕ) : ℕ :=
  gm06LabelIndex (gm06DartPairKeys n origins active) (gm06PairKey n u v)

/-- Replace each consecutive vertex pair by its directed dart label. -/
def gm06PathDarts (n : ℕ) (origins active vertices : List ℕ) : List ℕ :=
  (vertices.zip vertices.tail).map (fun p => gm06PathDart n origins active p.1 p.2)

/-- When a retained dart with the required endpoints exists, the
selected dart is retained and has precisely those ordered endpoints. -/
theorem gm06PathDart_spec {n m u v : ℕ} (origins active : List ℕ)
    (hlen : origins.length = 2 * m) (hvalues : ∀ x ∈ origins, x < n)
    (_hu : u < n) (hv : v < n)
    (hex : ∃ d, d < origins.length ∧ d ∈ active ∧ origins[d]?.getD 0 = u ∧
      gm06CutNeighbourHead origins d = v) :
    let d := gm06PathDart n origins active u v
    d < origins.length ∧ d ∈ active ∧ origins[d]?.getD 0 = u ∧ gm06CutNeighbourHead origins d = v := by
  obtain ⟨d₀, hd₀, hactive, htail, hhead⟩ := hex
  have hkey : gm06PairKey n u v ∈ gm06DartPairKeys n origins active := by
    apply List.mem_iff_getElem.mpr
    have hi : d₀ < (gm06DartPairKeys n origins active).length := by simpa only [gm06DartPairKeys_length] using hd₀
    refine ⟨d₀, hi, ?_⟩
    have he := gm06DartPairKeys_get (n := n) origins active hd₀
    simpa only [List.getElem?_eq_getElem hi, Option.getD_some, hactive, ↓reduceIte, htail, hhead] using he
  let d := gm06PathDart n origins active u v
  have hfind := gm06LabelIndex_of_mem (gm06DartPairKeys n origins active) (gm06PairKey n u v) hkey
  have hd : d < origins.length := by simpa only [d, gm06PathDart, gm06DartPairKeys_length] using hfind.1
  have hpair : (if d ∈ active then gm06PairKey n (origins[d]?.getD 0)
      (gm06CutNeighbourHead origins d) else 0) = gm06PairKey n u v := by
    rw [← gm06DartPairKeys_get origins active hd]
    exact hfind.2
  have hda : d ∈ active := by
    by_contra ha
    simp only [ha, ↓reduceIte, gm06PairKey] at hpair
    omega
  simp only [hda, ↓reduceIte] at hpair
  have hmate : gm06DartMate d < origins.length := by
    rw [hlen]
    exact gm06DartMate_lt (hlen ▸ hd)
  have hhd : gm06CutNeighbourHead origins d < n := by
    simpa only [gm06CutNeighbourHead, List.getElem?_eq_getElem hmate, Option.getD_some] using
      hvalues _ (List.getElem_mem hmate)
  have he := gm06PairKey_injective hhd hv hpair
  exact ⟨hd, hda, he.1, he.2⟩

/-- Candidate adjacency supplies an actual retained directed edge with
those ordered endpoints, even when edge labels are parallel. -/
theorem gm06CandidateGraph_exists_dart {n m : ℕ} (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ) (hlen : origins.length = 2 * m)
    {u v : Fin n} (h : (gm06CandidateGraph n (gm06CandidateEnds m origins)
      ordinary incV incE upper path j).Adj u v) :
    ∃ d, d < origins.length ∧ d ∈ gm06CandidateDarts m origins ordinary incV incE upper path j ∧
      origins[d]?.getD 0 = u.val ∧ gm06CutNeighbourHead origins d = v.val := by
  obtain ⟨_, e, he, hends⟩ := h
  have hem : e < m := by
    simpa only [gm06CandidateEnds_length] using
      ((gm06CandidateEdges_mem_iff _ ordinary incV incE upper path j e).mp he).1
  have hpair := (gm06CandidateDarts_edge_iff m origins ordinary incV incE upper path j e).mpr he
  rw [gm06CandidateEnds_get origins hem] at hends
  have hmate₀ : gm06DartMate (2 * e) = 2 * e + 1 := by unfold gm06DartMate; split_ifs <;> omega
  have hmate₁ : gm06DartMate (2 * e + 1) = 2 * e := by unfold gm06DartMate; split_ifs <;> omega
  rcases hends with hends | hends
  · exact ⟨2 * e, by omega, hpair.1, congrArg Prod.fst hends,
      by simpa only [gm06CutNeighbourHead, hmate₀] using congrArg Prod.snd hends⟩
  · exact ⟨2 * e + 1, by omega, hpair.2, congrArg Prod.snd hends,
      by simpa only [gm06CutNeighbourHead, hmate₁] using congrArg Prod.fst hends⟩

/-- A vertex row with at least two vertices starts with its selected
first dart, followed by recovery on its vertex suffix. -/
theorem gm06PathDarts_cons_cons (n : ℕ) (origins active : List ℕ) (u v : ℕ) (vs : List ℕ) :
    gm06PathDarts n origins active (u :: v :: vs) =
      gm06PathDart n origins active u v :: gm06PathDarts n origins active (v :: vs) := rfl

/-- Recovery on a candidate walk preserves the complete vertex sequence
and its ends, and every selected dart is an actual retained dart. -/
theorem gm06PathDarts_candidate_walk {n m : ℕ} (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ) (hlen : origins.length = 2 * m)
    (hvalues : ∀ x ∈ origins, x < n) {u v : Fin n}
    (p : (gm06CandidateGraph n (gm06CandidateEnds m origins)
      ordinary incV incE upper path j).Walk u v) :
    let active := gm06CandidateDarts m origins ordinary incV incE upper path j
    let ds := gm06PathDarts n origins active (p.support.map Fin.val)
    GM06DartWalk (fun d => origins[d]?.getD 0) (gm06CutNeighbourHead origins) u.val ds v.val ∧
      gm06WalkVertices (gm06CutNeighbourHead origins) u.val ds = p.support.map Fin.val ∧
      ∀ d ∈ ds, d < origins.length ∧ d ∈ active := by
  let active := gm06CandidateDarts m origins ordinary incV incE upper path j
  induction p with
  | nil => exact ⟨.nil _, rfl, by simp [gm06PathDarts]⟩
  | @cons u x v h q ih =>
    have hd := gm06PathDart_spec origins active hlen hvalues u.isLt x.isLt
      (gm06CandidateGraph_exists_dart origins ordinary incV incE upper path j hlen h)
    let d := gm06PathDart n origins active u.val x.val
    have hsupport : q.support.map Fin.val = x.val :: q.support.tail.map Fin.val := by
      exact congrArg (List.map Fin.val) q.cons_tail_support.symm
    have hrow : gm06PathDarts n origins active ((SimpleGraph.Walk.cons h q).support.map Fin.val) =
        d :: gm06PathDarts n origins active (q.support.map Fin.val) := by
      rw [SimpleGraph.Walk.support_cons, List.map_cons, hsupport, gm06PathDarts_cons_cons]
    dsimp only at ih ⊢
    dsimp only [active] at hrow
    rw [hrow]
    refine ⟨.cons hd.2.2.1 (hd.2.2.2.symm ▸ ih.1), ?_, ?_⟩
    · change u.val :: (gm06CutNeighbourHead origins d ::
        (gm06PathDarts n origins active (q.support.map Fin.val)).map (gm06CutNeighbourHead origins)) =
        u.val :: q.support.map Fin.val
      rw [hd.2.2.2]
      exact congrArg (u.val :: ·) ih.2.1
    · intro dart hmem
      rcases List.mem_cons.mp hmem with he | he
      · exact he ▸ ⟨hd.1, hd.2.1⟩
      · exact ih.2.2 dart he

/-- A simple BFS vertex path recovers a simple directed edge path. -/
theorem gm06PathDarts_candidate_nodup {n m : ℕ} (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ) (hlen : origins.length = 2 * m)
    (hvalues : ∀ x ∈ origins, x < n) {u v : Fin n}
    (p : (gm06CandidateGraph n (gm06CandidateEnds m origins)
      ordinary incV incE upper path j).Walk u v) (hp : p.IsPath) :
    (gm06WalkVertices (gm06CutNeighbourHead origins) u.val
      (gm06PathDarts n origins (gm06CandidateDarts m origins ordinary incV incE upper path j)
        (p.support.map Fin.val))).Nodup := by
  rw [(gm06PathDarts_candidate_walk origins ordinary incV incE upper path j hlen hvalues p).2.1]
  exact hp.support_nodup.map Fin.val_injective

end GraphMinor.Compute
