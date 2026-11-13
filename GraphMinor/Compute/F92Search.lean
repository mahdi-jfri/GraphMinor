module

public import GraphMinor.Compute.Algorithm92F
public import GraphMinor.Compute.TwoPathsSearchWalk
import GraphMinor.Compute.Algorithm92Route

/-!
# Search labels for the subwall paths

For one subwall, start a breadth-first search from all its inside vertices. Vertices outside
the main wall are free, vertices of the main wall outside the subwall are targets, and the
remaining wall vertices are forbidden. The search initializes all sources before scanning
edges, so its parent paths have no other source on them. These labels therefore prevent
wall vertices from occurring inside the returned path.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

open SimpleGraph WallOfHeight

/-- Labels for the search from the inside of a subwall: free vertices have label zero,
forbidden vertices have label two, and targets have label three. -/
def f92SearchLabel {n h hs : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (S : WallOfHeight hs G) (v : Fin n) : ℕ :=
  if v ∈ S.insideFinset then 0
  else if v ∈ W.vertexFinset then
    if v ∈ S.vertexFinset then 2 else 3
  else 0

/-- The free vertices are exactly the sources and the vertices outside the main wall. -/
theorem f92SearchLabel_zero {n h hs : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (S : WallOfHeight hs G) (v : Fin n) :
    f92SearchLabel W S v = 0 ↔ v ∈ S.insideFinset ∨ v ∉ W.vertexFinset := by
  classical
  unfold f92SearchLabel
  split_ifs <;> simp_all

/-- A target is exactly a vertex of the main wall outside the subwall. -/
theorem f92SearchLabel_three {n h hs : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (S : WallOfHeight hs G) (v : Fin n) :
    f92SearchLabel W S v = 3 ↔ v ∈ W.vertexFinset \ S.vertexFinset := by
  classical
  have hin : v ∈ S.insideFinset → v ∈ S.vertexFinset := fun hv => (Finset.mem_sdiff.mp hv).1
  unfold f92SearchLabel
  split_ifs <;> simp_all

/-- Every search label is a valid label for `TwoPaths.searchProg`. -/
theorem f92SearchLabel_le {n h hs : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (S : WallOfHeight hs G) (v : Fin n) :
    f92SearchLabel W S v ≤ 3 := by
  classical
  unfold f92SearchLabel
  split_ifs <;> omega

/-- A closed search cannot miss a target at the end of a walk whose preceding vertices are
free. This is the completeness step used with a non-dividing subwall's witness path. -/
theorem search_hit_of_walkList {n : ℕ} {G : MultiDigraph n}
    {L0 : Fin n → ℕ} {src : List ℕ} {s₀ s : State} {items : List ℕ}
    (hs : TwoPaths.SInv G.toSimpleGraph L0 src s₀ items items.length s)
    (hmiss : s.regs TwoPaths.rHit = n) :
    ∀ (L : List (Fin n)) (hne : L ≠ []), IsSimpleWalkList G L →
      (L.head hne).val ∈ items → L0 (L.getLast hne) = 3 →
      (∀ v ∈ L.dropLast, L0 v = 0) → False
  | [], hne, _, _, _, _ => (hne rfl).elim
  | [v], _, _, hv, ht, _ => by
    have hf := hs.free v hv
    simp only [List.getLast_singleton] at ht
    omega
  | u :: v :: rest, _, hw, hu, ht, hf => by
    cases rest with
    | nil =>
      have hnot := hs.noHit hmiss hu hw.1
      exact hnot ht
    | cons z rest =>
      have hvfree : L0 v = 0 := hf v (by simp)
      have hv : v.val ∈ items := by
        rcases hs.closed u (by simpa using hu) v hw.1 with h | h
        · exact (h hvfree).elim
        · exact h
      exact search_hit_of_walkList hs hmiss (v :: z :: rest) (by simp) hw.2 hv ht
        (fun y hy => hf y (by rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hy))

/-- A non-dividing subwall's witness path forces the search to find a target. The only
search hypothesis is its proved invariant after the queue has been exhausted. -/
theorem f92Search_hit {n h hs : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} {S : WallOfHeight hs G}
    {src : List ℕ} {s₀ s : State} {items : List ℕ}
    (hinv : TwoPaths.SInv G.toSimpleGraph (f92SearchLabel W S) src s₀ items items.length s)
    (hsrc : ∀ v : Fin n, v.val ∈ src ↔ v ∈ S.insideFinset)
    {P : List (Fin n)} (hP : IsSubwallHPath W S P) :
    s.regs TwoPaths.rHit ≠ n := by
  obtain ⟨⟨hne, h2, hnd, hw, hh, hl, hinner, _⟩, hstart, hend⟩ := hP
  have hstart' : P.head hne ∈ S.insideFinset :=
    hstart _ (List.head?_eq_some_head hne)
  have hend' : P.getLast hne ∈ W.vertexFinset \ S.vertexFinset :=
    hend _ (List.getLast?_eq_some_getLast hne)
  have hroot : (P.head hne).val ∈ items :=
    hinv.srcs _ ((hsrc _).mpr hstart') ((f92SearchLabel_zero W S _).mpr (Or.inl hstart'))
  have hendlabel : f92SearchLabel W S (P.getLast hne) = 3 :=
    (f92SearchLabel_three W S _).mpr hend'
  have hwall := (not_mem_drop_one_dropLast_iff hne h2 hnd W.vertexFinset hh hl).mp hinner
  have hnotlast : P.getLast hne ∉ P.dropLast := by
    have hnd' : (P.dropLast ++ [P.getLast hne]).Nodup := by
      rw [List.dropLast_concat_getLast hne]
      exact hnd
    exact fun hv => (List.nodup_append.mp hnd').2.2 _ hv _ (by simp) rfl
  intro hmiss
  apply search_hit_of_walkList hinv hmiss P hne hw hroot hendlabel
  intro v hv
  apply (f92SearchLabel_zero W S v).mpr
  by_cases hvW : v ∈ W.vertexFinset
  · obtain hvhead | hvlast := hwall v (List.mem_of_mem_dropLast hv) hvW
    · exact Or.inl (hvhead ▸ hstart')
    · exact (hnotlast (hvlast ▸ hv)).elim
  · exact Or.inr hvW

private theorem walk_support_isSimpleWalkList {n : ℕ} {G : MultiDigraph n}
    {u v : Fin n} (q : G.toSimpleGraph.Walk u v) : IsSimpleWalkList G q.support := by
  induction q with
  | nil => trivial
  | @cons u z v hadj q ih =>
    cases q with
    | nil => exact ⟨hadj, trivial⟩
    | cons _ _ => exact ⟨hadj, ih⟩

/-- A path between the prescribed endpoint sets, with no other wall vertices, is an
`H`-path. A single edge between these endpoint sets cannot be a wall edge. -/
theorem f92_isSubwallHPath_of_walk {n h hs : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} {S : WallOfHeight hs G}
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) (hsub : S.IsSubwallOf W)
    {u v : Fin n} (q : G.toSimpleGraph.Walk u v) (hq : q.IsPath)
    (hu : u ∈ S.insideFinset) (hv : v ∈ W.vertexFinset \ S.vertexFinset)
    (hinner : ∀ y ∈ q.support, y ∈ W.vertexFinset → y = u ∨ y = v) :
    IsSubwallHPath W S q.support := by
  have hne := q.support_ne_nil
  have hhead : q.support.head hne = u := q.head_support
  have hlast : q.support.getLast hne = v := q.getLast_support
  have huv : u ≠ v := fun huv =>
    (Finset.mem_sdiff.mp hv).2 (huv ▸ (Finset.mem_sdiff.mp hu).1)
  have hlen : 2 ≤ q.support.length :=
    two_le_length_of_ne_head_getLast hne (by rw [hhead, hlast]; exact huv)
  have huW : u ∈ W.vertexFinset :=
    W.subwall_vertexFinset_subset hsub (Finset.mem_sdiff.mp hu).1
  have hvW := (Finset.mem_sdiff.mp hv).1
  refine ⟨⟨hne, hlen, hq.support_nodup, walk_support_isSimpleWalkList q,
    by rwa [hhead], by rwa [hlast], ?_, ?_⟩, ?_, ?_⟩
  · apply (not_mem_drop_one_dropLast_iff hne hlen hq.support_nodup W.vertexFinset
      (by rwa [hhead]) (by rwa [hlast])).mpr
    simpa only [hhead, hlast] using hinner
  · intro _
    rw [hhead, hlast]
    exact W.not_isWallEdge_inside_to_outside h2 he hW hsub hu hv
  · intro y hy
    rw [List.head?_eq_some_head hne, hhead, Option.some.injEq] at hy
    exact hy ▸ hu
  · intro y hy
    rw [List.getLast?_eq_some_getLast hne, hlast, Option.some.injEq] at hy
    exact hy ▸ hv

/-- The parent path of a successful search, followed by the edge to its target, is the
subwall's required `H`-path. This uses only the search invariant and the actual wall data. -/
theorem f92Search_path {n h hs : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} {S : WallOfHeight hs G}
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) (hsub : S.IsSubwallOf W)
    {src : List ℕ} {s₀ s : State} {items : List ℕ}
    (hinv : TwoPaths.SInv G.toSimpleGraph (f92SearchLabel W S) src s₀ items items.length s)
    (hsrc : ∀ v : Fin n, v.val ∈ src ↔ v ∈ S.insideFinset)
    (hhit : s.regs TwoPaths.rHit ≠ n) :
    ∃ (u v : Fin n) (q : G.toSimpleGraph.Walk u v),
      IsSubwallHPath W S q.support ∧ s.regs TwoPaths.rHit = v.val := by
  obtain ⟨v, z, hv, _, hvlabel, hz, hadj⟩ := hinv.hit_of_ne hhit
  obtain ⟨par, _, hpar⟩ := hinv.par
  obtain ⟨u, q, hq, hu, hsupp, hns, _⟩ :=
    TwoPaths.exists_walk_of_parentOK hpar (items.idxOf z.val + 1) z hz (by omega)
  have htarget : v ∈ W.vertexFinset \ S.vertexFinset :=
    (f92SearchLabel_three W S v).mp hvlabel
  have hvnot : v ∉ q.support := by
    intro hmem
    have hf := hinv.free v (hsupp v hmem).1
    omega
  refine ⟨u, v, q.concat hadj,
    f92_isSubwallHPath_of_walk h2 he hW hsub _ (hq.concat hvnot hadj)
      ((hsrc u).mp hu) htarget ?_, hv⟩
  intro y hy hyW
  rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | rfl
  · left
    by_contra hyu
    have hfree := (f92SearchLabel_zero W S y).mp (hinv.free y (hsupp y hy).1)
    rcases hfree with hyS | hyout
    · exact hns y hy hyu ((hsrc y).mpr hyS)
    · exact hyout hyW
  · exact Or.inr rfl

/-- Run the existing breadth-first search with the labels for an input subwall.
Non-dividing supplies its witness, so the returned state contains a target and parent paths
that give an `H`-path. The source and label arrays are inputs here. -/
theorem f92SearchProg_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (a : Fin k)
    (lists : Fin x.n → List ℕ) (gS gE gEnt : Arr)
    (hgS : gS < 60) (hgE : gE < 60) (hgEnt : gEnt < 60)
    (src : List ℕ) (hsrc : ∀ v : Fin x.n, v.val ∈ src ↔ v ∈ (x.W_sub a).insideFinset)
    (hsrcLt : ∀ v ∈ src, v < x.n) (s : State)
    (hadj : IsAdjList x.G.toSimpleGraph gS gE gEnt lists s)
    (hent : (s.arrs gEnt).length < 2 ^ w) (hrn : s.regs 40 = x.n)
    (hw : 4 < 2 ^ w) (hn : x.n < 2 ^ w) (hlen : src.length < 2 ^ w)
    (hlab : s.arrs TwoPaths.aLab = List.ofFn (f92SearchLabel x.W (x.W_sub a)))
    (hsrcArr : s.arrs TwoPaths.aSrc = src) :
    ∃ s' t items, Exec w (TwoPaths.searchProg gS gE gEnt) s s' t ∧
      t ≤ 16 + 21 * x.n + 29 * src.length + 29 * totalAdjEntries lists ∧
      TwoPaths.SInv x.G.toSimpleGraph (f92SearchLabel x.W (x.W_sub a)) src s
        items items.length s' ∧
      s'.regs TwoPaths.rHit ≠ x.n ∧
      ∃ (u v : Fin x.n) (q : x.G.toSimpleGraph.Walk u v),
        IsSubwallHPath x.W (x.W_sub a) q.support ∧ s'.regs TwoPaths.rHit = v.val := by
  obtain ⟨s', t, items, hex, ht, hinv⟩ :=
    TwoPaths.searchProg_exec x.G.toSimpleGraph lists gS gE gEnt hgS hgE hgEnt
      (f92SearchLabel x.W (x.W_sub a)) (f92SearchLabel_le x.W (x.W_sub a)) src
      hsrcLt s hadj hent hrn hw hn hlen hlab hsrcArr
  obtain ⟨P, hP⟩ := exists_isSubwallHPath x a
  have hhit := f92Search_hit hinv hsrc hP
  exact ⟨s', t, items, hex, ht, hinv, hhit,
    f92Search_path x.hW_valid.1 x.hW_valid.2.1 x.hW_valid.2.2
      (x.hnondiv a).1 hinv hsrc hhit⟩

end GraphMinor.Compute.Alg92
