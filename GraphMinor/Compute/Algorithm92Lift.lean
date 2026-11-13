module

public import GraphMinor.Compute.Specs9
import GraphMinor.Compute.Algorithm72Wall

/-!
# Graph Minors XIII, (9.2): lifting an output from a compressed input (`Algorithm92Lift.lean`)

The algorithm of (9.2) (page 101) first finds a subgraph `F`, and then "since the size of $F$ is
bounded (exept for divalent vertices) by a function of $l, m$, and $p$, we can find an
$(l, m)$-star or a model of $K_p$ in $H \cup F$ in time $\le C\varepsilon(G)$". We do this search
on a compressed copy of `H ∪ F`: a graph `GK` on `Fin N` in which every long path of `H ∪ F`
whose inner vertices have valency `2` is replaced by a path of length `2`. This file proves that
an answer found in the compressed copy gives an answer in `G`.

The link between the two graphs is a `BlobMap`. Each vertex `v` of `GK` has a *blob*, a path of
`G`. A *node* `v` stands for one vertex `node v` of `G`, and its blob is `[node v]`. Every other
vertex `v` of `GK` is a *middle*: it has exactly two neighbours `ends v`, which are nodes, and its
blob is the inner path of the segment of `H ∪ F` that it replaces. The conditions are collected in
`IsBlobMap`.

* `isCliqueModel_liftSets`: the union of the blobs of the branch sets of a model of `K_p` in `GK`
  is a model of `K_p` in `G`. This is the usual fact that a model of a graph in a minor of `G`
  gives a model in `G`: the blobs form a model of `GK` in `G`.
* `isStarRay_liftRay`: the rays of an `(l, m)`-star of the wall `WK` of `GK` give the rays of an
  `(l, m)`-star of the wall `W` of `G`, when the blob map also respects the walls
  (`IsWallBlobMap`). Each ray is lifted by replacing every middle by its blob, turned the right
  way (`liftRay`). The center is a node, since a middle has only two neighbours and the star has at
  least three rays; and the last vertex of each ray is a node, since the edges at a middle of the
  wall are edges of the wall.
* `exists_isAlg92Output_of_blobMap`: so a correct output of the compressed input gives a correct
  output of the input.
-/

public section

namespace GraphMinor.Compute

namespace Alg92

/-- The data that links a compressed graph `GK` on `Fin N` with a graph `G` on `Fin n`: for each
vertex `v` of `GK`, its blob `blob v` (a path of `G`), whether it is a node (`isNode v`), the vertex
`node v` of `G` that a node stands for, and the two neighbours `ends v` of a middle. -/
structure BlobMap (N n : ℕ) where
  /-- The blob of a vertex of `GK`: a path of `G`. -/
  blob : Fin N → List (Fin n)
  /-- Whether a vertex of `GK` is a node. -/
  isNode : Fin N → Bool
  /-- The vertex of `G` that a node stands for. -/
  node : Fin N → Fin n
  /-- The two neighbours of a middle. -/
  ends : Fin N → Fin N × Fin N

namespace BlobMap

variable {N n : ℕ}

/-- The side conditions of a blob map from `GK` to `G`:
- the blobs are mutually disjoint, every blob is a nonempty path of `G`, and the blob of a node `v`
  is `[node v]`;
- a middle `v` has exactly the two neighbours `ends v`, which are distinct nodes, the first vertex
  of `blob v` is adjacent to the vertex of the first end, and the last vertex of `blob v` is adjacent
  to the vertex of the second end;
- two adjacent nodes stand for adjacent vertices. -/
structure IsBlobMap (B : BlobMap N n) (GK : MultiDigraph N) (G : MultiDigraph n) : Prop where
  disjoint : ∀ u v : Fin N, u ≠ v → ∀ y, y ∈ B.blob u → y ∉ B.blob v
  ne_nil : ∀ v, B.blob v ≠ []
  nodup : ∀ v, (B.blob v).Nodup
  walk : ∀ v, WallOfHeight.IsSimpleWalkList G (B.blob v)
  blob_node : ∀ v, B.isNode v = true → B.blob v = [B.node v]
  ends_node : ∀ v, B.isNode v = false →
    B.isNode (B.ends v).1 = true ∧ B.isNode (B.ends v).2 = true ∧ (B.ends v).1 ≠ (B.ends v).2
  adj_mid : ∀ v w, B.isNode v = false → GK.toSimpleGraph.Adj v w →
    w = (B.ends v).1 ∨ w = (B.ends v).2
  head_adj : ∀ v (_hv : B.isNode v = false),
    G.toSimpleGraph.Adj ((B.blob v).head (ne_nil v)) (B.node (B.ends v).1)
  getLast_adj : ∀ v (_hv : B.isNode v = false),
    G.toSimpleGraph.Adj ((B.blob v).getLast (ne_nil v)) (B.node (B.ends v).2)
  adj_node : ∀ u v, B.isNode u = true → B.isNode v = true → GK.toSimpleGraph.Adj u v →
    G.toSimpleGraph.Adj (B.node u) (B.node v)

variable {B : BlobMap N n} {GK : MultiDigraph N} {G : MultiDigraph n}

/-- The blobs of two adjacent vertices of `GK` contain two adjacent vertices of `G`. -/
theorem IsBlobMap.exists_adj (hB : B.IsBlobMap GK G) {u v : Fin N}
    (huv : GK.toSimpleGraph.Adj u v) :
    ∃ a ∈ B.blob u, ∃ b ∈ B.blob v, G.toSimpleGraph.Adj a b := by
  cases hu : B.isNode u <;> cases hv : B.isNode v
  · rcases hB.adj_mid u v hu huv with rfl | rfl
    · exact absurd (hB.ends_node u hu).1 (by rw [hv]; decide)
    · exact absurd (hB.ends_node u hu).2.1 (by rw [hv]; decide)
  · rw [hB.blob_node v hv]
    rcases hB.adj_mid u v hu huv with rfl | rfl
    · exact ⟨_, List.head_mem _, _, List.mem_singleton_self _, hB.head_adj u hu⟩
    · exact ⟨_, List.getLast_mem _, _, List.mem_singleton_self _, hB.getLast_adj u hu⟩
  · rw [hB.blob_node u hu]
    rcases hB.adj_mid v u hv huv.symm with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, _, List.head_mem _, (hB.head_adj v hv).symm⟩
    · exact ⟨_, List.mem_singleton_self _, _, List.getLast_mem _, (hB.getLast_adj v hv).symm⟩
  · rw [hB.blob_node u hu, hB.blob_node v hv]
    exact ⟨_, List.mem_singleton_self _, _, List.mem_singleton_self _, hB.adj_node u v hu hv huv⟩

/-- The vertices of `G` in the blobs of the vertices in `S`. -/
@[expose] def liftSet (B : BlobMap N n) (S : Finset (Fin N)) : Finset (Fin n) :=
  S.biUnion fun v => (B.blob v).toFinset

theorem mem_liftSet {S : Finset (Fin N)} {y : Fin n} :
    y ∈ B.liftSet S ↔ ∃ v ∈ S, y ∈ B.blob v := by
  simp [liftSet]

/-- Two vertices of a path of `G` that lies in `T` are joined in the graph of `G` induced on `T`. -/
private theorem reachable_of_walkList {T : Finset (Fin n)} :
    ∀ {L : List (Fin n)}, WallOfHeight.IsSimpleWalkList G L → ∀ (hT : ∀ y ∈ L, y ∈ T),
      ∀ a (ha : a ∈ L) b (hb : b ∈ L),
        (G.toSimpleGraph.induce (T : Set (Fin n))).Reachable ⟨a, hT a ha⟩ ⟨b, hT b hb⟩
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | [x], _, hT, a, ha, b, hb => by
    rw [List.mem_singleton] at ha hb
    subst ha hb
    rfl
  | x :: y :: rest, ⟨hxy, hrest⟩, hT, a, ha, b, hb => by
    have hT' : ∀ z ∈ y :: rest, z ∈ T := fun z hz => hT z (List.mem_cons_of_mem _ hz)
    have hy : y ∈ y :: rest := List.mem_cons_self ..
    have key : ∀ c (hc : c ∈ x :: y :: rest),
        (G.toSimpleGraph.induce (T : Set (Fin n))).Reachable ⟨c, hT c hc⟩ ⟨y, hT y
          (List.mem_cons_of_mem _ hy)⟩ := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact SimpleGraph.Adj.reachable (G := G.toSimpleGraph.induce (T : Set (Fin n)))
          (u := ⟨c, hT c hc⟩) (v := ⟨y, _⟩) hxy
      · exact reachable_of_walkList hrest hT' c hc' y hy
    exact (key a ha).trans (key b hb).symm

/-- **Lifting a model of `K_p`.** If `K` is a model of `K_p` in `GK`, then the unions of the blobs
of its branch sets form a model of `K_p` in `G`. -/
theorem isCliqueModel_liftSets (hB : B.IsBlobMap GK G) {p : ℕ} {K : Fin p → Finset (Fin N)}
    (hK : IsCliqueModel GK.toSimpleGraph p K) :
    IsCliqueModel G.toSimpleGraph p (fun i => B.liftSet (K i)) := by
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_, fun i j hij => ?_⟩
  · obtain ⟨v, hv⟩ := (hK.1 i).1
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (hB.ne_nil v)
    exact ⟨y, mem_liftSet.mpr ⟨v, hv, hy⟩⟩
  · set T := B.liftSet (K i)
    have hsub : ∀ v ∈ K i, ∀ y ∈ B.blob v, y ∈ T := fun v hv y hy => mem_liftSet.mpr ⟨v, hv, hy⟩
    -- Any two vertices in the blobs of two vertices of `K i` are joined in `G[T]`.
    have hR : ∀ x y : (K i : Set (Fin N)),
        (GK.toSimpleGraph.induce (K i : Set (Fin N))).Reachable x y →
        ∀ a (ha : a ∈ B.blob x.1) b (hb : b ∈ B.blob y.1),
          (G.toSimpleGraph.induce (T : Set (Fin n))).Reachable ⟨a, hsub x.1 x.2 a ha⟩
            ⟨b, hsub y.1 y.2 b hb⟩ := by
      intro x y ⟨w⟩
      induction w with
      | @nil u =>
        intro a ha b hb
        exact reachable_of_walkList (hB.walk _) (hsub u.1 u.2) a ha b hb
      | @cons x y z hxy rest ih =>
        intro a ha b hb
        obtain ⟨c, hc, d, hd, hcd⟩ := hB.exists_adj hxy
        have h1 := reachable_of_walkList (T := T) (hB.walk x.1) (hsub _ x.2) a ha c hc
        have h2 : (G.toSimpleGraph.induce (T : Set (Fin n))).Reachable
            ⟨c, hsub _ x.2 c hc⟩ ⟨d, hsub _ y.2 d hd⟩ :=
          SimpleGraph.Adj.reachable (G := G.toSimpleGraph.induce (T : Set (Fin n))) hcd
        exact h1.trans (h2.trans (ih d hd b hb))
    rw [SimpleGraph.connected_iff]
    obtain ⟨v₀, hv₀⟩ := (hK.1 i).1
    obtain ⟨y₀, hy₀⟩ := List.exists_mem_of_ne_nil _ (hB.ne_nil v₀)
    refine ⟨fun a b => ?_, ⟨⟨y₀, hsub v₀ hv₀ y₀ hy₀⟩⟩⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨u, hu, hau⟩ := mem_liftSet.mp ha
    obtain ⟨v, hv, hbv⟩ := mem_liftSet.mp hb
    exact hR ⟨u, hu⟩ ⟨v, hv⟩ ((hK.1 i).2.preconnected ⟨u, hu⟩ ⟨v, hv⟩) a hau b hbv
  · rw [Finset.disjoint_left]
    intro y hyi hyj
    obtain ⟨u, hu, hyu⟩ := mem_liftSet.mp hyi
    obtain ⟨v, hv, hyv⟩ := mem_liftSet.mp hyj
    have huv : u ≠ v := fun h => Finset.disjoint_left.mp (hK.2.1 i j hij) hu (h ▸ hv)
    exact hB.disjoint u v huv y hyu hyv
  · obtain ⟨u, hu, v, hv, huv⟩ := hK.2.2 i j hij
    obtain ⟨a, ha, b, hb, hab⟩ := hB.exists_adj huv
    exact ⟨a, mem_liftSet.mpr ⟨u, hu, ha⟩, b, mem_liftSet.mpr ⟨v, hv, hb⟩, hab⟩

/-! ### Lifting the rays of a star -/

/-- The side conditions that link the wall `WK` of `GK` with the wall `W` of `G`:
- the blob of a vertex outside `WK` has no vertex of `W`, and a node of `WK` stands for a vertex
  of `W`;
- if two nodes stand for the ends of an edge of `W`, they are the ends of an edge of `WK`;
- every edge at a middle of `WK` is an edge of `WK`;
- the distance in `WK` of two nodes of `WK` is at most the distance in `W` of their vertices. -/
structure IsWallBlobMap {h : ℕ} (B : BlobMap N n) (WK : WallOfHeight h GK)
    (W : WallOfHeight h G) : Prop where
  blob_not_mem : ∀ v, v ∉ WK.vertexFinset → ∀ y ∈ B.blob v, y ∉ W.vertexFinset
  node_mem : ∀ v, B.isNode v = true → v ∈ WK.vertexFinset → B.node v ∈ W.vertexFinset
  isWallEdge : ∀ u v, B.isNode u = true → B.isNode v = true →
    W.IsWallEdge (B.node u) (B.node v) → WK.IsWallEdge u v
  isWallEdge_mid : ∀ v w, B.isNode v = false → v ∈ WK.vertexFinset →
    GK.toSimpleGraph.Adj v w → WK.IsWallEdge v w
  brickDist_le : ∀ u v, B.isNode u = true → B.isNode v = true → u ∈ WK.vertexFinset →
    v ∈ WK.vertexFinset → WK.brickDist u v ≤ W.brickDist (B.node u) (B.node v)

/-- The blob of `v`, turned so that it starts next to `prev`: the blob of a node, or the blob of a
middle read from its end `prev`. -/
@[expose] def piece (B : BlobMap N n) (prev v : Fin N) : List (Fin n) :=
  if B.isNode v then [B.node v]
  else if prev = (B.ends v).1 then B.blob v else (B.blob v).reverse

/-- The lift of the part `L` of a path of `GK` that follows the vertex `prev`. -/
@[expose] def liftTail (B : BlobMap N n) : Fin N → List (Fin N) → List (Fin n)
  | _, [] => []
  | prev, v :: rest => B.piece prev v ++ B.liftTail v rest

/-- The lift of a path of `GK` that starts at a node: every vertex is replaced by its piece. -/
@[expose] def liftRay (B : BlobMap N n) : List (Fin N) → List (Fin n)
  | [] => []
  | c :: rest => B.node c :: B.liftTail c rest

theorem mem_piece (hB : B.IsBlobMap GK G) {prev v : Fin N} {y : Fin n} :
    y ∈ B.piece prev v ↔ y ∈ B.blob v := by
  unfold piece
  cases hv : B.isNode v
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> simp
  · simp [hB.blob_node v hv]

theorem piece_ne_nil (hB : B.IsBlobMap GK G) (prev v : Fin N) : B.piece prev v ≠ [] := by
  unfold piece
  split_ifs
  · simp
  · exact hB.ne_nil v
  · simpa using hB.ne_nil v

theorem nodup_piece (hB : B.IsBlobMap GK G) (prev v : Fin N) : (B.piece prev v).Nodup := by
  unfold piece
  split_ifs
  · simp
  · exact hB.nodup v
  · exact List.nodup_reverse.mpr (hB.nodup v)

theorem mem_liftTail (hB : B.IsBlobMap GK G) :
    ∀ (prev : Fin N) (L : List (Fin N)) (y : Fin n),
      y ∈ B.liftTail prev L ↔ ∃ v ∈ L, y ∈ B.blob v
  | _, [], _ => by simp [liftTail]
  | prev, v :: rest, y => by
    simp only [liftTail, List.mem_append, mem_piece hB, mem_liftTail hB v rest y, List.mem_cons]
    constructor
    · rintro (h | ⟨w, hw, hy⟩)
      · exact ⟨v, Or.inl rfl, h⟩
      · exact ⟨w, Or.inr hw, hy⟩
    · rintro ⟨w, rfl | hw, hy⟩
      · exact Or.inl hy
      · exact Or.inr ⟨w, hw, hy⟩

theorem nodup_liftTail (hB : B.IsBlobMap GK G) :
    ∀ (prev : Fin N) (L : List (Fin N)), L.Nodup → (B.liftTail prev L).Nodup
  | _, [], _ => by simp [liftTail]
  | prev, v :: rest, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [liftTail]
    refine List.nodup_append.mpr ⟨nodup_piece hB prev v, nodup_liftTail hB v rest hnd.2, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨w, hw, haw⟩ := (mem_liftTail hB v rest a).mp hb
    exact hB.disjoint v w (fun h => hnd.1 (h ▸ hw)) a ((mem_piece hB).mp ha) haw

theorem liftTail_ne_nil (hB : B.IsBlobMap GK G) (prev : Fin N) {L : List (Fin N)}
    (hL : L ≠ []) : B.liftTail prev L ≠ [] := by
  rcases L with _ | ⟨v, rest⟩
  · exact absurd rfl hL
  · simp only [liftTail]
    exact List.append_ne_nil_of_left_ne_nil (piece_ne_nil hB prev v) _

/-- A middle that follows `prev` on a path of `GK` and is followed by `w` has the ends `prev` and
`w`, in some order. -/
theorem ends_of_mid (hB : B.IsBlobMap GK G) {prev v w : Fin N} (hv : B.isNode v = false)
    (h1 : GK.toSimpleGraph.Adj prev v) (h2 : GK.toSimpleGraph.Adj v w) (hne : prev ≠ w) :
    (prev = (B.ends v).1 ∧ w = (B.ends v).2) ∨ (prev = (B.ends v).2 ∧ w = (B.ends v).1) := by
  rcases hB.adj_mid v prev hv h1.symm with hp | hp <;>
    rcases hB.adj_mid v w hv h2 with hw | hw
  · exact absurd (hp.trans hw.symm) hne
  · exact Or.inl ⟨hp, hw⟩
  · exact Or.inr ⟨hp, hw⟩
  · exact absurd (hp.trans hw.symm) hne

/-- The piece of a middle `v` between `prev` and `w`: it is a path whose first vertex is adjacent
to the vertex of `prev` and whose last vertex is adjacent to the vertex of `w`. -/
theorem piece_mid (hB : B.IsBlobMap GK G) {prev v w : Fin N} (hv : B.isNode v = false)
    (hends : (prev = (B.ends v).1 ∧ w = (B.ends v).2) ∨ (prev = (B.ends v).2 ∧ w = (B.ends v).1)) :
    WallOfHeight.IsSimpleWalkList G (B.piece prev v) ∧
      G.toSimpleGraph.Adj (B.node prev) ((B.piece prev v).head (piece_ne_nil hB prev v)) ∧
      G.toSimpleGraph.Adj ((B.piece prev v).getLast (piece_ne_nil hB prev v)) (B.node w) := by
  have hne12 := (hB.ends_node v hv).2.2
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hp : B.piece (B.ends v).1 v = B.blob v := by simp [piece, hv]
    simp only [hp]
    exact ⟨hB.walk v, (hB.head_adj v hv).symm, hB.getLast_adj v hv⟩
  · have hp : B.piece (B.ends v).2 v = (B.blob v).reverse := by
      simp [piece, hv, Ne.symm hne12]
    simp only [hp, List.head_reverse, List.getLast_reverse]
    exact ⟨(isSimpleWalkList_reverse_iff _).mpr (hB.walk v), (hB.getLast_adj v hv).symm,
      hB.head_adj v hv⟩

/-- The lift of a path of `GK` that starts at a node and ends at a node is a path of `G`. -/
theorem isSimpleWalkList_liftTail (hB : B.IsBlobMap GK G) :
    ∀ (prev : Fin N) (L : List (Fin N)), B.isNode prev = true →
      WallOfHeight.IsSimpleWalkList GK (prev :: L) → (prev :: L).Nodup →
      (∀ hL : L ≠ [], B.isNode (L.getLast hL) = true) →
      WallOfHeight.IsSimpleWalkList G (B.node prev :: B.liftTail prev L)
  | _, [], _, _, _, _ => by simp [liftTail, WallOfHeight.IsSimpleWalkList]
  | prev, [v], hprev, hw, _, hlast => by
    have hv : B.isNode v = true := hlast (by simp)
    simp only [liftTail, piece, hv, ↓reduceIte, List.append_nil]
    exact ⟨hB.adj_node prev v hprev hv hw.1, trivial⟩
  | prev, v :: w :: rest, hprev, hw, hnd, hlast => by
    have hlast' : ∀ hL : w :: rest ≠ [], B.isNode ((w :: rest).getLast hL) = true :=
      fun hL => by simpa using hlast (by simp)
    have hnd' : (v :: w :: rest).Nodup := (List.nodup_cons.mp hnd).2
    cases hv : B.isNode v
    · -- `v` is a middle, between `prev` and `w`.
      have hpw : prev ≠ w := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
      have hends := ends_of_mid hB hv hw.1 hw.2.1 hpw
      have hwn : B.isNode w = true := by
        rcases hends with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact (hB.ends_node v hv).2.1
        · exact (hB.ends_node v hv).1
      obtain ⟨hpw', hph, hpl⟩ := piece_mid hB hv hends
      have ih := isSimpleWalkList_liftTail hB w rest hwn hw.2.2
        (List.nodup_cons.mp hnd').2 (fun hL => by
          have := hlast (by simp)
          rwa [List.getLast_cons (by simp), List.getLast_cons hL] at this)
      have hwpiece : B.piece v w = [B.node w] := by simp [piece, hwn]
      simp only [liftTail, hwpiece, List.singleton_append]
      have h1 := isSimpleWalkList_append_of_adj (B.piece prev v) (B.node w :: B.liftTail w rest)
        (piece_ne_nil hB prev v) (by simp) hpw' ih (by simpa using hpl)
      have h2 := isSimpleWalkList_append_of_adj [B.node prev]
        (B.piece prev v ++ B.node w :: B.liftTail w rest) (by simp)
        (List.append_ne_nil_of_left_ne_nil (piece_ne_nil hB prev v) _) trivial h1
        (by
          rw [List.getLast_singleton, List.head_append_of_ne_nil (piece_ne_nil hB prev v)]
          exact hph)
      simpa using h2
    · -- `v` is a node.
      have ih := isSimpleWalkList_liftTail hB v (w :: rest) hv hw.2 hnd' hlast'
      have hvpiece : B.piece prev v = [B.node v] := by simp [piece, hv]
      simp only [liftTail, hvpiece, List.singleton_append] at ih ⊢
      exact ⟨hB.adj_node prev v hprev hv hw.1, ih⟩

/-- A pair of consecutive entries of `x :: Q` is `(x, Q.head)` or is consecutive in `Q`. -/
private theorem mem_zip_cons_self {α : Type*} {a b x : α} {Q : List α}
    (h : (a, b) ∈ (x :: Q).zip ((x :: Q).drop 1)) :
    (∃ hQ : Q ≠ [], a = x ∧ b = Q.head hQ) ∨ (a, b) ∈ Q.zip (Q.drop 1) := by
  rcases Q with _ | ⟨q, Q'⟩
  · simp at h
  · simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.mem_cons,
      Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact Or.inl ⟨by simp, rfl, rfl⟩
    · exact Or.inr (by simpa using h)

/-- A pair of consecutive entries of `L₁ ++ L₂` is consecutive in `L₁`, or has its first entry in
`L₁` and its second in `L₂`, or is consecutive in `L₂`. -/
private theorem mem_zip_drop_append {α : Type*} {a b : α} :
    ∀ (L₁ L₂ : List α), (a, b) ∈ (L₁ ++ L₂).zip ((L₁ ++ L₂).drop 1) →
      (a, b) ∈ L₁.zip (L₁.drop 1) ∨ (a ∈ L₁ ∧ b ∈ L₂) ∨ (a, b) ∈ L₂.zip (L₂.drop 1)
  | [], _, h => Or.inr (Or.inr (by simpa using h))
  | [x], L₂, h => by
    rcases L₂ with _ | ⟨y, ys⟩
    · simp at h
    · simp only [List.singleton_append, List.drop_succ_cons, List.drop_zero, List.zip_cons_cons,
        List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact Or.inr (Or.inl ⟨List.mem_singleton_self _, List.mem_cons_self ..⟩)
      · exact Or.inr (Or.inr (by simpa using h))
  | x :: y :: rest, L₂, h => by
    simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.zip_cons_cons,
      List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact Or.inl (by simp)
    · have h' : (a, b) ∈ ((y :: rest) ++ L₂).zip (((y :: rest) ++ L₂).drop 1) := by simpa using h
      rcases mem_zip_drop_append (y :: rest) L₂ h' with h1 | h1 | h1
      · exact Or.inl (by simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons,
          List.mem_cons]; exact Or.inr (by simpa using h1))
      · exact Or.inr (Or.inl ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩)
      · exact Or.inr (Or.inr h1)

/-- Two consecutive vertices of the lift of a path of `GK` (that starts at a node and ends at a
node) either meet the blob of a middle of the path, or stand for two consecutive nodes of the
path. -/
theorem mem_zip_liftTail (hB : B.IsBlobMap GK G) :
    ∀ (prev : Fin N) (L : List (Fin N)), B.isNode prev = true →
      WallOfHeight.IsSimpleWalkList GK (prev :: L) → (prev :: L).Nodup →
      (∀ hL : L ≠ [], B.isNode (L.getLast hL) = true) →
      ∀ a b, (a, b) ∈ (B.node prev :: B.liftTail prev L).zip
          ((B.node prev :: B.liftTail prev L).drop 1) →
        (∃ v ∈ L, B.isNode v = false ∧ (a ∈ B.blob v ∨ b ∈ B.blob v)) ∨
        (∃ u v, (u, v) ∈ (prev :: L).zip ((prev :: L).drop 1) ∧ B.isNode u = true ∧
          B.isNode v = true ∧ a = B.node u ∧ b = B.node v)
  | _, [], _, _, _, _, a, b, h => by simp [liftTail] at h
  | prev, [v], hprev, _, _, hlast, a, b, h => by
    have hv : B.isNode v = true := hlast (by simp)
    simp only [liftTail, piece, hv, ↓reduceIte, List.append_nil, List.drop_succ_cons,
      List.drop_zero, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨prev, v, by simp, hprev, hv, rfl, rfl⟩
  | prev, v :: w :: rest, hprev, hw, hnd, hlast, a, b, h => by
    have hnd' : (v :: w :: rest).Nodup := (List.nodup_cons.mp hnd).2
    have hzip_sub : ∀ u u', (u, u') ∈ (v :: w :: rest).zip ((v :: w :: rest).drop 1) →
        (u, u') ∈ (prev :: v :: w :: rest).zip ((prev :: v :: w :: rest).drop 1) := by
      intro u u' hu
      simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.mem_cons] at hu ⊢
      exact Or.inr hu
    cases hv : B.isNode v
    · -- `v` is a middle, followed by the node `w`.
      have hpw : prev ≠ w := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
      have hends := ends_of_mid hB hv hw.1 hw.2.1 hpw
      have hwn : B.isNode w = true := by
        rcases hends with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact (hB.ends_node v hv).2.1
        · exact (hB.ends_node v hv).1
      have hwpiece : B.piece v w = [B.node w] := by simp [piece, hwn]
      simp only [liftTail, hwpiece, List.singleton_append] at h
      have hmid : ∀ y ∈ B.piece prev v, y ∈ B.blob v := fun y hy => (mem_piece hB).mp hy
      have hvL : v ∈ v :: w :: rest := List.mem_cons_self ..
      have hPne := piece_ne_nil hB prev v
      rcases mem_zip_cons_self h with ⟨hQ, -, hb⟩ | h
      · refine Or.inl ⟨v, hvL, hv, Or.inr (hmid b ?_)⟩
        rw [hb, List.head_append_of_ne_nil hPne]
        exact List.head_mem _
      · rcases mem_zip_drop_append _ _ h with h1 | h1 | h1
        · exact Or.inl ⟨v, hvL, hv, Or.inl (hmid a (WallOfHeight.mem_of_mem_zip_drop_one h1).1)⟩
        · exact Or.inl ⟨v, hvL, hv, Or.inl (hmid a h1.1)⟩
        · have ih := mem_zip_liftTail hB w rest hwn hw.2.2 (List.nodup_cons.mp hnd').2
            (fun hL => by
              have := hlast (by simp)
              rwa [List.getLast_cons (by simp), List.getLast_cons hL] at this) a b h1
          rcases ih with ⟨v', hv', hv'n, hab⟩ | ⟨u, u', hu, hun, hu'n, rfl, rfl⟩
          · exact Or.inl ⟨v', by simp [hv'], hv'n, hab⟩
          · exact Or.inr ⟨u, u', hzip_sub u u' (by
              simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons,
                List.mem_cons] at hu ⊢
              exact Or.inr hu), hun, hu'n, rfl, rfl⟩
    · -- `v` is a node.
      have hvpiece : B.piece prev v = [B.node v] := by simp [piece, hv]
      simp only [liftTail, hvpiece, List.singleton_append] at h
      rcases mem_zip_cons_self h with ⟨-, rfl, rfl⟩ | h
      · exact Or.inr ⟨prev, v, by simp, hprev, hv, rfl, by simp⟩
      · have ih := mem_zip_liftTail hB v (w :: rest) hv hw.2 hnd'
          (fun hL => by simpa using hlast (by simp)) a b (by simpa [liftTail] using h)
        rcases ih with ⟨v', hv', hv'n, hab⟩ | ⟨u, u', hu, hun, hu'n, rfl, rfl⟩
        · exact Or.inl ⟨v', List.mem_cons_of_mem _ hv', hv'n, hab⟩
        · exact Or.inr ⟨u, u', hzip_sub u u' hu, hun, hu'n, rfl, rfl⟩

/-- The lift of a path that ends at a node ends at the vertex of that node. -/
theorem getLast?_liftTail (hB : B.IsBlobMap GK G) :
    ∀ (prev : Fin N) (L : List (Fin N)) (hL : L ≠ []), B.isNode (L.getLast hL) = true →
      (B.liftTail prev L).getLast? = some (B.node (L.getLast hL))
  | _, [], hL, _ => absurd rfl hL
  | prev, [v], _, hv => by
    simp only [List.getLast_singleton] at hv ⊢
    simp [liftTail, piece, hv]
  | prev, v :: w :: rest, _, hlast => by
    have hT' : B.liftTail v (w :: rest) ≠ [] := liftTail_ne_nil hB v (by simp)
    have heq : B.liftTail prev (v :: w :: rest) = B.piece prev v ++ B.liftTail v (w :: rest) :=
      rfl
    rw [heq, List.getLast?_append, getLast?_liftTail hB v (w :: rest) (by simp)
      (by rwa [List.getLast_cons_cons] at hlast), List.getLast_cons_cons]
    rfl

theorem getLast_liftTail (hB : B.IsBlobMap GK G) (prev : Fin N) (L : List (Fin N))
    (hL : L ≠ []) (hlast : B.isNode (L.getLast hL) = true) (hT : B.liftTail prev L ≠ []) :
    (B.liftTail prev L).getLast hT = B.node (L.getLast hL) := by
  have h := getLast?_liftTail hB prev L hL hlast
  rw [List.getLast?_eq_some_getLast hT, Option.some.injEq] at h
  exact h

/-- An inner entry of a list without repetitions is neither its first nor its last entry. -/
private theorem ne_head_and_ne_getLast {α : Type*} {L : List α} (hne : L ≠ []) (hnd : L.Nodup)
    {y : α} (hy : y ∈ (L.drop 1).dropLast) : y ≠ L.head hne ∧ y ≠ L.getLast hne := by
  rcases L with _ | ⟨x, rest⟩
  · exact False.elim (hne rfl)
  · simp only [List.drop_succ_cons, List.drop_zero] at hy
    have hrest : rest ≠ [] := by
      rintro rfl
      simp at hy
    have hyr : y ∈ rest := List.dropLast_subset rest hy
    have hnd' := (List.nodup_cons.mp hnd)
    refine ⟨fun h => hnd'.1 (by rw [h] at hyr; exact hyr), fun h => ?_⟩
    have hsplit := hnd'.2
    rw [← List.dropLast_append_getLast hrest] at hsplit
    rw [List.getLast_cons hrest] at h
    exact (List.nodup_append.mp hsplit).2.2 y hy _ (List.mem_singleton_self _) h

/-- The last entry of a list of length at least `2` follows some entry. -/
private theorem exists_mem_zip_getLast {α : Type*} :
    ∀ {L : List α} (hne : L ≠ []), 2 ≤ L.length → ∃ a, (a, L.getLast hne) ∈ L.zip (L.drop 1)
  | [], hne, _ => absurd rfl hne
  | [_], _, h => by simp at h
  | [x, y], _, _ => ⟨x, by simp⟩
  | x :: y :: z :: rest, _, _ => by
    obtain ⟨a, ha⟩ := exists_mem_zip_getLast (L := y :: z :: rest) (by simp) (by simp)
    refine ⟨a, ?_⟩
    simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.mem_cons] at ha ⊢
    rw [List.getLast_cons (by simp)]
    exact Or.inr ha

/-- **Lifting the rays of a star.** Let `B` be a blob map from `GK` to `G` that respects the
walls `WK` and `W`. If `rays` are the rays of an `(l, m)`-star over `WK` with center `c` (`l ≥ 3`),
in the format of `IsAlg92Output`, then `c` is a node, and the lifted rays `B.liftRay (rays i)` are
the rays of an `(l, m)`-star over `W` with center `B.node c`. -/
theorem isStarRay_liftRay {h l m : ℕ} {WK : WallOfHeight h GK} {W : WallOfHeight h G}
    (hB : B.IsBlobMap GK G) (hBW : B.IsWallBlobMap WK W) (hl : 3 ≤ l) {c : Fin N}
    {rays : Fin l → List (Fin N)}
    (hray : ∀ i : Fin l, WK.IsStarRay c (rays i))
    (hdisj : ∀ i j : Fin l, i ≠ j → ∀ y, y ∈ rays i → y ∈ rays j → y = c)
    (hfar : ∀ i j : Fin l, i ≠ j → ∀ a b,
      (rays i).getLast? = some a → (rays j).getLast? = some b → m ≤ WK.brickDist a b) :
    (∀ i : Fin l, W.IsStarRay (B.node c) (B.liftRay (rays i))) ∧
    (∀ i j : Fin l, i ≠ j → ∀ y, y ∈ B.liftRay (rays i) → y ∈ B.liftRay (rays j) →
      y = B.node c) ∧
    (∀ i j : Fin l, i ≠ j → ∀ a b, (B.liftRay (rays i)).getLast? = some a →
      (B.liftRay (rays j)).getLast? = some b → m ≤ W.brickDist a b) := by
  -- Each ray is `c :: rest i` with `rest i ≠ []`.
  have hshape : ∀ i, ∃ rest : List (Fin N), rays i = c :: rest ∧ rest ≠ [] := fun i => by
    obtain ⟨hne, hhead, hlen, -⟩ := hray i
    rcases hr : rays i with _ | ⟨x, rest⟩
    · exact absurd hr hne
    · have hx : x = c := by simpa [hr] using hhead
      refine ⟨rest, by rw [hx], fun h => ?_⟩
      rw [hr, h] at hlen
      simp at hlen
  choose rest hrest hrest_ne using hshape
  -- The last vertex of each ray is a node.
  have hlast_node : ∀ i, B.isNode ((rays i).getLast (hray i).1) = true := by
    intro i
    obtain ⟨hne, -, hlen, -, hwalk, hlastW, -, hnowall⟩ := hray i
    by_contra hmid
    rw [Bool.not_eq_true] at hmid
    obtain ⟨a, ha⟩ := exists_mem_zip_getLast hne hlen
    have hadj := WallOfHeight.isSimpleWalkList_adj_of_mem_zip hwalk ha
    exact hnowall a _ ha (WallOfHeight.IsWallEdge.symm _
      (hBW.isWallEdge_mid _ a hmid hlastW hadj.symm))
  -- The center is a node: a middle has only two neighbours.
  have hc_node : B.isNode c = true := by
    by_contra hmid
    rw [Bool.not_eq_true] at hmid
    have hsecond : ∀ i, ∃ v, v ∈ rays i ∧ GK.toSimpleGraph.Adj c v := fun i => by
      obtain ⟨-, -, -, -, hwalk, -⟩ := hray i
      obtain ⟨v, rest', hv⟩ := List.exists_cons_of_ne_nil (hrest_ne i)
      rw [hrest i, hv] at hwalk
      exact ⟨v, by rw [hrest i, hv]; simp, hwalk.1⟩
    choose v hv hadj using hsecond
    have hends : ∀ i, v i = (B.ends c).1 ∨ v i = (B.ends c).2 := fun i =>
      hB.adj_mid c (v i) hmid (hadj i)
    let i₀ : Fin l := ⟨0, by omega⟩
    let i₁ : Fin l := ⟨1, by omega⟩
    let i₂ : Fin l := ⟨2, by omega⟩
    have hne01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    have hne02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
    have hne12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
    have key : ∀ i j, i ≠ j → v i ≠ v j := fun i j hij hvij =>
      (hadj i).ne (hdisj i j hij (v i) (hv i) (hvij ▸ hv j)).symm
    rcases hends i₀ with h0 | h0 <;> rcases hends i₁ with h1 | h1 <;>
      rcases hends i₂ with h2 | h2
    all_goals first
      | exact key _ _ hne01 (h0.trans h1.symm)
      | exact key _ _ hne02 (h0.trans h2.symm)
      | exact key _ _ hne12 (h1.trans h2.symm)
  -- Facts about one lifted ray.
  have hlift : ∀ i, B.liftRay (rays i) = B.node c :: B.liftTail c (rest i) := fun i => by
    rw [hrest i]
    rfl
  have hmem : ∀ i y, y ∈ B.liftRay (rays i) ↔ ∃ v ∈ rays i, y ∈ B.blob v := fun i y => by
    rw [hlift i, List.mem_cons, mem_liftTail hB, hrest i]
    constructor
    · rintro (rfl | ⟨v, hv, hy⟩)
      · exact ⟨c, List.mem_cons_self .., by rw [hB.blob_node c hc_node]; simp⟩
      · exact ⟨v, List.mem_cons_of_mem _ hv, hy⟩
    · rintro ⟨v, hv, hy⟩
      rcases List.mem_cons.mp hv with rfl | hv
      · left
        rw [hB.blob_node v hc_node] at hy
        simpa using hy
      · exact Or.inr ⟨v, hv, hy⟩
  have hlastR : ∀ i (hL : rest i ≠ []), (rest i).getLast hL = (rays i).getLast (hray i).1 :=
    fun i hL => by
      simp only [hrest i]
      rw [List.getLast_cons hL]
  have hlast_rest : ∀ i (hL : rest i ≠ []), B.isNode ((rest i).getLast hL) = true := fun i hL => by
    rw [hlastR i hL]
    exact hlast_node i
  have hwalkK : ∀ i, WallOfHeight.IsSimpleWalkList GK (c :: rest i) := fun i => by
    rw [← hrest i]
    exact (hray i).2.2.2.2.1
  have hndK : ∀ i, (c :: rest i).Nodup := fun i => by
    rw [← hrest i]
    exact (hray i).2.2.2.1
  have hne : ∀ i, B.liftRay (rays i) ≠ [] := fun i => by rw [hlift i]; simp
  have hgetLast : ∀ i, (B.liftRay (rays i)).getLast (hne i) =
      B.node ((rays i).getLast (hray i).1) := fun i => by
    have hT : B.liftTail c (rest i) ≠ [] := liftTail_ne_nil hB c (hrest_ne i)
    simp only [hlift i]
    rw [List.getLast_cons hT, getLast_liftTail hB c (rest i) (hrest_ne i) (hlast_rest i _),
      hlastR i]
  have hnd : ∀ i, (B.liftRay (rays i)).Nodup := fun i => by
    rw [hlift i, List.nodup_cons]
    refine ⟨fun h => ?_, nodup_liftTail hB c (rest i) (List.nodup_cons.mp (hndK i)).2⟩
    obtain ⟨v, hv, hcv⟩ := (mem_liftTail hB c (rest i) _).mp h
    have hcv' : v ≠ c := fun h' => (List.nodup_cons.mp (hndK i)).1 (h' ▸ hv)
    exact hB.disjoint c v hcv'.symm _ (by rw [hB.blob_node c hc_node]; simp) hcv
  -- A vertex of a ray other than its first and last vertex is not in `WK`.
  have hinner : ∀ i v, v ∈ rays i → v ≠ c → v ≠ (rays i).getLast (hray i).1 →
      v ∉ WK.vertexFinset := fun i v hv hvc hvl => by
    obtain ⟨hne', hhead, -, -, -, -, hin, -⟩ := hray i
    rcases WallOfHeight.mem_head_or_drop_one_dropLast_or_getLast hne' hv with h | h | h
    · exact absurd (h.trans hhead) hvc
    · exact hin v h
    · exact absurd h hvl
  refine ⟨fun i => ?_, fun i j hij y hyi hyj => ?_, fun i j hij a b ha hb => ?_⟩
  · refine ⟨hne i, by simp [hlift i], ?_, hnd i, ?_, ?_, ?_, ?_⟩
    · rw [hlift i]
      have := liftTail_ne_nil hB c (hrest_ne i)
      rcases hT : B.liftTail c (rest i) with _ | ⟨y, ys⟩
      · exact absurd hT this
      · simp
    · rw [hlift i]
      exact isSimpleWalkList_liftTail hB c (rest i) hc_node (hwalkK i) (hndK i)
        (hlast_rest i)
    · rw [hgetLast i]
      exact hBW.node_mem _ (hlast_node i) (hray i).2.2.2.2.2.1
    · intro y hy hyW
      obtain ⟨hyh, hyl⟩ := ne_head_and_ne_getLast (hne i) (hnd i) hy
      have hyL : y ∈ B.liftRay (rays i) := List.drop_subset 1 _ (List.dropLast_subset _ hy)
      obtain ⟨v, hv, hyv⟩ := (hmem i y).mp hyL
      have hvc : v ≠ c := by
        rintro rfl
        rw [hB.blob_node v hc_node, List.mem_singleton] at hyv
        exact hyh (by rw [hyv]; simp [hlift i])
      have hvl : v ≠ (rays i).getLast (hray i).1 := by
        intro h
        rw [h, hB.blob_node _ (hlast_node i), List.mem_singleton] at hyv
        exact hyl (by rw [hyv, hgetLast i])
      exact hBW.blob_not_mem v (hinner i v hv hvc hvl) y hyv hyW
    · intro a b hab hwall
      rw [hlift i] at hab
      rcases mem_zip_liftTail hB c (rest i) hc_node (hwalkK i) (hndK i) (hlast_rest i) a b hab
        with ⟨v, hv, hvn, hab'⟩ | ⟨u, v, huv, hun, hvn, rfl, rfl⟩
      · have hvR : v ∈ rays i := by rw [hrest i]; exact List.mem_cons_of_mem _ hv
        have hvc : v ≠ c := fun h => by rw [h, hc_node] at hvn; exact absurd hvn (by decide)
        have hvl : v ≠ (rays i).getLast (hray i).1 := fun h => by
          rw [h, hlast_node i] at hvn
          exact absurd hvn (by decide)
        have hvW := hinner i v hvR hvc hvl
        obtain ⟨haW, hbW⟩ := WallOfHeight.IsWallEdge.mem_vertexFinset W hwall
        rcases hab' with h | h
        · exact hBW.blob_not_mem v hvW a h haW
        · exact hBW.blob_not_mem v hvW b h hbW
      · have huv' : (u, v) ∈ (rays i).zip ((rays i).drop 1) := by rw [hrest i]; exact huv
        exact (hray i).2.2.2.2.2.2.2 u v huv' (hBW.isWallEdge u v hun hvn hwall)
  · obtain ⟨u, hu, hyu⟩ := (hmem i y).mp hyi
    obtain ⟨v, hv, hyv⟩ := (hmem j y).mp hyj
    have huv : u = v := by
      by_contra hne'
      exact hB.disjoint u v hne' y hyu hyv
    subst huv
    have huc := hdisj i j hij u hu hv
    subst huc
    rw [hB.blob_node _ hc_node, List.mem_singleton] at hyu
    exact hyu
  · rw [List.getLast?_eq_some_getLast (hne i), hgetLast i, Option.some.injEq] at ha
    rw [List.getLast?_eq_some_getLast (hne j), hgetLast j, Option.some.injEq] at hb
    subst ha hb
    exact (hfar i j hij _ _ (List.getLast?_eq_some_getLast _) (List.getLast?_eq_some_getLast _)).trans
      (hBW.brickDist_le _ _ (hlast_node i) (hlast_node j) (hray i).2.2.2.2.2.1
        (hray j).2.2.2.2.2.1)

/-- **A correct output of the compressed input gives a correct output of the input.** If `B` is a
blob map from the graph of `xK` to the graph of `x` that respects their walls, then every output
of the algorithm of (9.2) that is correct for `xK` gives one that is correct for `x`: the star is
lifted by `isStarRay_liftRay` and the model of `K_p` by `isCliqueModel_liftSets`. -/
theorem exists_isAlg92Output_of_blobMap {l m p h k r k' r' : ℕ} (hl : 3 ≤ l)
    {xK : Alg92Input l m p h k r} {x : Alg92Input l m p h k' r'} {B : BlobMap xK.n x.n}
    (hB : B.IsBlobMap xK.G x.G) (hBW : B.IsWallBlobMap xK.W x.W) {outK : List ℕ}
    (hout : IsAlg92Output l m p xK outK) :
    ∃ out : List ℕ, IsAlg92Output l m p x out := by
  rcases hout with ⟨c, rays, -, hrays, hdisj, hfar⟩ | ⟨K, -, hK⟩
  · obtain ⟨h1, h2, h3⟩ := isStarRay_liftRay hB hBW hl hrays hdisj hfar
    exact ⟨_, Or.inl ⟨B.node c, fun i => B.liftRay (rays i), rfl, h1, h2, h3⟩⟩
  · exact ⟨_, Or.inr ⟨fun i => B.liftSet (K i), rfl, isCliqueModel_liftSets hB hK⟩⟩

end BlobMap

end Alg92

end GraphMinor.Compute
