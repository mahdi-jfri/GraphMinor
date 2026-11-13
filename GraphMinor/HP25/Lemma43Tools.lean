module

public import GraphMinor.HP25.Alternate
public import GraphMinor.HP25.Web
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.Prop34
import GraphMinor.HP25.Split
public import GraphMinor.HP25.Embedding

/-!
# Tools for the proof of Lemma 4.3

Small facts about paths avoiding a set, crossings in an edge extension, and crossings of a side of a
graph, used in both cases of the proof of Lemma 4.3 (Humeau and Pous, pages 13–15):

* `isConnectedAvoiding_of_walk`: a walk whose vertices in `X` are only its ends gives an `X`-path;
* `exists_connected_of_walk`: a walk from `A` to `B` whose vertices in `X` lie in `A ∪ B` contains an
  `X`-path from `A` to `B`;
* `isCrossed_sup_edge_cases`: a crossing of `T` in `G + uv`, with `u, v ∈ T`, is a crossing of `T` in
  `G`, or uses the edge `uv` as one of its paths, so that the other path is a `T`-path of `G` whose
  ends alternate with `u` and `v`;
* `IsCrossed.of_restrict_prefix`: a crossing of a stretch `T₁` of a rotation `T₁ T₂` of `T`, in the
  subgraph induced by a set that misses `T₂`, is a crossing of `T`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- A walk from `s` to `t` whose only vertices in `X` are its ends gives an `X`-path from `s` to
`t`. -/
theorem isConnectedAvoiding_of_walk {X : Set V} {s t : V} (W : G.Walk s t)
    (hW : ∀ v ∈ W.support, v ∈ X → v = s ∨ v = t) : IsConnectedAvoiding G X s {t} := by
  classical
  refine ⟨t, rfl, W.bypass, W.bypass_isPath, fun v hv h1 h2 hX => ?_⟩
  rcases hW v (W.support_bypass_subset_support hv) hX with h | h
  · exact h1 h
  · exact h2 h

/-- `X`-paths between two vertices go both ways. -/
theorem IsConnectedAvoiding.symm' {X : Set V} {s t : V} (h : IsConnectedAvoiding G X s {t}) :
    IsConnectedAvoiding G X t {s} := by
  obtain ⟨z, hz, p, hp, hin⟩ := h
  rw [mem_singleton_iff] at hz
  subst hz
  exact ⟨s, rfl, p.reverse, hp.reverse, fun x hx h1 h2 => hin x (by simpa using hx) h2 h1⟩

/-- **An `X`-path from `A` to `B` inside a walk.** Let `p` be a walk from `a ∈ A` to `s` whose
vertices other than `a` miss `X`, and `W` a walk from `s` to `t ∈ B` whose vertices in `X` lie in
`A ∪ B`. Then some vertex of `A` has an `X`-path to some vertex of `B`. -/
theorem exists_connected_of_walk {X A B : Set V} :
    ∀ {s t : V} (W : G.Walk s t), t ∈ B → (∀ v ∈ W.support, v ∈ X → v ∈ A ∨ v ∈ B) →
      ∀ a ∈ A, ∀ (p : G.Walk a s), (∀ v ∈ p.support, v ≠ a → v ∉ X) →
      ∃ a ∈ A, ∃ b ∈ B, IsConnectedAvoiding G X a {b}
  | _, _, .nil, ht, _, a, ha, p, hp =>
    ⟨a, ha, _, ht, isConnectedAvoiding_of_walk p fun v hv hX => by
      by_cases h : v = a
      · exact Or.inl h
      · exact absurd hX (hp v hv h)⟩
  | s, t, .cons (v := s₁) h W, ht, hW, a, ha, p, hp => by
    have hW' : ∀ v ∈ W.support, v ∈ X → v ∈ A ∨ v ∈ B := fun v hv => hW v (by simp [hv])
    have hp' : ∀ v ∈ (p.concat h).support, v ≠ a → v ≠ s₁ → v ∉ X := by
      intro v hv h1 _
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact hp v hv h1
      · exact absurd rfl ‹v ≠ v›
    by_cases hs₁ : s₁ ∈ X
    · rcases hW s₁ (by simp) hs₁ with hA | hB
      · have hnil : ∀ v ∈ (Walk.nil : G.Walk s₁ s₁).support, v ≠ s₁ → v ∉ X := by
          intro v hv h1
          rw [Walk.support_nil, List.mem_singleton] at hv
          exact absurd hv h1
        exact exists_connected_of_walk W ht hW' s₁ hA .nil hnil
      · refine ⟨a, ha, s₁, hB, isConnectedAvoiding_of_walk (p.concat h) fun v hv hX => ?_⟩
        by_cases h1 : v = a
        · exact Or.inl h1
        · by_cases h2 : v = s₁
          · exact Or.inr h2
          · exact absurd hX (hp' v hv h1 h2)
    · refine exists_connected_of_walk W ht hW' a ha (p.concat h) fun v hv h1 => ?_
      by_cases h2 : v = s₁
      · rw [h2]; exact hs₁
      · exact hp' v hv h1 h2

/-- A cycle stays a cycle in a larger graph. -/
theorem IsCycleList.mono {H : SimpleGraph V} {C : List V} (h : IsCycleList G C) (hle : G ≤ H) :
    IsCycleList H C :=
  ⟨h.1, h.2.1, fun p hp => hle (h.2.2 p hp)⟩

/-- **Crossings in an edge extension.** If `T` is crossed in `G + uv`, where `u` and `v` are distinct
entries of `T`, then either `T` is crossed in `G`, or one path of the crossing is a path from `u` to
`v` and the other path is a `T`-path of `G` whose ends `c`, `d` alternate with `u` and `v`. -/
theorem isCrossed_sup_edge_cases {T : List V} {u v : V} (hc : IsCrossed (G ⊔ edge u v) T)
    (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) :
    IsCrossed G T ∨ ∃ c d, ∃ R : G.Walk c d, Alternate T u v c d ∧ IsTPath G T R := by
  obtain ⟨a, b, c, d, Q, R, hcr⟩ := hc
  have halt := hcr.alternate
  obtain ⟨hidx, hQ, hR, hdisj⟩ := hcr
  by_cases hQe : s(u, v) ∈ Q.edges
  · have hRe : s(u, v) ∉ R.edges := fun h =>
      hdisj (Q.fst_mem_support_of_mem_edges hQe) (R.fst_mem_support_of_mem_edges h)
    obtain ⟨R', hR', -⟩ := hR.transfer hRe
    right
    rcases ends_of_mem_edges hQ hQe hu hv huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨c, d, R', halt, hR'⟩
    · exact ⟨d, c, R'.reverse, halt.swap, hR'.reverse⟩
  · by_cases hRe : s(u, v) ∈ R.edges
    · obtain ⟨Q', hQ', -⟩ := hQ.transfer hQe
      right
      rcases ends_of_mem_edges hR hRe hu hv huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨b, a, Q'.reverse, halt.comm, hQ'.reverse⟩
      · exact ⟨a, b, Q', halt.comm.swap, hQ'⟩
    · obtain ⟨Q', hQ', hQs⟩ := hQ.transfer hQe
      obtain ⟨R', hR', hRs⟩ := hR.transfer hRe
      exact Or.inl ⟨a, b, c, d, Q', R', hidx, hQ', hR', by rw [hQs, hRs]; exact hdisj⟩

/-- A vertex of a walk of the subgraph induced by `S'`, other than its start, lies in `S'`. -/
theorem mem_of_mem_support_restrict {S' : Set V} :
    ∀ {a b : V} (p : (restrict G S').Walk a b) {x : V}, x ∈ p.support → x ≠ a → x ∈ S'
  | _, _, .nil, x, hx, hxa => by simp at hx; exact absurd hx hxa
  | _, _, .cons h p, x, hx, hxa => by
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact absurd rfl hxa
    · by_cases hx' : x = p.getVert 0
      · rw [hx', Walk.getVert_zero]; exact h.2.2
      · exact mem_of_mem_support_restrict p hx (by rwa [Walk.getVert_zero] at hx')

/-- **Crossings of a side.** If `T` is, up to rotation, `T₁ T₂`, and `T₁` is crossed in the subgraph
induced by a set `S'` that misses `T₂`, then `T` is crossed in `G`. -/
theorem IsCrossed.of_restrict_prefix {S' : Set V} {T T₁ T₂ : List V} {k : ℕ}
    (h : IsCrossed (restrict G S') T₁) (hrot : T.rotate k = T₁ ++ T₂)
    (hT₂ : ∀ v ∈ T₂, v ∉ S') : IsCrossed G T := by
  obtain ⟨a, b, c, d, Q, R, ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisj⟩ := h
  have hle := restrict_le G S'
  have conv : ∀ {x y : V} (p : (restrict G S').Walk x y), IsTPath (restrict G S') T₁ p →
      IsTPath G (T.rotate k) (p.mapLe hle) := by
    intro x y p hp
    rw [hrot]
    refine ⟨hp.1.mapLe hle, List.mem_append_left _ hp.2.1, List.mem_append_left _ hp.2.2.1,
      fun w hw h1 h2 => ?_⟩
    rw [support_mapLe] at hw
    obtain ⟨hw1, -⟩ := hp.2.2.2 w hw h1 h2
    have hw2 : w ∉ T₂ := fun h' => hT₂ w h' (mem_of_mem_support_restrict p hw h1)
    have : w ∉ T₁ ++ T₂ := by simp only [List.mem_append, not_or]; exact ⟨hw1, hw2⟩
    exact ⟨this, this⟩
  have e : ∀ {p : ℕ} {w : V}, T₁[p]? = some w → (T.rotate k)[p]? = some w := fun {p w} hw => by
    rw [hrot, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hw).1]
    exact hw
  refine IsCrossed.of_rotate k ⟨a, b, c, d, Q.mapLe hle, R.mapLe hle,
    ⟨⟨i, r, j, s, hir, hrj, hjs, e hi, e hr, e hj, e hs⟩, ?_, ?_, ?_⟩⟩
  · exact conv Q hQ
  · exact conv R hR
  · rw [support_mapLe, support_mapLe]; exact hdisj

/-- The start of a path is not on the part after a later vertex. -/
theorem start_notMem_support_dropUntil [DecidableEq V] {u v c : V} {q : G.Walk u v} (hq : q.IsPath)
    (hc : c ∈ q.support) (hcu : c ≠ u) : u ∉ (q.dropUntil c hc).support := by
  intro hu
  have hnd := hq.support_nodup
  rw [← q.take_spec hc, Walk.support_append] at hnd
  have hu' : u ∈ (q.dropUntil c hc).support.tail := by
    rw [← Walk.cons_tail_support (q.dropUntil c hc)] at hu
    rcases List.mem_cons.mp hu with h | h
    · exact absurd h.symm hcu
    · exact h
  exact (List.nodup_append.mp hnd).2.2 u (Walk.start_mem_support _) u hu' rfl

/-- **Two meeting paths.** Let `p` be a path from `x` to `w` and `q` a path from `u` to `v`, each with
no vertex in `X` other than its ends. If they meet at a vertex `c` other than `w` and `u`, then
`p` up to `c` followed by `q` from `c` is an `X`-path from `x` to `v`. -/
theorem connected_of_meet {X : Set V} {x w u v c : V} {p : G.Walk x w} {q : G.Walk u v}
    (hp : p.IsPath) (hq : q.IsPath) (hpX : ∀ y ∈ p.support, y ∈ X → y = x ∨ y = w)
    (hqX : ∀ y ∈ q.support, y ∈ X → y = u ∨ y = v) (hcp : c ∈ p.support) (hcq : c ∈ q.support)
    (hcw : c ≠ w) (hcu : c ≠ u) : IsConnectedAvoiding G X x {v} := by
  classical
  refine isConnectedAvoiding_of_walk ((p.takeUntil c hcp).append (q.dropUntil c hcq))
    fun y hy hyX => ?_
  rcases (Walk.mem_support_append_iff _ _).mp hy with hy | hy
  · rcases hpX y (Walk.support_takeUntil_subset_support p hcp hy) hyX with h | rfl
    · exact Or.inl h
    · exact absurd hy (Walk.endpoint_notMem_support_takeUntil hp hcp hcw.symm)
  · rcases hqX y (Walk.support_dropUntil_subset_support q hcq hy) hyX with rfl | h
    · exact absurd hy (start_notMem_support_dropUntil hq hcq hcu)
    · exact Or.inr h

/-- A `T`-path gives a `T`-connection between its ends. -/
theorem IsTPath.isConnectedAvoiding {T : List V} {a b : V} {p : G.Walk a b} (hp : IsTPath G T p) :
    IsConnectedAvoiding G {v | v ∈ T} a {b} :=
  ⟨b, rfl, p, hp.1, fun x hx h1 h2 => (hp.2.2.2 x hx h1 h2).1⟩

/-- A cycle of `G` whose vertices lie in `S'` is a cycle of the subgraph induced by `S'`. -/
theorem IsCycleList.restrict {C : List V} (h : IsCycleList G C) {S' : Set V}
    (hS : ∀ v ∈ C, v ∈ S') : IsCycleList (restrict G S') C :=
  ⟨h.1, h.2.1, fun p hp => ⟨h.2.2 p hp, hS _ (List.of_mem_zip hp).1,
    hS _ (List.mem_rotate.mp (List.of_mem_zip hp).2)⟩⟩

/-- A beginning of a path list is a path list. -/
theorem IsPathList.prefix {R : Set V} {l₁ l₂ : List V} (h : IsPathList G R (l₁ ++ l₂)) :
    IsPathList G R l₁ :=
  ⟨h.1.sublist (List.sublist_append_left _ _), h.2.1.left_of_append,
    fun x hx => h.2.2 x (List.mem_append_left _ hx)⟩

/-- **Cutting a cycle along a chord.** If `a A b B` is a cycle with `A` nonempty and `ab` is an edge,
then `a A b` is a cycle. -/
theorem IsCycleList.of_chord {a b : V} {A B : List V} (h : IsCycleList G (a :: A ++ b :: B))
    (hab : G.Adj a b) (hA : A ≠ []) : IsCycleList G (a :: A ++ [b]) := by
  have hP := h.isPathList (R := univ) (fun _ _ => trivial)
  have e : a :: A ++ b :: B = (a :: A ++ [b]) ++ B := by simp
  rw [e] at hP
  have h1 := hP.prefix
  have hnd := h1.1
  have hab' : a ≠ b := G.ne_of_adj hab
  have h2 : IsPathList G univ (b :: ([] : List V) ++ [a]) :=
    ⟨by simp [hab'.symm], by simp [hab.symm], fun _ _ => trivial⟩
  have := isCycleList_of_two_paths h1 h2 (by simp) hab' (Or.inl hA)
  simpa using this

end GraphMinor.HP25
