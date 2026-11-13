module

public import GraphMinor.HP25.Sec5StripTools
public import GraphMinor.HP25.Sec5StripDraw
import GraphMinor.HP25.Sec5Lemma54
import GraphMinor.HP25.Lemma43
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Completion
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Prop23
import GraphMinor.HP25.Prop34Tools
import GraphMinor.HP25.Embedding
import GraphMinor.HP25.Lemma43Tools
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# The strip lemma

Lemma 5.4 of Humeau and Pous (page 19) asks to show that the edge `y_j y_s` is safe. The paper's
proof edits fans of a web, and a more general chord lemma that could replace this argument is
false. We prove the following *strip lemma*, which gives Lemma 5.4 for induced,
tight paths, for `r < s` as well as for `r = s` (`lemma_5_4_tight`).

Let `P` be an induced and tight `C`-path from `a` to `b` (`C = a A b B` up to rotation), with
vertex list `L₁ y N s L₂`. Let `y` and `s` be on side `B`, and let no vertex of `N` be on side `B`.
Then the edge `ys` is safe (`strip_safe`).

The proof argues in a web `H ⊇ G` in which `C` is maximally crossless (Lemma 4.3), as in
Proposition 3.2. Let `(Q, R)` be a crossing of `C` in `G + ys`, with `ys` on `Q`. The rib vertices of
`P` form a path `l` of the rib that cuts the closed disc bounded by the image of `C` into two sides,
the side of `A` and the side of `B` (`IsRibEmbedding.theta`). Along the rib vertices of `N`, the
triangles on the side of `B` form a strip (`IsRibEmbedding.joinedIn_strip`). The two parts of `Q`
before and after `ys` end on the first and last triangle of the strip (`end_tri`, which uses that
`y` and `s` are on side `B`). The rib vertices of `R`, after removing the third kind (step 0, which
uses that `P` is tight), form a path whose image misses the strip (`false_of_spoke`, which uses that
`P` is induced and that no vertex of `N` is on side `B`). So the ends of `Q` are joined in the closed
disc by a connected set that misses the image of the rib vertices of `R`, while the ends alternate
on the frame (`false_of_joinedIn`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V}

/-! ### Lists -/

/-- The first entry of `X ++ y :: Y` lies in `X ++ [y]`. -/
theorem head_mem_of_eq {X Y T : List V} {x y : V} (h : X ++ y :: Y = x :: T) : x ∈ X ++ [y] := by
  rcases X with _ | ⟨x', X⟩
  · simp only [List.nil_append, List.cons.injEq] at h
    simp [h.1]
  · simp only [List.cons_append, List.cons.injEq] at h
    simp [h.1]

/-- The last entry of `X ++ [y]` lies in the part `σ β` of a split `α σ β`. -/
theorem last_mem_of_eq {X α β : List V} {y σ : V} (h : X ++ [y] = α ++ σ :: β) : y ∈ σ :: β := by
  rcases List.eq_nil_or_concat β with rfl | ⟨β', z, rfl⟩
  · have := (List.append_inj' h rfl).2
    simp only [List.cons.injEq, and_true] at this
    simp [this]
  · have h' : X ++ [y] = (α ++ σ :: β') ++ [z] := by rw [h]; simp
    have := (List.append_inj' h' rfl).2
    simp only [List.cons.injEq, and_true] at this
    simp [this]

/-- The list of vertices of a walk between distinct vertices `u`, `v` reads `u m v`. -/
theorem exists_support_eq {u v : V} (p : G.Walk u v) (h : u ≠ v) :
    ∃ m, p.support = u :: m ++ [v] := by
  cases p with
  | nil => exact absurd rfl h
  | cons _ q =>
    refine ⟨q.support.dropLast, ?_⟩
    rw [Walk.support_cons, List.cons_append]
    congr 1
    conv_lhs => rw [← List.dropLast_append_getLast (l := q.support) (by simp)]
    rw [Walk.getLast_support]

/-- In a list without repetition, the entry after `x` is the only entry after `x` adjacent to it. -/
theorem eq_of_isListEdge_next {l₀ l₁ : List V} {x z u : V} (hnd : (l₀ ++ x :: z :: l₁).Nodup)
    (h : IsListEdge (l₀ ++ x :: z :: l₁) u x) (hu : u ∈ z :: l₁) : u = z := by
  obtain ⟨m₀, m₁, h' | h'⟩ := h.exists_split
  · have e : (m₀ ++ [u]) ++ x :: m₁ = l₀ ++ x :: z :: l₁ := by rw [h']; simp
    have := (split_unique e (e ▸ hnd)).1
    rw [List.nodup_append] at hnd
    exact absurd rfl (hnd.2.2 u (by rw [← this]; simp) u (List.mem_cons_of_mem _ hu))
  · have := (split_unique h'.symm (h' ▸ hnd)).2
    simp only [List.cons.injEq] at this
    exact this.1

/-- In a list without repetition, the entry before `z` is the only entry before `z` adjacent to
it. -/
theorem eq_of_isListEdge_prev {l₀ l₁ : List V} {x z u : V} (hnd : (l₀ ++ x :: z :: l₁).Nodup)
    (h : IsListEdge (l₀ ++ x :: z :: l₁) u z) (hu : u ∈ l₀ ++ [x]) : u = x := by
  have e0 : l₀ ++ x :: z :: l₁ = (l₀ ++ [x]) ++ z :: l₁ := by simp
  rw [e0] at hnd h
  obtain ⟨m₀, m₁, h' | h'⟩ := h.exists_split
  · have e : (m₀ ++ [u]) ++ z :: m₁ = (l₀ ++ [x]) ++ z :: l₁ := by rw [h']; simp
    have := (List.append_inj' (split_unique e (e ▸ hnd)).1 rfl).2
    simpa using this
  · have := (split_unique h'.symm (h' ▸ hnd)).2
    rw [List.nodup_append] at hnd
    exact absurd rfl (hnd.2.2 u hu u (by rw [← this]; simp))

/-- Two consecutive entries `u`, `v` of a filtered list come from a stretch `u K v` of the list or
of its reverse whose inner entries are removed. -/
theorem exists_stretch_of_isListEdge_filter {p : V → Bool} {L : List V} {u v : V}
    (h : IsListEdge (L.filter p) u v) :
    ∃ K, ((u :: K ++ [v]) <:+: L ∨ (u :: K ++ [v]) <:+: L.reverse) ∧ ∀ k ∈ K, p k = false := by
  obtain ⟨f₀, f₁, h' | h'⟩ := h.exists_split
  · obtain ⟨L₀, K, L₁, hL, hK⟩ := exists_stretch_of_filter h'
    exact ⟨K, Or.inl ⟨L₀, L₁, by rw [hL]; simp⟩, hK⟩
  · obtain ⟨L₀, K, L₁, hL, hK⟩ := exists_stretch_of_filter h'
    exact ⟨K.reverse, Or.inr ⟨L₁.reverse, L₀.reverse, by rw [hL]; simp⟩,
      fun k hk => hK k (List.mem_reverse.mp hk)⟩

/-- A stretch `u K v` of `l` or of its reverse whose inner entries are removed by a filter gives an
edge of the filtered list. -/
theorem isListEdge_filter_of_infix {p : V → Bool} {l K : List V} {u v : V} (hu : p u = true)
    (hv : p v = true) (hK : ∀ k ∈ K, p k = false)
    (h : (u :: (K ++ [v])) <:+: l ∨ (u :: (K ++ [v])) <:+: l.reverse) :
    IsListEdge (l.filter p) u v := by
  rcases h with ⟨L₀, L₁, he⟩ | ⟨L₀, L₁, he⟩
  · rw [← he, show L₀ ++ u :: (K ++ [v]) ++ L₁ = L₀ ++ u :: K ++ v :: L₁ by simp]
    exact isListEdge_filter hu hv hK
  · have e : l = L₁.reverse ++ v :: K.reverse ++ u :: L₀.reverse := by
      rw [← List.reverse_reverse l, ← he]; simp
    rw [e]
    exact (isListEdge_filter hv hu fun k hk => hK k (List.mem_reverse.mp hk)).symm

/-! ### The strip lemma -/

variable {C A B L₁ N L₂ : List V} {a b y s : V} {k : ℕ} {P : G.Walk a b}

/-- A vertex `y` of `P` on side `B` has a neighbour joined to `B` by a walk that never meets `P`. -/
theorem exists_adj_reachesOff (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) (hyP : y ∈ P.support)
    (hy : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} y) :
    ∃ w, G.Adj y w ∧ ReachesOff G P.support B w := by
  obtain ⟨z, hz, p, hp, hin⟩ := hy
  have hzP : z ∉ P.support := notMem_support_of_arc hCnd hrot hP (Or.inr hz)
  cases p with
  | nil => exact absurd hyP hzP
  | cons hyw p' =>
    refine ⟨_, hyw, z, hz, p', fun v hv hvP => ?_⟩
    have hvy : v ≠ y := fun h => ((Walk.cons_isPath_iff _ _).mp hp).2 (h ▸ hv)
    by_cases hvz : v = z
    · exact hzP (hvz ▸ hvP)
    · exact hin v (by simp [hv]) hvy hvz (Or.inr hvP)

/-- **Step 9: the ends of `Q` are joined off the image of `r`.** Let the rib vertices `M` of a cut
`l` lie between the edges `σ₁σ₀` and `τ₀τ₁` of `l`, with triangles `σ₁σ₀x₀` and `τ₀τ₁x₁` on the side
`F₂`, and let `r` be a path of the rib with no edge at `M` between two triangles on the side `F₂`
(`hZ`). Let `Q` be a `C`-path of `G + ys` through `ys` that misses `r`, where the rib vertices next
to `y` lie on `σ₁σ₀x₀` and those next to `s` on `τ₀τ₁x₁`. Then the ends of `Q` cannot alternate on
the frame with two ends of `r`. The rib vertices of the part of `Q` up to `ys`, the strip, and the
rib vertices of the part after `ys` join the ends of `Q` (`IsRibEmbedding.joinedIn_strip`) in a set
that misses the image of `r` (`false_of_joinedIn`). -/
theorem strip_join {H : SimpleGraph V} {Rw : Set V} {tri : V → Set V} [Finite V]
    (W : WebData H univ C Rw tri) {φ : PlaneEmbedding H Rw} (hφ : φ.IsRibEmbedding C)
    (hCH : IsCycleList H C) (hCR : ∀ x ∈ C, x ∈ Rw) (hGH : G ≤ H) {F₁ F₂ A₁ A₂ : Set ℂ}
    {p q : ℂ} {l : List V} (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hUF : φ.U ⊆ Surface.inner (φ.cycleImage C) ∪ φ.cycleImage C) (hl : IsPathList H Rw l)
    {M : Set V} (hMC : ∀ u ∈ M, u ∉ C) {r : List V} (hr : IsPathList H Rw r)
    (hZ : ∀ σ ∈ M, ∀ w, w ∈ Rw → H.Adj σ w → ¬ IsListEdge l σ w →
      (∀ x, IsTriangleOn H Rw σ w x →
        Surface.inner (φ.cycleImage [σ, w, x]) ⊆ Surface.inner F₂) → ¬ IsListEdge r σ w)
    {σ₀ σ₁ τ₀ τ₁ x₀ x₁ : V} (hσ : IsListEdge l σ₁ σ₀) (hσ₁ : σ₁ ∈ M) (hσ₀ : σ₀ ∉ M)
    (hτ : IsListEdge l τ₀ τ₁)
    (honly : ∀ u v, IsListEdge l u v → u ∈ M → v ∉ M → s(u, v) = s(σ₁, σ₀) ∨ s(u, v) = s(τ₀, τ₁))
    (hx₀ : x₀ ∈ φ.sideTris F₂ σ₁ σ₀) (hx₁ : x₁ ∈ φ.sideTris F₂ τ₀ τ₁) {c₁ c₂ c₃ c₄ : V}
    (Q : (G ⊔ edge y s).Walk c₁ c₂) (hQ : IsTPath (G ⊔ edge y s) C Q) (hQe : s(y, s) ∈ Q.edges)
    (hQr : ∀ x ∈ r, x ∉ Q.support)
    (hendY : ∀ x, x ∈ Rw → (x = y ∨ (y ∉ Rw ∧ x ∈ tri y)) → x ∈ [σ₁, σ₀, x₀])
    (hendS : ∀ x, x ∈ Rw → (x = s ∨ (s ∉ Rw ∧ x ∈ tri s)) → x ∈ [τ₀, τ₁, x₁])
    (hc₃ : c₃ ∈ r) (hc₄ : c₄ ∈ r) (hcd : c₃ ≠ c₄)
    (hcross : PairsCrossOn (φ.cycleImage C) (φ.pt c₁) (φ.pt c₂) (φ.pt c₃) (φ.pt c₄)) : False := by
  classical
  set pR : V → Bool := fun x => decide (x ∈ Rw) with hpR
  have hpRt : ∀ {x}, x ∈ Rw → pR x = true := fun h => by simp [hpR, h]
  -- The two parts of `Q` before and after the edge `ys`.
  obtain ⟨u₀, v₀, X₁, X₂, hQs, huv₀⟩ : ∃ u₀ v₀ X₁ X₂, Q.support = X₁ ++ u₀ :: v₀ :: X₂ ∧
      ((u₀ = y ∧ v₀ = s) ∨ (u₀ = s ∧ v₀ = y)) := by
    obtain ⟨X₁, X₂, h | h⟩ := Walk.exists_split_of_mem_edges hQe
    exacts [⟨y, s, X₁, X₂, h, Or.inl ⟨rfl, rfl⟩⟩, ⟨s, y, X₁, X₂, h, Or.inr ⟨rfl, rfl⟩⟩]
  have hedge : edge y s = edge u₀ v₀ := by
    rcases huv₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact edge_comm ..
  have hQc : Q.support.IsChain (G ⊔ edge u₀ v₀).Adj := by
    rw [← hedge]; exact Q.isChain_adj_support
  have hQnd : ((X₁ ++ [u₀]) ++ v₀ :: X₂).Nodup := by
    have := hQ.1.support_nodup
    rw [hQs] at this
    simpa using this
  obtain ⟨hnd₁, hnd₂, hdisj₁₂⟩ := List.nodup_append.mp hQnd
  have hc₁' : (X₁ ++ [u₀]).IsChain G.Adj :=
    isChain_of_sup_edge (hQc.infix ⟨[], v₀ :: X₂, by rw [hQs]; simp⟩)
      (fun h => hdisj₁₂ v₀ h v₀ List.mem_cons_self rfl)
  have hc₂' : (v₀ :: X₂).IsChain G.Adj :=
    isChain_of_sup_edge (u := v₀) (v := u₀)
      (by rw [edge_comm]; exact hQc.infix ⟨X₁ ++ [u₀], [], by rw [hQs]; simp⟩)
      (fun h => hdisj₁₂ u₀ (by simp) u₀ h rfl)
  set q₁ := (X₁ ++ [u₀]).filter pR with hq₁_def
  set q₂ := (v₀ :: X₂).filter pR with hq₂_def
  have hq₁ : IsPathList H Rw q₁ := W.isPathList_filter (hc₁'.imp fun _ _ h => hGH h) hnd₁
  have hq₂ : IsPathList H Rw q₂ := W.isPathList_filter (hc₂'.imp fun _ _ h => hGH h) hnd₂
  have hQm₁ : ∀ x ∈ q₁, x ∈ Q.support := fun x hx => by
    have := List.mem_of_mem_filter hx
    rw [hQs]; simp only [List.mem_append, List.mem_cons] at this ⊢; tauto
  have hQm₂ : ∀ x ∈ q₂, x ∈ Q.support := fun x hx => by
    have := List.mem_of_mem_filter hx
    rw [hQs]; simp only [List.mem_append, List.mem_cons] at this ⊢; tauto
  have hq₁r : q₁.Disjoint r := fun x h1 h2 => hQr x h2 (hQm₁ x h1)
  have hq₂r : q₂.Disjoint r := fun x h1 h2 => hQr x h2 (hQm₂ x h1)
  have hc₁m : c₁ ∈ X₁ ++ [u₀] :=
    head_mem_of_eq (Y := v₀ :: X₂) (T := Q.support.tail) (by rw [← hQs, Walk.cons_tail_support])
  have hc₂m : c₂ ∈ v₀ :: X₂ := by
    have e : X₂.reverse ++ v₀ :: (u₀ :: X₁.reverse) = c₂ :: Q.reverse.support.tail := by
      rw [Walk.cons_tail_support, Walk.support_reverse, hQs]; simp
    have := head_mem_of_eq e
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at this
    rcases this with h | h
    · exact List.mem_cons_of_mem _ h
    · exact h ▸ List.mem_cons_self
  have hc₁R : c₁ ∈ Rw := hCR c₁ hQ.2.1
  have hc₂R : c₂ ∈ Rw := hCR c₂ hQ.2.2.1
  have hc₁q : c₁ ∈ q₁ := List.mem_filter.mpr ⟨hc₁m, hpRt hc₁R⟩
  have hc₂q : c₂ ∈ q₂ := List.mem_filter.mpr ⟨hc₂m, hpRt hc₂R⟩
  -- The last rib vertex `e₁` before `ys`, and the first one `e₂` after it.
  obtain ⟨α, e₁, β, he₁, he₁R, he₁u⟩ := W.exists_rib_near (w := u₀) (L := X₁.reverse)
    (by
      have := List.isChain_reverse.mpr (hc₁'.imp fun _ _ h => (hGH h).symm)
      simpa using this)
    ⟨c₁, by simp only [List.mem_append, List.mem_singleton] at hc₁m; simp; tauto, hc₁R⟩
  have he₁q : e₁ ∈ q₁ := by
    have : e₁ ∈ u₀ :: X₁.reverse := by rw [he₁]; simp
    refine List.mem_filter.mpr ⟨?_, hpRt he₁R⟩
    simp only [List.mem_cons, List.mem_reverse] at this
    simp only [List.mem_append, List.mem_singleton]
    tauto
  obtain ⟨α', e₂, β', he₂, he₂R, he₂v⟩ := W.exists_rib_near (w := v₀) (L := X₂)
    (hc₂'.imp fun _ _ h => hGH h) ⟨c₂, hc₂m, hc₂R⟩
  have he₂q : e₂ ∈ q₂ := List.mem_filter.mpr ⟨by rw [he₂]; simp, hpRt he₂R⟩
  -- Step 9: the ends of `Q` are joined off the image of `r`.
  set S := (φ.pathImage q₁ ∪ φ.pt '' {x | x ∈ q₁}) ∪ (φ.pathImage q₂ ∪ φ.pt '' {x | x ∈ q₂}) ∪
    φ.stripSet F₂ (φ.pathImage r) with hS_def
  have hT₀ : IsTriangleOn H Rw σ₁ σ₀ x₀ := hx₀.1
  have hT₁ : IsTriangleOn H Rw τ₀ τ₁ x₁ := hx₁.1
  have hstrip : ∀ {e e' : V}, e ∈ [σ₁, σ₀, x₀] → e' ∈ [τ₀, τ₁, x₁] → e ∉ r → e' ∉ r →
      JoinedIn S (φ.pt e) (φ.pt e') := by
    intro e e' he he' her he'r
    refine (hφ.joinedIn_strip hCH hCR hθ hl hMC hr hZ hσ hσ₁ hσ₀ hτ honly hx₀ hx₁ ?_ ?_).mono
      subset_union_right
    · exact Or.inr ⟨φ.pt_mem_cycleImage hT₀.isCycleList hT₀.mem he,
        fun h => her (φ.mem_of_pt_mem_pathImage hr (hT₀.mem e he) h)⟩
    · exact Or.inr ⟨φ.pt_mem_cycleImage hT₁.isCycleList hT₁.mem he',
        fun h => he'r (φ.mem_of_pt_mem_pathImage hr (hT₁.mem e' he') h)⟩
  have he₁r : e₁ ∉ r := fun h => hq₁r he₁q h
  have he₂r : e₂ ∉ r := fun h => hq₂r he₂q h
  have J1 : JoinedIn S (φ.pt c₁) (φ.pt e₁) :=
    (joinedIn_pts (φ := φ) hq₁ hc₁q he₁q).mono (subset_union_left.trans subset_union_left)
  have J3 : JoinedIn S (φ.pt e₂) (φ.pt c₂) :=
    (joinedIn_pts (φ := φ) hq₂ he₂q hc₂q).mono (subset_union_right.trans subset_union_left)
  have J2 : JoinedIn S (φ.pt e₁) (φ.pt e₂) := by
    rcases huv₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hstrip (hendY e₁ he₁R (h1 ▸ he₁u)) (hendS e₂ he₂R (h2 ▸ he₂v)) he₁r he₂r
    · exact (hstrip (hendY e₂ he₂R (h2 ▸ he₂v)) (hendS e₁ he₁R (h1 ▸ he₁u)) he₂r he₁r).symm
  have hS : S ⊆ Surface.inner (φ.cycleImage C) ∪ φ.cycleImage C :=
    union_subset (union_subset ((pts_subset_U hq₁).trans hUF) ((pts_subset_U hq₂).trans hUF))
      (hφ.stripSet_subset hCH hCR hUF _)
  have hSr : Disjoint S (φ.pathImage r) :=
    Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
      ⟨disjoint_pts hq₁ hr hq₁r, disjoint_pts hq₂ hr hq₂r⟩,
      hφ.disjoint_stripSet (φ.pathImage_subset_U hr)⟩
  exact false_of_joinedIn hCH hCR hUF hS (J1.trans (J2.trans J3)) hr hc₃ hc₄ hcd hSr hcross

/-- **The strip lemma.** Let `P` be an induced and tight `C`-path from `a` to `b`, with vertex list
`L₁ y N s L₂`, let `y` and `s` be on side `B`, and let no vertex of `N` be on side `B`. Then the edge
`ys` is safe. -/
theorem strip_safe [Finite V] (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (htight : IsTight G C A B P.support)
    (hy : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} y)
    (hs : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} s)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) :
    IsSafe G (edge y s) C := by
  classical
  intro hc
  by_contra hG
  have hCnd : C.Nodup := hC.2.1
  have hnd : P.support.Nodup := hP.1.support_nodup
  have hndL : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hnd
  have hyP : y ∈ P.support := by rw [hsupp]; simp
  have hsP : s ∈ P.support := by rw [hsupp]; simp
  have hys : y ≠ s := (List.nodup_append.mp hndL).2.2 y (by simp) s (by simp)
  -- If `A` is empty, no vertex is on side `A`, and Claim 5.5 applies.
  by_cases hA : A = []
  · refine hG (claim_5_5_tight hrot hP hsupp hind htight (fun v hv => ⟨?_, hN v hv⟩) hc)
    rintro ⟨z, hz, -⟩
    simp [hA] at hz
  -- The arcs `A` and `B`.
  have hndC : (a :: A ++ b :: B).Nodup := hrot ▸ List.nodup_rotate.mpr hCnd
  have hBne : B ≠ [] := by
    obtain ⟨z, hz, -⟩ := hy
    rintro rfl
    simp at hz
  have hab : ¬ IsCycleEdge C a b := by
    rw [← isCycleEdge_rotate C k, hrot, isCycleEdge_cons_append_cons_iff hndC]
    rintro (h | h)
    exacts [hA h, hBne h]
  have hndC' := hndC
  rw [List.cons_append, List.nodup_cons, List.nodup_append, List.nodup_cons] at hndC'
  have hab' : a ≠ b := fun h => hndC'.1 (List.mem_append_right _ (h ▸ List.mem_cons_self))
  have hAB : ∀ t, t ∈ A ∨ t ∈ B → t ∈ C ∧ t ≠ a ∧ t ≠ b := by
    rintro t (ht | ht)
    · exact ⟨List.mem_rotate.mp (by rw [hrot]; simp [ht]),
        fun h => hndC'.1 (List.mem_append_left _ (h ▸ ht)),
        hndC'.2.2.2 t ht b List.mem_cons_self⟩
    · exact ⟨List.mem_rotate.mp (by rw [hrot]; simp [ht]),
        fun h => hndC'.1 (List.mem_append_right _ (List.mem_cons_of_mem _ (h ▸ ht))),
        fun h => hndC'.2.2.1.1 (h ▸ ht)⟩
  -- Step 2: the web.
  obtain ⟨H, hGH, hmax⟩ := exists_maxCrosslessOn (S := univ) (fun _ _ _ => trivial) hG
  obtain ⟨Rw, tri, W⟩ :=
    (lemma_4_3_on _ H univ C rfl (IsCycleList.mono hC hGH) (fun _ _ => trivial) hmax).exists_webData
  obtain ⟨hCH, hCR, φ, hφ⟩ := W.rib
  have hHys : ¬ H.Adj y s := fun h =>
    hmax.2.1 (IsCrossed.mono hc (sup_le hGH fun u v huv => by
      rw [edge_adj] at huv
      rcases huv.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [h, h.symm]))
  -- The crossing in `G + ys`.
  rcases isCrossed_sup_edge_cases' hc with h | ⟨c₁, c₂, c₃, c₄, Q, R, halt, hQ, hQe, hR, hdisj⟩
  · exact hG h
  have hyQ : y ∈ Q.support := Q.fst_mem_support_of_mem_edges hQe
  have hsQ : s ∈ Q.support := Q.snd_mem_support_of_mem_edges hQe
  -- Step 4: the cut `l`, the rib vertices of `P`.
  set pR : V → Bool := fun x => decide (x ∈ Rw) with hpR
  have hPH : P.support.IsChain H.Adj := P.isChain_adj_support.imp fun _ _ h => hGH h
  obtain ⟨mid, hmid⟩ := exists_support_eq P hab'
  have haR : a ∈ Rw := hCR a (List.mem_rotate.mp (by rw [hrot]; simp))
  have hbR : b ∈ Rw := hCR b (List.mem_rotate.mp (by rw [hrot]; simp))
  have hlm : P.support.filter pR = a :: mid.filter pR ++ [b] := by
    rw [hmid]; simp [List.filter_append, hpR, haR, hbR]
  set l := a :: mid.filter pR ++ [b] with hl_def
  have hl : IsPathList H Rw l := hlm ▸ W.isPathList_filter hPH hnd
  have hmC : ∀ v ∈ mid.filter pR, v ∉ C := by
    intro v hv
    have hvmid : v ∈ mid := List.mem_of_mem_filter hv
    have hndm : (a :: mid ++ [b]).Nodup := hmid ▸ hnd
    rw [List.nodup_append] at hndm
    have hva : v ≠ a := fun h => (List.nodup_cons.mp hndm.1).1 (h ▸ hvmid)
    have hvb : v ≠ b := hndm.2.2 v (List.mem_cons_of_mem _ hvmid) b (List.mem_singleton_self _)
    exact (hP.2.2.2 v (by rw [hmid]; simp [hvmid]) hva hvb).1
  obtain ⟨hθ, hUF, -, -, -, -, -, -, hPA, hPB⟩ := hφ.theta hCH hCR hrot hab hl hmC
  have hlL : ∀ v ∈ l, v ∈ P.support := fun v hv => List.mem_of_mem_filter (hlm ▸ hv)
  have hptne : ∀ t, t ∈ A ∨ t ∈ B → t ∈ Rw ∧ φ.pt t ∉ ({φ.pt a, φ.pt b} : Set ℂ) := by
    intro t ht
    obtain ⟨htC, hta, htb⟩ := hAB t ht
    refine ⟨hCR t htC, ?_⟩
    rintro (h | h)
    · exact hta (φ.injOn (hCR t htC) haR h)
    · exact htb (φ.injOn (hCR t htC) hbR h)
  have hTA : ∀ t ∈ A, t ∈ Rw ∧ φ.pt t ∈ φ.pathImage (a :: A ++ [b]) \ {φ.pt a, φ.pt b} :=
    fun t ht => ⟨(hptne t (Or.inl ht)).1,
      φ.pt_mem_pathImage hPA (by simp) (by simp [ht]), (hptne t (Or.inl ht)).2⟩
  have hTB : ∀ t ∈ B, t ∈ Rw ∧ φ.pt t ∈ φ.pathImage (b :: B ++ [a]) \ {φ.pt a, φ.pt b} :=
    fun t ht => ⟨(hptne t (Or.inr ht)).1,
      φ.pt_mem_pathImage hPB (by simp) (by simp [ht]), (hptne t (Or.inr ht)).2⟩
  -- The last rib vertex `σ₀` up to `y`, and the first one `τ₁` from `s` on.
  have e0 := hsupp.symm.trans hmid
  have haL : a ∈ L₁ ++ [y] := head_mem_of_eq (Y := N ++ s :: L₂) (T := mid ++ [b]) (by simpa using e0)
  have hbL : b ∈ s :: L₂ := by
    have e' := congrArg List.reverse e0
    have := head_mem_of_eq (X := L₂.reverse) (y := s) (Y := N.reverse ++ y :: L₁.reverse)
      (T := mid.reverse ++ [a]) (by simpa using e')
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at this
    rcases this with h | h
    · exact List.mem_cons_of_mem _ h
    · exact h ▸ List.mem_cons_self
  obtain ⟨α₀, σ₀, β₀, h1, hσ₀R, hβ₀⟩ := exists_last_mem (Z := Rw) (L₁ ++ [y]) ⟨a, haL, haR⟩
  obtain ⟨α₁, τ₁, β₁, h4, hτ₁R, hα₁⟩ := exists_first_mem (Z := Rw) (s :: L₂) ⟨b, hbL, hbR⟩
  have hyσ : y ∈ σ₀ :: β₀ := last_mem_of_eq h1
  have hsτ : s ∈ α₁ ++ [τ₁] := head_mem_of_eq h4.symm
  have hsupp' : P.support = α₀ ++ σ₀ :: (β₀ ++ N ++ α₁) ++ τ₁ :: β₁ := by
    rw [hsupp, show L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ [y]) ++ N ++ (s :: L₂) by simp, h1, h4]
    simp
  -- If `N` has no rib vertex, `y` and `s` are on one stretch through a clique.
  by_cases hNR : ∃ w ∈ N, w ∈ Rw
  swap
  · push Not at hNR
    have hinf : (σ₀ :: (β₀ ++ N ++ α₁) ++ [τ₁]) <:+: P.support :=
      ⟨α₀, β₁, by rw [hsupp']; simp⟩
    refine hHys (W.adj_of_mem_stretch (hPH.infix hinf) (hnd.sublist hinf.sublist) hσ₀R hτ₁R
      (fun x hx => ?_) ?_ ?_ hys)
    · simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      exacts [hβ₀ x hx, hNR x hx, hα₁ x hx]
    · simp only [List.mem_cons] at hyσ
      rcases hyσ with h | h
      · simp [h]
      · simp [h]
    · simp only [List.mem_append, List.mem_singleton] at hsτ
      rcases hsτ with h | h
      · simp [h]
      · simp [h]
  obtain ⟨γ, σ₁, δ, h2, hσ₁R, hγ⟩ := exists_first_mem (Z := Rw) N hNR
  obtain ⟨γ', τ₀, δ', h3, hτ₀R, hδ'⟩ := exists_last_mem (Z := Rw) N hNR
  have E1 : P.support = α₀ ++ σ₀ :: (β₀ ++ γ) ++ σ₁ :: (δ ++ α₁ ++ τ₁ :: β₁) := by
    rw [hsupp', h2]; simp
  have E2 : P.support = (α₀ ++ σ₀ :: (β₀ ++ γ')) ++ τ₀ :: (δ' ++ α₁) ++ τ₁ :: β₁ := by
    rw [hsupp', h3]; simp
  have hβγ : ∀ x ∈ β₀ ++ γ, x ∉ Rw := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    exacts [hβ₀ x h, hγ x h]
  have hδα : ∀ x ∈ δ' ++ α₁, x ∉ Rw := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    exacts [hδ' x h, hα₁ x h]
  have hpRf : ∀ {x}, x ∉ Rw → pR x = false := fun h => by simp [hpR, h]
  have hpRt : ∀ {x}, x ∈ Rw → pR x = true := fun h => by simp [hpR, h]
  have hσ : IsListEdge l σ₁ σ₀ := by
    rw [← hlm, E1]
    exact (isListEdge_filter (hpRt hσ₀R) (hpRt hσ₁R) fun k hk => hpRf (hβγ k hk)).symm
  have hτ : IsListEdge l τ₀ τ₁ := by
    rw [← hlm, E2]
    exact isListEdge_filter (hpRt hτ₀R) (hpRt hτ₁R) fun k hk => hpRf (hδα k hk)
  -- The rib vertices `Mf` of `N`.
  have hnil : ∀ {X : List V}, (∀ x ∈ X, x ∉ Rw) → X.filter pR = [] :=
    fun h => List.filter_eq_nil_iff.mpr fun x hx => by simp [hpR, h x hx]
  set Mf := N.filter pR with hMf
  have hlsplit : l = α₀.filter pR ++ σ₀ :: Mf ++ τ₁ :: β₁.filter pR := by
    rw [← hlm, hsupp']
    simp [List.filter_append, hpRt hσ₀R, hpRt hτ₁R, hnil hβ₀, hnil hα₁, hMf]
  have hMf1 : Mf = σ₁ :: δ.filter pR := by
    rw [hMf, h2]; simp [List.filter_append, hnil hγ, hpRt hσ₁R]
  have hMf2 : Mf = γ'.filter pR ++ [τ₀] := by
    rw [hMf, h3]; simp [List.filter_append, hnil hδ', hpRt hτ₀R]
  have hlnd : (α₀.filter pR ++ σ₀ :: Mf ++ τ₁ :: β₁.filter pR).Nodup := hlsplit ▸ hl.1
  have hσ₁M : σ₁ ∈ Mf := by rw [hMf1]; exact List.mem_cons_self
  have hτ₀M : τ₀ ∈ Mf := by rw [hMf2]; simp
  have hσ₀M : σ₀ ∉ Mf := by
    have := (List.nodup_append.mp (List.nodup_append.mp hlnd).1).2.1
    exact (List.nodup_cons.mp this).1
  have hMC : ∀ u ∈ {x | x ∈ Mf}, u ∉ C := fun u hu =>
    not_mem_C_of_mem_window hP hsupp (List.mem_of_mem_filter hu)
  have hMR : ∀ u ∈ Mf, u ∈ Rw := fun u hu => of_decide_eq_true (List.mem_filter.mp hu).2
  have honly : ∀ u v, IsListEdge l u v → u ∈ {x | x ∈ Mf} → v ∉ {x | x ∈ Mf} →
      s(u, v) = s(σ₁, σ₀) ∨ s(u, v) = s(τ₀, τ₁) := by
    intro u v huv hu hv
    rw [hlsplit] at huv
    have hw := huv.mem_window hlnd hu
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | hw | rfl
    · left
      have e : α₀.filter pR ++ v :: Mf ++ τ₁ :: β₁.filter pR =
          α₀.filter pR ++ v :: σ₁ :: (δ.filter pR ++ τ₁ :: β₁.filter pR) := by
        rw [hMf1]; simp
      rw [e] at huv hlnd
      rw [eq_of_isListEdge_next hlnd huv (by
        have : u ∈ σ₁ :: δ.filter pR := hMf1 ▸ hu
        simp only [List.mem_cons, List.mem_append] at this ⊢
        tauto)]
    · exact absurd hw hv
    · right
      have e : α₀.filter pR ++ σ₀ :: Mf ++ v :: β₁.filter pR =
          (α₀.filter pR ++ σ₀ :: γ'.filter pR) ++ τ₀ :: v :: β₁.filter pR := by
        rw [hMf2]; simp
      rw [e] at huv hlnd
      rw [eq_of_isListEdge_prev hlnd huv (by
        have : u ∈ γ'.filter pR ++ [τ₀] := hMf2 ▸ hu
        simp only [List.mem_append, List.mem_singleton] at this ⊢
        simp only [List.mem_cons]
        tauto)]
  -- The triangles at the two ends of the strip, on the side of `B`.
  obtain ⟨x₀, hx₀⟩ := hφ.sideTris_eq_one hCH hCR hθ hl (hMC σ₁ hσ₁M) hσ
  obtain ⟨x₁, hx₁⟩ := hφ.sideTris_eq_one hCH hCR hθ hl (hMC τ₀ hτ₀M) hτ
  set F₂ := φ.cycleImage (b :: B ++ a :: mid.filter pR) with hF₂
  have hx₀m : x₀ ∈ φ.sideTris F₂ σ₁ σ₀ := by rw [hx₀]; rfl
  have hx₁m : x₁ ∈ φ.sideTris F₂ τ₀ τ₁ := by rw [hx₁]; rfl
  -- Step 6: the rib vertices on the triangles of `y` and `s`.
  have hend : ∀ {z u v t : V} {K : List V}, z ∈ K → (u :: K ++ [v]) <:+: P.support →
      (∀ x ∈ K, x ∉ Rw) → u ∈ Rw → v ∈ Rw →
      IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} z → φ.sideTris F₂ u v = {t} →
      ∀ x, x ∈ Rw → x ∈ tri z → x = u ∨ x = v ∨ x = t := by
    intro z u v t K hzK hinf hK hu hv hz ht x hxR hxz
    have hzP : z ∈ P.support := hinf.subset (by simp [hzK])
    obtain ⟨w, hzw, hw⟩ := exists_adj_reachesOff hCnd hrot hP hzP hz
    obtain ⟨x', hx'R, hx'w, hfar⟩ := far_of_reachesOff W hθ.symm hUF hl hlL hTB (hw.mono hGH)
    obtain ⟨t', ht', htri⟩ := end_tri W hφ hCH hCR hθ hl (hPH.infix hinf)
      (hnd.sublist hinf.sublist) hu hv hK hzK (hGH hzw) hx'R hx'w hfar
    rw [ht] at ht'
    rw [htri, Set.mem_singleton_iff.mp ht'] at hxz
    simpa only [mem_insert_iff, mem_singleton_iff] using hxz
  have hendY : ∀ x, x ∈ Rw → (x = y ∨ (y ∉ Rw ∧ x ∈ tri y)) → x ∈ [σ₁, σ₀, x₀] := by
    rintro x hxR (hxy | ⟨hyR, hxy⟩)
    · rcases List.mem_cons.mp hyσ with h | h
      · simp [hxy, h]
      · exact absurd (hxy ▸ hxR) (hβ₀ y h)
    · have hyβ : y ∈ β₀ := (List.mem_cons.mp hyσ).resolve_left fun h => hyR (h ▸ hσ₀R)
      have := hend (z := y) (K := β₀ ++ γ) (by simp [hyβ])
        ⟨α₀, δ ++ α₁ ++ τ₁ :: β₁, by rw [E1]; simp⟩ hβγ hσ₀R hσ₁R hy
        ((φ.sideTris_comm F₂ σ₀ σ₁).trans hx₀) x hxR hxy
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      tauto
  have hendS : ∀ x, x ∈ Rw → (x = s ∨ (s ∉ Rw ∧ x ∈ tri s)) → x ∈ [τ₀, τ₁, x₁] := by
    rintro x hxR (hxs | ⟨hsR, hxs⟩)
    · rcases List.mem_append.mp hsτ with h | h
      · exact absurd (hxs ▸ hxR) (hα₁ s h)
      · simp [hxs, List.mem_singleton.mp h]
    · have hsα : s ∈ α₁ := by
        rcases List.mem_append.mp hsτ with h | h
        · exact h
        · exact absurd (List.mem_singleton.mp h ▸ hτ₁R) hsR
      have := hend (z := s) (K := δ' ++ α₁) (by simp [hsα])
        ⟨α₀ ++ σ₀ :: (β₀ ++ γ'), β₁, by rw [E2]; simp⟩ hδα hτ₀R hτ₁R hs hx₁ x hxR hxs
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      tauto
  -- Step 0: the rib vertices `r` of `R`, after removing the third kind.
  set Lr := R.support.filter fun u => !decide (IsThirdKind G C A B P.support u) with hLr
  have hLrc : Lr.IsChain G.Adj := isChain_filter_thirdKind hrot htight le_rfl
    (fun _ _ h _ => h) R.isChain_adj_support hR.1.support_nodup
  have hLrnd : Lr.Nodup := hR.1.support_nodup.filter _
  have hLrR : ∀ x ∈ Lr, x ∈ R.support ∧ ¬ IsThirdKind G C A B P.support x := fun x hx => by
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hx
    exact ⟨h1, by simpa using h2⟩
  set r := Lr.filter pR with hr_def
  have hr : IsPathList H Rw r := W.isPathList_filter (hLrc.imp fun _ _ h => hGH h) hLrnd
  have hrR : ∀ x ∈ r, x ∈ R.support := fun x hx => (hLrR x (List.mem_of_mem_filter hx)).1
  have hmemr : ∀ x, x ∈ R.support → x ∈ C → x ∈ r := fun x hx hxC =>
    List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hx, by simp [IsThirdKind, hxC]⟩, hpRt (hCR x hxC)⟩
  have hc₃ : c₃ ∈ r := hmemr c₃ R.start_mem_support hR.2.1
  have hc₄ : c₄ ∈ r := hmemr c₄ R.end_mem_support hR.2.2.1
  -- Step 8: no edge of `r` at the strip runs between two triangles on the side of `B`.
  have hZ : ∀ σ ∈ {x | x ∈ Mf}, ∀ w, w ∈ Rw → H.Adj σ w → ¬ IsListEdge l σ w →
      (∀ x, IsTriangleOn H Rw σ w x →
        Surface.inner (φ.cycleImage [σ, w, x]) ⊆ Surface.inner F₂) →
      ¬ IsListEdge r σ w := by
    intro σ hσM w hwR hadj hnl hall hrl
    obtain ⟨K, hinf, hK⟩ := exists_stretch_of_isListEdge_filter hrl
    have hKR : ∀ k ∈ K, k ∉ Rw := fun k hk h => absurd (hK k hk) (by rw [hpRt h]; decide)
    obtain ⟨hsc, hsnd, hsmem⟩ : (σ :: K ++ [w]).IsChain G.Adj ∧ (σ :: K ++ [w]).Nodup ∧
        ∀ x ∈ σ :: K ++ [w], x ∈ Lr := by
      rcases hinf with h | h
      · exact ⟨hLrc.infix h, hLrnd.sublist h.sublist, fun x hx => h.subset hx⟩
      · exact ⟨(List.isChain_reverse.mpr (hLrc.imp fun _ _ h => h.symm)).infix h,
          (List.nodup_reverse.mpr hLrnd).sublist h.sublist,
          fun x hx => List.mem_reverse.mp (h.subset hx)⟩
    have hT' : ∀ x ∈ K ++ [w], ¬ IsThirdKind G C A B P.support x ∧ x ≠ y ∧ x ≠ s := by
      intro x hx
      have hxL := hLrR x (hsmem x (by simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto))
      exact ⟨hxL.2, fun h => hdisj hyQ (h ▸ hxL.1), fun h => hdisj hsQ (h ▸ hxL.1)⟩
    have hσN : σ ∈ N := List.mem_of_mem_filter hσM
    rcases stretch_infix hCnd hrot hP hsupp hind hN hσN (by simpa using hsc)
      (by simpa using hsnd) hT' with ⟨x, hx, hxA⟩ | hPinf
    · obtain ⟨x', hx'R, hxx', hfar⟩ := far_of_reachesOff W hθ hUF hl hlL hTA (hxA.mono hGH)
      exact false_of_spoke W hφ hCH hCR hθ (hMC σ hσM) (hMR σ hσM) hwR hadj hall
        (hsc.imp fun _ _ h => hGH h) hsnd hKR hx hx'R hxx' hfar
    · apply hnl
      rw [← hlm]
      exact isListEdge_filter_of_infix (hpRt (hMR σ hσM)) (hpRt hwR) hK hPinf
  exact strip_join W hφ hCH hCR hGH hθ hUF hl hMC hr hZ hσ hσ₁M hσ₀M hτ honly hx₀m hx₁m Q hQ hQe
    (fun x hx hxQ => hdisj hxQ (hrR x hx)) hendY hendS hc₃ hc₄ (halt.ne hCnd)
    (pairsCrossOn_of_alternate φ hCH hCR halt)

/-- **Lemma 5.4 for induced, tight paths** (Humeau and Pous, page 19): "Then the edge $y_jy_s$ is
safe, and in the graph $G+y_jy_s$, all vertices of $Py_jy_s$ lie on both $Py_jy_sP$-sides." Here
`P.support = L₁ ++ y :: N ++ s :: L₂` with `y = y_j` and `s = y_s`, and `B` is the side of `y_s`.
The vertices of `Py_j` are on both sides; no vertex of `N` is on side `B`, by the choice of `r` and
`s`; and `y_s` is on side `B`, while `y_s` or some `y_r` in `N` is on side `A`. The safety is the
strip lemma (`strip_safe`), since `y_j` is on side `B`; the sides are `lemma_5_4_sides`. -/
theorem lemma_5_4_tight [Finite V] (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (htight : IsTight G C A B P.support)
    (hpre : ∀ v ∈ L₁ ++ [y], IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hsA : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} s ∨
      ∃ r ∈ N, IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} r)
    (hsB : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} s) :
    IsSafe G (edge y s) C ∧ ∃ P' : (G ⊔ edge y s).Walk a b, IsTPath (G ⊔ edge y s) C P' ∧
      P'.support = L₁ ++ y :: s :: L₂ ∧
      ∀ v ∈ L₁ ++ [y, s],
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ B} v :=
  ⟨strip_safe hC hrot hP hsupp hind htight (hpre y (by simp)).2 hsB hN,
    lemma_5_4_sides hrot hP hsupp hpre hsA (Or.inl hsB)⟩

end GraphMinor.HP25
