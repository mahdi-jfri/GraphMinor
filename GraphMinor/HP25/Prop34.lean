module

public import GraphMinor.HP25.Prop34Tools
import GraphMinor.HP25.Prop22
import GraphMinor.HP25.Prop23
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Proposition 3.4: edge decompositions

Humeau and Pous, arXiv:2505.16431v2, Proposition 3.4 (page 10). "Let $G$ be a web with frame $C$.
The following holds:
1. $G$ is the edge composition of two webs if and only if there is a pair of vertices of $G$ which
are not $C$-connected.
2. for all vertices $x,y$, either $x$ is $C$-connected to $y$, or there exists a pair of vertices
$c,c'\in C-x-y$ separating $x$ from $y$ and such that $G$ is the edge composition of two webs along
$cc'$,
3. for every vertex $x$ and every subpath $P$ of $C$, either $x$ is $C$-connected to $P$, or there
are vertices $c,c'$ of $C-P-x$ separating $x$ from $P$ and such that $G$ is the edge composition of
two webs along $cc'$."

## The proof, and where it departs from the paper

The paper proves item 2 with Lemma 3.3 and crossings: it takes the frame vertices `c_x`, `c_x'` of
Lemma 3.3, shows that the frame vertices `C`-connected to `y` lie on one of the two arcs `P` of `C`
between them, takes `P` of minimum length, and then argues on a plane embedding ("Without being too
formal on the manipulation of such embeddings, the green area must correspond to an inner face of
the embedding, meaning a triangle"). The step "Since $x$ is not $C$-connected to $\mathring{P}$" is
not justified by the minimality of `P`: when `x` is `C`-connected to a vertex `v` inside `P`, and the
frame vertices `C`-connected to `y` are only the ends of `P` and `v`, no shorter arc and no crossing
is available. Excluding this case needs planarity beyond crossings.

We prove items 2 and 3 together, for a vertex `x` and a set `Z` of vertices that induces a connected
subgraph (`Z = {y}`, or the vertices of a subpath of `C`), by induction on the length of the frame:
* if `|C| = 3`, the web is a clique (Proposition 2.2), so `x` is adjacent to `Z`;
* if no two non-consecutive vertices of `C` are adjacent, all vertices are `C`-connected: the
  vertices off the frame are connected (`IsRibOn.no_chord`, from the fans of Proposition 2.3);
* otherwise a chord `cc'` splits the web into two webs (`WebData.split`, the plane argument of the
  paper). If `x` and `Z` lie on different sides, `{c, c'}` separates them. Otherwise we use the
  induction hypothesis on the side that holds `x` and meets `Z`; a walk that avoids the separating
  pair of that side can be folded back into the side (`reach_side`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V}

/-! ### Small facts -/

theorem restrict_le (G : SimpleGraph V) (X : Set V) : restrict G X ≤ G := fun _ _ h => h.1

/-- A walk of a graph with vertex set `S` that starts in `S` stays in `S`. -/
theorem mem_of_support_supported {S : Set V} (hs : IsSupportedOn G S) :
    ∀ {u v : V} (p : G.Walk u v), u ∈ S → ∀ w ∈ p.support, w ∈ S
  | _, _, .nil, hu, w, hw => by simp at hw; rw [hw]; exact hu
  | _, _, .cons h p, hu, w, hw => by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hu
    · exact mem_of_support_supported hs p (hs h.symm) w hw

/-- A walk of length at most one from `v` to `w`, when `w = v` or `vw` is an edge. -/
theorem exists_short_walk {v w : V} (h : w = v ∨ G.Adj v w) :
    ∃ p : G.Walk v w, ∀ u ∈ p.support, u = v ∨ u = w := by
  rcases h with rfl | h
  · exact ⟨.nil, fun u hu => by simp at hu; exact Or.inl hu⟩
  · exact ⟨h.toWalk, fun u hu => by simpa using hu⟩

/-- The vertices of the frame of a web are vertices of the web. -/
theorem IsWebOn.frame_subset {S : Set V} {C : List V} (h : IsWebOn G S C) : ∀ v ∈ C, v ∈ S := by
  obtain ⟨-, R, tri, hRS, hrib, -⟩ := h
  exact fun v hv => hRS (hrib.2.1 v hv)

/-! ### Webs without chords -/

namespace WebData

variable {S : Set V} {C : List V} {R : Set V} {tri : V → Set V}

/-- **Webs without chords.** In a web whose frame has at least four vertices and no chord, any two
vertices are `C`-connected. -/
theorem connected_of_no_chord (W : WebData G S C R tri) (h4 : 4 ≤ C.length)
    (hnc : ∀ u ∈ C, ∀ v ∈ C, G.Adj u v → IsCycleEdge C u v) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    IsConnectedAvoiding G {z | z ∈ C} x {y} := by
  classical
  have hC := W.rib.1
  obtain ⟨hnbr, hreach⟩ := W.rib.no_chord h4 hnc
  set I := {w | w ∈ R ∧ w ∉ C} with hI
  -- every vertex is an inner rib vertex or is adjacent to one
  have hanchor : ∀ v ∈ S, ∃ w, (w ∈ R ∧ w ∉ C) ∧ (w = v ∨ G.Adj v w) := by
    intro v hv
    by_cases hvC : v ∈ C
    · obtain ⟨w, hw, hvw⟩ := hnbr v hvC
      exact ⟨w, hw, Or.inr hvw⟩
    by_cases hvR : v ∈ R
    · exact ⟨v, ⟨hvR, hvC⟩, Or.inl rfl⟩
    obtain ⟨a, b, c, ⟨ha, hb, hc, hab, hbc, hac⟩, he⟩ := W.tri_spec v ⟨hv, hvR⟩
    have hadj : ∀ w ∈ ({a, b, c} : Set V), G.Adj v w := fun w hw =>
      (W.adj_iff v ⟨hv, hvR⟩ w).mpr (Or.inl (he ▸ hw))
    by_cases haC : a ∈ C
    · by_cases hbC : b ∈ C
      · by_cases hcC : c ∈ C
        · exact absurd (hnc b hbC c hcC hbc) (hC.not_isCycleEdge_frame_neighbours h4 hbc.ne
            (hnc a haC b hbC hab) (hnc a haC c hcC hac))
        · exact ⟨c, ⟨hc, hcC⟩, Or.inr (hadj c (by simp))⟩
      · exact ⟨b, ⟨hb, hbC⟩, Or.inr (hadj b (by simp))⟩
    · exact ⟨a, ⟨ha, haC⟩, Or.inr (hadj a (by simp))⟩
  obtain ⟨wx, hwx, hxw⟩ := hanchor x hx
  obtain ⟨wy, hwy, hyw⟩ := hanchor y hy
  obtain ⟨p₁, hp₁⟩ := exists_short_walk hxw
  obtain ⟨p₂, hp₂⟩ := exists_short_walk hyw
  obtain ⟨q⟩ := hreach wx wy hwx hwy
  have hqI : ∀ v ∈ q.support, v ∈ I := mem_of_support_restrict q hwx
  set w := p₁.append ((q.mapLe (restrict_le G I)).append p₂.reverse) with hw
  have hw' : ∀ v ∈ w.support, v ≠ x → v ≠ y → v ∉ {z | z ∈ C} := by
    intro v hv hvx hvy
    rw [hw, Walk.mem_support_append_iff, Walk.mem_support_append_iff, support_mapLe,
      Walk.support_reverse, List.mem_reverse] at hv
    rcases hv with hv | hv | hv
    · rcases hp₁ v hv with rfl | rfl
      · exact absurd rfl hvx
      · exact hwx.2
    · exact (hqI v hv).2
    · rcases hp₂ v hv with rfl | rfl
      · exact absurd rfl hvy
      · exact hwy.2
  obtain ⟨r, hr, -, hrC⟩ := exists_path_of_walk w {z | z ∈ C} hw'
  exact ⟨y, rfl, r, hr, hrC⟩

/-- **Edge composition along a chord.** A web is the edge composition of two webs along every edge
between two non-consecutive vertices of its frame. -/
theorem edge_composition (W : WebData G S C R tri) {d d' : V} (hd : d ∈ C) (hd' : d' ∈ C)
    (hadj : G.Adj d d') (hnot : ¬ IsCycleEdge C d d') : IsWebComposition G S C [d, d'] := by
  obtain ⟨k, A, B, hrot⟩ := exists_rotate_cons_cons hd hd' hadj.ne
  have hR := W.rib.2.1
  refine W.split (m := []) hrot hnot ⟨by simp [hadj.ne], by simp [hadj], ?_⟩ (by simp) ?_
  · intro v hv
    simp only [List.nil_append, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hR _ hd
    · exact hR _ hd'
  · intro u hu v hv huv
    simp only [List.nil_append, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd huv (G.loopless.irrefl _)
    · exact ⟨(u, v), by simp, rfl⟩
    · exact ⟨(v, u), by simp, Sym2.eq_swap⟩
    · exact absurd huv (G.loopless.irrefl _)

end WebData

/-! ### Facts about edge compositions -/

/-- In an edge composition along `dd'`, the edge `dd'` is a chord of the frame. -/
theorem IsWebComposition.chord {H : SimpleGraph V} {T : Set V} {D : List V} {d d' : V}
    (h : IsWebComposition H T D [d, d']) (hD : D.Nodup) :
    H.Adj d d' ∧ ¬ IsCycleEdge D d d' ∧ d ∈ D ∧ d' ∈ D := by
  obtain ⟨a, b, m, A, B, k, S₁, S₂, hl, hrot, -, -, -, -, -, hw₁, hw₂⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ : d = a ∧ m = [] ∧ d' = b := by
    cases m with
    | nil => simp at hl; exact ⟨hl.1, rfl, hl.2⟩
    | cons x m => have := congrArg List.length hl; simp at this
  have hmem : ∀ v, v ∈ D ↔ v ∈ d :: A ++ d' :: B := fun v => by
    rw [← hrot]; exact List.mem_rotate.symm
  obtain ⟨-, -, -, -, ⟨hC₁, -⟩, -⟩ := hw₁
  obtain ⟨-, -, -, -, ⟨hC₂, -⟩, -⟩ := hw₂
  simp only [List.reverse_nil] at hC₁ hC₂
  have hA : A ≠ [] := by
    rintro rfl
    have := hC₁.1
    simp at this
  have hB : B ≠ [] := by
    rintro rfl
    have := hC₂.1
    simp at this
  have hnd : (d :: A ++ d' :: B).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr hD
  -- the closing edge of the first frame is the edge `d'd`
  have hcl : IsCycleEdge (d :: (A ++ [d'])) d' d := by
    refine isCycleEdge_of_isListEdge ?_
    rw [show d :: (A ++ [d']) ++ [d] = (d :: A) ++ [d', d] by simp]
    exact IsListEdge.append_right ⟨(d', d), by simp, rfl⟩
  have hadj : (restrict H S₁).Adj d' d := hcl.adj (by simpa using hC₁)
  refine ⟨hadj.1.symm, ?_, (hmem d).mpr (by simp), (hmem d').mpr (by simp)⟩
  rw [← isCycleEdge_rotate D k, hrot, isCycleEdge_cons_append_cons_iff hnd]
  rintro (h | h)
  · exact hA h
  · exact hB h

/-- An edge of a cycle `C` between two vertices of the front part `D` of a rotation `C = D E`, with
`E` nonempty, is an edge of the cycle `D`. -/
theorem isCycleEdge_of_rotate_append {C D E : List V} {k : ℕ} (hnd : C.Nodup)
    (hrot : C.rotate k = D ++ E) (hE : E ≠ []) {d d' : V} (hd : d ∈ D) (hd' : d' ∈ D)
    (h : IsCycleEdge C d d') : IsCycleEdge D d d' := by
  classical
  have hnd' : (D ++ E).Nodup := by rw [← hrot]; exact List.nodup_rotate.mpr hnd
  have hD : D.Nodup := hnd'.sublist (List.sublist_append_left _ _)
  rw [← isCycleEdge_rotate C k, hrot, isCycleEdge_iff_idxOf hnd'] at h
  rw [isCycleEdge_iff_idxOf hD]
  rw [List.idxOf_append_of_mem hd, List.idxOf_append_of_mem hd'] at h
  have hi := List.idxOf_lt_length_of_mem hd
  have hj := List.idxOf_lt_length_of_mem hd'
  have hE' := List.length_pos_of_ne_nil hE
  simp only [List.length_append] at h
  obtain ⟨-, -, h | h⟩ := h
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    exact ⟨hd, hd', Or.inl (by rw [Nat.mod_eq_of_lt (by omega)]; exact h)⟩
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    exact ⟨hd, hd', Or.inr (by rw [Nat.mod_eq_of_lt (by omega)]; exact h)⟩

/-! ### Items 2 and 3, by induction on the length of the frame -/

/-- The conclusion of items 2 and 3 of Proposition 3.4, for a vertex `x` and a set `Z`. -/
def SepConclusion (G : SimpleGraph V) (S : Set V) (C : List V) (x : V) (Z : Set V) : Prop :=
  ∃ c c', c ∈ C ∧ c' ∈ C ∧ c ∉ Z ∧ c' ∉ Z ∧ c ≠ x ∧ c' ≠ x ∧
    (∀ z ∈ Z, ∀ p : G.Walk x z, c ∈ p.support ∨ c' ∈ p.support) ∧
    IsWebComposition G S C [c, c']

/-- Items 2 and 3 of Proposition 3.4 for frames of length at most `n`. -/
def SepUpTo (V : Type*) (n : ℕ) : Prop :=
  ∀ {S : Set V} {C : List V} {G : SimpleGraph V}, C.length ≤ n → IsWebOn G S C →
    ∀ x ∈ S, ∀ Z : Set V, Z ⊆ S → Z.Nonempty → x ∉ Z →
    (∀ z ∈ Z, ∀ z' ∈ Z, (restrict G Z).Reachable z z') →
    ¬ IsConnectedAvoiding G {v | v ∈ C} x Z → SepConclusion G S C x Z

/-- `x` and `Z` lie on different sides of an edge composition along `cc'`. -/
private theorem sep_direct {S : Set V} {C : List V} (hsupp : IsSupportedOn G S) {T₁ T₂ : Set V}
    {c c' : V} (hU : T₁ ∪ T₂ = S) (hI : ∀ v, v ∈ T₁ → v ∈ T₂ → v = c ∨ v = c')
    (hX : ∀ u ∈ T₁, ∀ v ∈ T₂, G.Adj u v → u ∈ T₂ ∨ v ∈ T₁) (hcc : G.Adj c c')
    (hc₁ : c ∈ T₁) (hc'₁ : c' ∈ T₁) (hc₂ : c ∈ T₂) (hc'₂ : c' ∈ T₂) (hcC : c ∈ C) (hc'C : c' ∈ C)
    (hcomp : IsWebComposition G S C [c, c']) {x : V} (hx₁ : x ∈ T₁) (hx₂ : x ∉ T₂) {Z : Set V}
    (hZS : Z ⊆ S) (hZ : ∀ z ∈ Z, z ∉ T₁) : SepConclusion G S C x Z := by
  refine ⟨c, c', hcC, hc'C, fun h => hZ c h hc₁, fun h => hZ c' h hc'₁,
    fun h => hx₂ (h ▸ hc₂), fun h => hx₂ (h ▸ hc'₂), fun z hz p => ?_, hcomp⟩
  have hS : ∀ w ∈ p.reverse.support, w ∈ T₁ ∪ T₂ := fun w hw =>
    hU ▸ mem_of_support_supported hsupp p.reverse (hZS hz) w hw
  obtain ⟨e, he, hce, -⟩ := (reach_side (M := univ) hX hI hcc hc₁ hc'₁ p.reverse hx₁ hS
    (fun _ _ => trivial)).2 (hZ z hz)
  rw [Walk.support_reverse, List.mem_reverse] at he
  rcases hce with rfl | rfl
  · exact Or.inl he
  · exact Or.inr he

/-- `x` lies on the side `T₁` of an edge composition, and `Z` meets `T₁`: the induction hypothesis
on the side gives the separating pair. -/
private theorem sep_side {n : ℕ} (ih : SepUpTo V n) {S : Set V} {C : List V} {R : Set V}
    {tri : V → Set V} (W : WebData G S C R tri) {T₁ T₂ : Set V} {c c' : V} {D₁ E : List V}
    {k : ℕ} (hU : T₁ ∪ T₂ = S) (hI : ∀ v, v ∈ T₁ → v ∈ T₂ → v = c ∨ v = c')
    (hX : ∀ u ∈ T₁, ∀ v ∈ T₂, G.Adj u v → u ∈ T₂ ∨ v ∈ T₁) (hcc : G.Adj c c')
    (hc : c ∈ T₁) (hc' : c' ∈ T₁) (hweb : IsWebOn (restrict G T₁) T₁ D₁)
    (hlen : D₁.length ≤ n) (hrot : C.rotate k = D₁ ++ E) (hE : E ≠ [])
    (hET : ∀ v ∈ E, v ∈ T₂) (hcE : c ∉ E) (hc'E : c' ∉ E) {x : V} (hx : x ∈ T₁) {Z : Set V}
    (hZS : Z ⊆ S) (hZ1 : (Z ∩ T₁).Nonempty) (hxZ : x ∉ Z)
    (hZc : ∀ z ∈ Z, ∀ z' ∈ Z, (restrict G Z).Reachable z z')
    (hnc : ¬ IsConnectedAvoiding G {v | v ∈ C} x Z) : SepConclusion G S C x Z := by
  classical
  have hCnd := W.rib.1.2.1
  have hmemC : ∀ v, v ∈ C ↔ v ∈ D₁ ++ E := fun v => by
    rw [← hrot]; exact List.mem_rotate.symm
  have hD₁C : ∀ v ∈ D₁, v ∈ C := fun v hv => (hmemC v).mpr (List.mem_append_left _ hv)
  have hD₁T : ∀ v ∈ D₁, v ∈ T₁ := hweb.frame_subset
  have hD₁nd : D₁.Nodup := by
    obtain ⟨-, -, -, -, ⟨hC₁, -⟩, -⟩ := hweb
    exact hC₁.2.1
  -- the frame vertices on the side `T₁` are those of `D₁`
  have hCT : ∀ v ∈ C, v ∈ T₁ → v ∈ D₁ := by
    intro v hv hvT
    rcases List.mem_append.mp ((hmemC v).mp hv) with h | h
    · exact h
    · rcases hI v hvT (hET v h) with rfl | rfl
      · exact absurd h hcE
      · exact absurd h hc'E
  have hxS : x ∈ S := hU ▸ Or.inl hx
  have hwS : ∀ {u v : V} (p : G.Walk u v), u ∈ S → ∀ w ∈ p.support, w ∈ T₁ ∪ T₂ :=
    fun p hu w hw => hU ▸ mem_of_support_supported W.supp p hu w hw
  have hZwalk : ∀ z ∈ Z, ∀ z' ∈ Z, ∃ q : G.Walk z z', ∀ w ∈ q.support, w ∈ Z := by
    intro z hz z' hz'
    obtain ⟨q⟩ := hZc z hz z' hz'
    exact ⟨q.mapLe (restrict_le G Z), fun w hw => by
      rw [support_mapLe] at hw; exact mem_of_support_restrict q hz w hw⟩
  -- the hypotheses on the side
  have hZ₁c : ∀ z ∈ Z ∩ T₁, ∀ z' ∈ Z ∩ T₁,
      (restrict (restrict G T₁) (Z ∩ T₁)).Reachable z z' := by
    intro z hz z' hz'
    obtain ⟨q, hq⟩ := hZwalk z hz.1 z' hz'.1
    have := (reach_side hX hI hcc hc hc' q hz'.2 (hwS q (hZS hz.1)) hq).1 hz.2
    have hle : restrict G (T₁ ∩ Z) ≤ restrict (restrict G T₁) (Z ∩ T₁) := fun u v h =>
      ⟨⟨h.1, h.2.1.1, h.2.2.1⟩, ⟨h.2.1.2, h.2.1.1⟩, ⟨h.2.2.2, h.2.2.1⟩⟩
    exact this.mono hle
  have hnc₁ : ¬ IsConnectedAvoiding (restrict G T₁) {v | v ∈ D₁} x (Z ∩ T₁) := by
    rintro ⟨z, hz, p, hp, hpC⟩
    refine hnc ⟨z, hz.1, p.mapLe (restrict_le G T₁), hp.mapLe _, fun w hw h1 h2 hwC => ?_⟩
    rw [support_mapLe] at hw
    exact hpC w hw h1 h2 (hCT w hwC (mem_of_support_restrict p hx w hw))
  obtain ⟨d, d', hd, hd', hdZ, hd'Z, hdx, hd'x, hsep, hcomp⟩ :=
    ih hlen hweb x hx (Z ∩ T₁) (fun v hv => hv.2) hZ1 (fun h => hxZ h.1) hZ₁c hnc₁
  obtain ⟨hadj, hnot, -, -⟩ := hcomp.chord hD₁nd
  have hdT : d ∈ T₁ := hD₁T d hd
  have hd'T : d' ∈ T₁ := hD₁T d' hd'
  have hdZ' : d ∉ Z := fun h => hdZ ⟨h, hdT⟩
  have hd'Z' : d' ∉ Z := fun h => hd'Z ⟨h, hd'T⟩
  refine ⟨d, d', hD₁C d hd, hD₁C d' hd', hdZ', hd'Z', hdx, hd'x, ?_,
    W.edge_composition (hD₁C d hd) (hD₁C d' hd') hadj.1
      (fun h => hnot (isCycleEdge_of_rotate_append hCnd hrot hE hd hd' h))⟩
  intro z hz p
  by_contra hno
  push Not at hno
  set M := {v | v ≠ d ∧ v ≠ d'} with hM
  have hpM : ∀ w ∈ p.support, w ∈ M :=
    fun w hw => ⟨fun h => hno.1 (h ▸ hw), fun h => hno.2 (h ▸ hw)⟩
  -- a walk inside the side from `x` to a vertex of `Z` that avoids `d` and `d'`
  obtain ⟨f, hf, hr⟩ : ∃ f ∈ Z ∩ T₁, (restrict G (T₁ ∩ M)).Reachable x f := by
    by_cases hzT : z ∈ T₁
    · exact ⟨z, ⟨hz, hzT⟩, (reach_side hX hI hcc hc hc' p hzT (hwS p hxS) hpM).1 hx⟩
    · -- `Z` meets `T₁` and leaves it, so it holds `c` or `c'`
      obtain ⟨z₀, hz₀⟩ := hZ1
      obtain ⟨q, hq⟩ := hZwalk z hz z₀ hz₀.1
      obtain ⟨f, hfq, hf, -⟩ :=
        (reach_side hX hI hcc hc hc' q hz₀.2 (hwS q (hZS hz)) hq).2 hzT
      have hfZ : f ∈ Z := hq f hfq
      have hfT : f ∈ T₁ := by rcases hf with rfl | rfl <;> assumption
      have hfM : f ∈ M := ⟨fun h => hdZ' (h ▸ hfZ), fun h => hd'Z' (h ▸ hfZ)⟩
      have hpM' : ∀ w ∈ p.reverse.support, w ∈ M := fun w hw => hpM w (by
        rw [Walk.support_reverse, List.mem_reverse] at hw; exact hw)
      obtain ⟨e, hep, he, hex⟩ :=
        (reach_side hX hI hcc hc hc' p.reverse hx (hwS p.reverse (hZS hz)) hpM').2 hzT
      have heT : e ∈ T₁ := by rcases he with rfl | rfl <;> assumption
      have heM : e ∈ M := hpM' e hep
      refine ⟨f, ⟨hfZ, hfT⟩, hex.symm.trans ?_⟩
      by_cases hef : e = f
      · rw [hef]
      · have hef' : G.Adj e f := by
          rcases he with rfl | rfl <;> rcases hf with rfl | rfl
          · exact absurd rfl hef
          · exact hcc
          · exact hcc.symm
          · exact absurd rfl hef
        exact Adj.reachable (G := restrict G (T₁ ∩ M)) ⟨hef', ⟨heT, heM⟩, ⟨hfT, hfM⟩⟩
  obtain ⟨q⟩ := hr
  have hle : restrict G (T₁ ∩ M) ≤ restrict G T₁ := fun u v h => ⟨h.1, h.2.1.1, h.2.2.1⟩
  have hqM := mem_of_support_restrict q ⟨hx, hpM x (Walk.start_mem_support p)⟩
  rcases hsep f hf (q.mapLe hle) with h | h
  · rw [support_mapLe] at h
    exact (hqM d h).2.1 rfl
  · rw [support_mapLe] at h
    exact (hqM d' h).2.2 rfl

/-- Items 2 and 3 of Proposition 3.4, for a vertex `x` and a set `Z` inducing a connected subgraph,
by induction on the length of the frame. -/
theorem sepUpTo : ∀ n, SepUpTo V n := by
  intro n
  induction n with
  | zero =>
    intro S C G hlen hweb
    obtain ⟨-, -, -, -, ⟨hC, -⟩, -⟩ := hweb
    have := hC.1
    omega
  | succ n ih =>
    intro S C G hlen hweb x hx Z hZS hZne hxZ hZc hnc
    obtain ⟨R, tri, W⟩ := hweb.exists_webData
    have hC := W.rib.1
    obtain ⟨z₀, hz₀⟩ := hZne
    have hxz₀ : x ≠ z₀ := fun h => hxZ (h ▸ hz₀)
    -- frames of length three: the web is a clique
    by_cases h3 : C.length = 3
    · exfalso
      obtain ⟨a, b, c, rfl⟩ : ∃ a b c, C = [a, b, c] := by
        match C, h3 with
        | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      have hxz : G.Adj x z₀ := ((isWebOn_three_iff.mp hweb).2 x z₀).mpr ⟨hx, hZS hz₀, hxz₀⟩
      exact hnc ⟨z₀, hz₀, hxz.toWalk, Walk.IsPath.of_adj hxz, fun w hw h1 h2 => by
        rw [support_toWalk, List.mem_cons, List.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact absurd rfl h1
        · exact absurd rfl h2⟩
    have h4 : 4 ≤ C.length := by have := hC.1; omega
    -- frames without chords: all vertices are `C`-connected
    by_cases hch : ∃ c ∈ C, ∃ c' ∈ C, G.Adj c c' ∧ ¬ IsCycleEdge C c c'
    swap
    · exfalso
      push Not at hch
      obtain ⟨z, hz, p, hp, hpC⟩ := W.connected_of_no_chord h4 hch hx (hZS hz₀)
      rw [mem_singleton_iff] at hz
      subst hz
      exact hnc ⟨z, hz₀, p, hp, hpC⟩
    -- a chord `cc'`: the web is an edge composition along it
    obtain ⟨c, hcC, c', hc'C, hcc, hnot⟩ := hch
    have hcomp := W.edge_composition hcC hc'C hcc hnot
    obtain ⟨a, b, m, A, B, k, S₁, S₂, hl, hrot, -, hU, hI, hX, -, hw₁, hw₂⟩ := hcomp
    obtain ⟨rfl, rfl, rfl⟩ : c = a ∧ m = [] ∧ c' = b := by
      cases m with
      | nil => simp at hl; exact ⟨hl.1, rfl, hl.2⟩
      | cons x m => have := congrArg List.length hl; simp at this
    simp only [List.reverse_nil] at hw₁ hw₂
    have hI' : ∀ v, v ∈ S₁ → v ∈ S₂ → v = c ∨ v = c' := fun v h1 h2 => by
      have : v ∈ S₁ ∩ S₂ := ⟨h1, h2⟩
      rw [hI] at this
      simpa using this
    have hcS : c ∈ S₁ ∩ S₂ := by rw [hI]; simp
    have hc'S : c' ∈ S₁ ∩ S₂ := by rw [hI]; simp
    have hX' : ∀ u ∈ S₂, ∀ v ∈ S₁, G.Adj u v → u ∈ S₁ ∨ v ∈ S₂ :=
      fun u hu v hv huv => (hX v hv u hu huv.symm).symm
    have hnd : (c :: A ++ c' :: B).Nodup := by rw [← hrot]; exact List.nodup_rotate.mpr hC.2.1
    have hlen' : (c :: A ++ c' :: B).length = C.length := by rw [← hrot, List.length_rotate]
    have hA : A ≠ [] := by
      rintro rfl
      obtain ⟨-, -, -, -, ⟨hC₁, -⟩, -⟩ := hw₁
      have := hC₁.1
      simp at this
    have hB : B ≠ [] := by
      rintro rfl
      obtain ⟨-, -, -, -, ⟨hC₂, -⟩, -⟩ := hw₂
      have := hC₂.1
      simp at this
    rw [List.cons_append, List.nodup_cons, List.nodup_append, List.nodup_cons] at hnd
    have hcA : c ∉ A := fun h => hnd.1 (List.mem_append_left _ h)
    have hcB : c ∉ B := fun h => hnd.1 (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    have hc'A : c' ∉ A := fun h => hnd.2.2.2 c' h c' List.mem_cons_self rfl
    have hc'B : c' ∉ B := hnd.2.2.1.1
    have hrot₁ : C.rotate k = (c :: A ++ [c']) ++ B := by rw [hrot]; simp
    have hrot₂ : C.rotate (k + (c :: A).length) = (c' :: B ++ [c]) ++ A := by
      rw [← List.rotate_rotate, hrot, List.rotate_append_length_eq]
      simp
    have hlen₁ : (c :: A ++ [c']).length ≤ n := by
      have := List.length_pos_of_ne_nil hB
      simp at hlen' ⊢
      omega
    have hlen₂ : (c' :: B ++ [c]).length ≤ n := by
      have := List.length_pos_of_ne_nil hA
      simp at hlen' ⊢
      omega
    have hBS : ∀ v ∈ B, v ∈ S₂ := fun v hv => hw₂.frame_subset v (by simp [hv])
    have hAS : ∀ v ∈ A, v ∈ S₁ := fun v hv => hw₁.frame_subset v (by simp [hv])
    have hcomp : IsWebComposition G S C [c, c'] := W.edge_composition hcC hc'C hcc hnot
    have hU₂ : S₂ ∪ S₁ = S := by rw [union_comm]; exact hU
    have hI'' : ∀ v, v ∈ S₂ → v ∈ S₁ → v = c ∨ v = c' := fun v h2 h1 => hI' v h1 h2
    by_cases h1 : x ∈ S₁ ∧ (Z ∩ S₁).Nonempty
    · exact sep_side ih W hU hI' hX hcc hcS.1 hc'S.1 hw₁ hlen₁ hrot₁ hB hBS hcB hc'B h1.1 hZS h1.2
        hxZ hZc hnc
    by_cases h2 : x ∈ S₂ ∧ (Z ∩ S₂).Nonempty
    · exact sep_side ih W hU₂ hI'' hX' hcc hcS.2 hc'S.2 hw₂ hlen₂ hrot₂ hA hAS hcA hc'A h2.1 hZS
        h2.2 hxZ hZc hnc
    -- `x` and `Z` lie on different sides
    have hZU : ∀ z ∈ Z, z ∈ S₁ ∪ S₂ := fun z hz => hU ▸ hZS hz
    have hxU : x ∈ S₁ ∪ S₂ := hU ▸ hx
    rcases hxU with hx1 | hx2
    · have hZ1 : ∀ z ∈ Z, z ∉ S₁ := fun z hz hz1 => h1 ⟨hx1, z, hz, hz1⟩
      have hx2 : x ∉ S₂ := fun hx2 => h2 ⟨hx2, z₀, hz₀, (hZU z₀ hz₀).resolve_left (hZ1 z₀ hz₀)⟩
      exact sep_direct W.supp hU hI' hX hcc hcS.1 hc'S.1 hcS.2 hc'S.2 hcC hc'C hcomp hx1 hx2 hZS
        hZ1
    · have hZ2 : ∀ z ∈ Z, z ∉ S₂ := fun z hz hz2 => h2 ⟨hx2, z, hz, hz2⟩
      have hx1 : x ∉ S₁ := fun hx1 => h1 ⟨hx1, z₀, hz₀, (hZU z₀ hz₀).resolve_right (hZ2 z₀ hz₀)⟩
      exact sep_direct W.supp hU₂ hI'' hX' hcc hcS.2 hc'S.2 hcS.1 hc'S.1 hcC hc'C hcomp hx2 hx1
        hZS hZ2

/-! ### Proposition 3.4 and Corollary 3.5 -/

variable {S : Set V} {C : List V}

/-- **Proposition 3.4, item 2** (Humeau and Pous, page 10). "for all vertices $x,y$, either $x$ is
$C$-connected to $y$, or there exists a pair of vertices $c,c'\in C-x-y$ separating $x$ from $y$ and
such that $G$ is the edge composition of two webs along $cc'$". Separation is stated for all walks
from `x` to `y`, which is the same as for all paths. -/
theorem prop_3_4_ii (h : IsWebOn G S C) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    IsConnectedAvoiding G {z | z ∈ C} x {y} ∨
      ∃ c c', c ∈ C ∧ c' ∈ C ∧ c ≠ x ∧ c ≠ y ∧ c' ≠ x ∧ c' ≠ y ∧
        (∀ p : G.Walk x y, c ∈ p.support ∨ c' ∈ p.support) ∧ IsWebComposition G S C [c, c'] := by
  by_cases hxy : x = y
  · subst hxy
    exact Or.inl ⟨x, rfl, .nil, Walk.IsPath.nil, fun w hw h1 _ => by
      simp at hw; exact absurd hw h1⟩
  by_cases hcon : IsConnectedAvoiding G {z | z ∈ C} x {y}
  · exact Or.inl hcon
  obtain ⟨c, c', hc, hc', hcy, hc'y, hcx, hc'x, hsep, hcomp⟩ :=
    sepUpTo C.length le_rfl h x hx {y} (by simpa using hy) (singleton_nonempty y)
      (fun h => hxy (mem_singleton_iff.mp h)) (fun z hz z' hz' => by
        rw [mem_singleton_iff.mp hz, mem_singleton_iff.mp hz']) hcon
  exact Or.inr ⟨c, c', hc, hc', hcx, fun h => hcy (h ▸ rfl), hc'x, fun h => hc'y (h ▸ rfl),
    hsep y rfl, hcomp⟩

/-- **Proposition 3.4, item 3** (Humeau and Pous, page 10). "for every vertex $x$ and every subpath
$P$ of $C$, either $x$ is $C$-connected to $P$, or there are vertices $c,c'$ of $C-P-x$ separating
$x$ from $P$ and such that $G$ is the edge composition of two webs along $cc'$." A subpath of `C` is
a nonempty front part `P` of a rotation `P ++ Q` of `C`. -/
theorem prop_3_4_iii (h : IsWebOn G S C) {x : V} (hx : x ∈ S) {P Q : List V} {k : ℕ}
    (hrot : C.rotate k = P ++ Q) (hP : P ≠ []) :
    IsConnectedAvoiding G {z | z ∈ C} x {v | v ∈ P} ∨
      ∃ c c', c ∈ C ∧ c' ∈ C ∧ c ∉ P ∧ c' ∉ P ∧ c ≠ x ∧ c' ≠ x ∧
        (∀ z ∈ P, ∀ p : G.Walk x z, c ∈ p.support ∨ c' ∈ p.support) ∧
        IsWebComposition G S C [c, c'] := by
  have hmem : ∀ v ∈ P, v ∈ C := fun v hv => by
    rw [← List.mem_rotate (n := k), hrot]; exact List.mem_append_left _ hv
  by_cases hxP : x ∈ P
  · exact Or.inl ⟨x, hxP, .nil, Walk.IsPath.nil, fun w hw h1 _ => by
      simp at hw; exact absurd hw h1⟩
  by_cases hcon : IsConnectedAvoiding G {z | z ∈ C} x {v | v ∈ P}
  · exact Or.inl hcon
  have hC : IsCycleList G C := by
    obtain ⟨-, -, -, -, ⟨hC, -⟩, -⟩ := h
    exact hC
  have hch : P.IsChain G.Adj := by
    have := ((hC.rotate k).isPathList (R := univ) (fun _ _ => trivial)).2.1
    rw [hrot] at this
    exact this.left_of_append
  obtain ⟨v₀, hv₀⟩ := List.exists_mem_of_ne_nil P hP
  obtain ⟨c, c', hc, hc', hcP, hc'P, hcx, hc'x, hsep, hcomp⟩ :=
    sepUpTo C.length le_rfl h x hx {v | v ∈ P} (fun v hv => h.frame_subset v (hmem v hv))
      ⟨v₀, hv₀⟩ hxP (fun z hz z' hz' => chain_reach hch (fun v hv => hv) z hz z' hz') hcon
  exact Or.inr ⟨c, c', hc, hc', hcP, hc'P, hcx, hc'x, hsep, hcomp⟩

/-- **Proposition 3.4, item 1** (Humeau and Pous, page 10). "$G$ is the edge composition of two webs
if and only if there is a pair of vertices of $G$ which are not $C$-connected." -/
theorem prop_3_4_i (h : IsWebOn G S C) :
    (∃ c c', IsWebComposition G S C [c, c']) ↔
      ∃ x ∈ S, ∃ y ∈ S, ¬ IsConnectedAvoiding G {z | z ∈ C} x {y} := by
  constructor
  · rintro ⟨c, c', hcomp⟩
    have hC : IsCycleList G C := by
      obtain ⟨-, -, -, -, ⟨hC, -⟩, -⟩ := h
      exact hC
    obtain ⟨hcc, -, -, -⟩ := hcomp.chord hC.2.1
    obtain ⟨a, b, m, A, B, k, S₁, S₂, hl, hrot, hsupp, hU, hI, hX, -, hw₁, hw₂⟩ := hcomp
    obtain ⟨rfl, rfl, rfl⟩ : c = a ∧ m = [] ∧ c' = b := by
      cases m with
      | nil => simp at hl; exact ⟨hl.1, rfl, hl.2⟩
      | cons x m => have := congrArg List.length hl; simp at this
    simp only [List.reverse_nil] at hw₁ hw₂
    have hnd : (c :: A ++ c' :: B).Nodup := by rw [← hrot]; exact List.nodup_rotate.mpr hC.2.1
    rw [List.cons_append, List.nodup_cons, List.nodup_append, List.nodup_cons] at hnd
    have hA : A ≠ [] := by
      rintro rfl
      obtain ⟨-, -, -, -, ⟨hC₁, -⟩, -⟩ := hw₁
      have := hC₁.1
      simp at this
    have hB : B ≠ [] := by
      rintro rfl
      obtain ⟨-, -, -, -, ⟨hC₂, -⟩, -⟩ := hw₂
      have := hC₂.1
      simp at this
    obtain ⟨x, hxA⟩ := List.exists_mem_of_ne_nil A hA
    obtain ⟨y, hyB⟩ := List.exists_mem_of_ne_nil B hB
    have hI' : ∀ v, v ∈ S₁ → v ∈ S₂ → v = c ∨ v = c' := fun v h1 h2 => by
      have : v ∈ S₁ ∩ S₂ := ⟨h1, h2⟩
      rw [hI] at this
      simpa using this
    have hcS : c ∈ S₁ ∩ S₂ := by rw [hI]; simp
    have hc'S : c' ∈ S₁ ∩ S₂ := by rw [hI]; simp
    have hcA : c ∉ A := fun h => hnd.1 (List.mem_append_left _ h)
    have hcB : c ∉ B := fun h => hnd.1 (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    have hc'A : c' ∉ A := fun h => hnd.2.2.2 c' h c' List.mem_cons_self rfl
    have hc'B : c' ∉ B := hnd.2.2.1.1
    have hx1 : x ∈ S₁ := hw₁.frame_subset x (by simp [hxA])
    have hy2 : y ∈ S₂ := hw₂.frame_subset y (by simp [hyB])
    have hy1 : y ∉ S₁ := fun hy1 => by
      rcases hI' y hy1 hy2 with rfl | rfl
      · exact hcB hyB
      · exact hc'B hyB
    have hmemC : ∀ v, v ∈ C ↔ v ∈ c :: A ++ c' :: B := fun v => by
      rw [← hrot]; exact List.mem_rotate.symm
    refine ⟨x, hU ▸ Or.inl hx1, y, hU ▸ Or.inr hy2, ?_⟩
    rintro ⟨z, hz, p, -, hpC⟩
    rw [mem_singleton_iff] at hz
    subst hz
    have hS : ∀ w ∈ p.reverse.support, w ∈ S₁ ∪ S₂ := fun w hw =>
      hU ▸ mem_of_support_supported hsupp p.reverse (hU ▸ Or.inr hy2) w hw
    obtain ⟨e, he, hce, -⟩ := (reach_side (M := univ) hX hI' hcc hcS.1 hc'S.1 p.reverse hx1 hS
      (fun _ _ => trivial)).2 hy1
    rw [Walk.support_reverse, List.mem_reverse] at he
    have heC : e ∈ C := (hmemC e).mpr (by rcases hce with rfl | rfl <;> simp)
    refine hpC e he (fun hex => ?_) (fun hey => ?_) heC
    · subst hex
      rcases hce with rfl | rfl
      · exact hcA hxA
      · exact hc'A hxA
    · subst hey
      rcases hce with rfl | rfl
      · exact hcB hyB
      · exact hc'B hyB
  · rintro ⟨x, hx, y, hy, hxy⟩
    rcases prop_3_4_ii h hx hy with h' | ⟨c, c', -, -, -, -, -, -, -, hcomp⟩
    · exact absurd h' hxy
    · exact ⟨c, c', hcomp⟩

end GraphMinor.HP25
