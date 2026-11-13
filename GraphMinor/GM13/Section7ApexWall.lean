module

public import GraphMinor.GM13.Section7a
public import GraphMinor.GM14.Suppress
public import GraphMinor.Minor.Basic

/-!
# Graph Minors XIII, (7.3): the wall with a vertex at infinity

To show that the new wall of (7.3) is drawn as in Fig. 1 we use Whitney's theorem
(`GraphMinor/GM14/Whitney.lean`): two drawings in the sphere of a subdivision of a simple
3-connected graph differ by a homeomorphism of the sphere. A wall alone is not 3-connected, since
the vertices on its sides have only two neighbours. So we add one vertex, which will be drawn at
the point at infinity, and join it to every vertex on the four sides of the elementary wall
(`apexWall`). This graph stays connected when any two vertices are deleted
(`apexWall_conn`), and a graph with this property is a subdivision of a simple 3-connected graph
(`ConnGood.good`, then `good_sub` of Graph Minors XIV). The property passes along graph
isomorphisms (`ConnGood.of_iso`), so it holds for every drawing of `apexWall`.

The connectivity proof is direct. If the new vertex is kept, every vertex of the wall reaches it
along one of three paths that meet only at the start: along its row to the left side, along its
row to the right side, and up or down a staircase to the top or bottom side. Two deleted vertices
block at most two of them. If the new vertex is deleted, one vertex `x` of the wall may be deleted
as well. Then the rows other than the row of `x` are whole paths, two consecutive rows are joined
by a vertical edge, the rows just below and above `x` are joined around `x`, and each vertex of
the row of `x` has a vertical edge to another row, or a neighbour in its row that has one.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor.GM06 GraphMinor.GM14.Whitney

universe u v u' v'

/-! ## Graphs that stay connected when two vertices are deleted -/

section Generic

variable {α : Type u} {β : Type v}

/-- A step along an edge of `G` from `x` to a vertex `y` outside `X`. -/
def StepOut (G : Graph α β) (X : Set α) (x y : α) : Prop := (∃ e, G.IsLink e x y) ∧ y ∉ X

/-- `x` reaches `y` in `G` without passing through `X` after the start. -/
def ReachOut (G : Graph α β) (X : Set α) : α → α → Prop := Relation.ReflTransGen (StepOut G X)

/-- A finite simple graph with four vertices of valency at least 3, which stays connected when
at most two vertices are deleted. -/
structure ConnGood (G : Graph α β) : Prop where
  finV : V(G).Finite
  finE : E(G).Finite
  no_loop : ∀ e v, ¬ G.IsLink e v v
  simple : ∀ e f u v, G.IsLink e u v → G.IsLink f u v → e = f
  four : ∃ w : Fin 4 → α, Injective w ∧ ∀ i, w i ∈ V(G) ∧
    ∃ y : Fin 3 → α, Injective y ∧ ∀ j, ∃ e, G.IsLink e (w i) (y j)
  conn : ∀ X ⊆ V(G), X.ncard ≤ 2 → ∀ a ∈ V(G), a ∉ X → ∀ b ∈ V(G), b ∉ X → ReachOut G X a b

variable {G : Graph α β}

/-- A walk outside `X` that starts in `V(G₁) \ V(G₂)` stays there, where `(G₁, G₂)` is a
separation with `V(G₁) ∩ V(G₂) ⊆ X`: an edge at a vertex of `V(G₁) \ V(G₂)` is not an edge of
`G₂`, so it is an edge of `G₁`. -/
theorem ReachOut.stays {G₁ G₂ : Graph α β} (hs : IsGraphSeparation G G₁ G₂) {X : Set α}
    (hX : V(G₁) ∩ V(G₂) ⊆ X) {a b : α} (hab : ReachOut G X a b) (ha1 : a ∈ V(G₁))
    (ha2 : a ∉ V(G₂)) : b ∈ V(G₁) ∧ b ∉ V(G₂) := by
  induction hab with
  | refl => exact ⟨ha1, ha2⟩
  | tail _ hst ih =>
    obtain ⟨hz1, hz2⟩ := ih
    obtain ⟨⟨e, hl⟩, hwX⟩ := hst
    obtain ⟨h1, h2, -, hE, -⟩ := hs
    have he : e ∈ E(G₁) ∪ E(G₂) := hE ▸ hl.edge_mem
    rcases he with he | he
    · have hl1 := (IsSubgraph.isLink_iff h1 he).mpr hl
      exact ⟨hl1.right_mem, fun hw2 => hwX (hX ⟨hl1.right_mem, hw2⟩)⟩
    · have hl2 := (IsSubgraph.isLink_iff h2 he).mpr hl
      exact absurd hl2.left_mem hz2

/-- A vertex with three distinct neighbours has valency other than `2`. -/
theorem ConnGood.deg_ne_two (hG : ConnGood G) {w : α} {y : Fin 3 → α} (hy : Injective y)
    (hl : ∀ j, ∃ e, G.IsLink e w (y j)) : deg G w ≠ 2 := by
  choose e he using hl
  have hinj : Injective e := fun i j hij => hy ((he i).right_unique (hij ▸ he j))
  have hi : ∀ j, G.Inc (e j) w := fun j => ⟨y j, he j⟩
  have hfin : {f | G.Inc f w}.Finite := hG.finE.subset fun f hf => hf.edge_mem
  have h3 : (range e).ncard = 3 := by
    rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle : (range e).ncard ≤ deg G w :=
    ncard_le_ncard (by rintro _ ⟨j, rfl⟩; exact hi j) hfin
  omega

/-- **A graph that stays connected when two vertices are deleted is good.** For a separation
`(G₁, G₂)` of order at most `2`, a vertex of `G₁` outside `G₂` and a vertex of `G₂` outside `G₁`
would be joined outside the common vertices (`ReachOut.stays`). So one side has all its vertices
in the other side. Its edges then join the at most two common vertices, so there is at most one
of them, since the graph is simple and has no loops. -/
theorem ConnGood.good (hG : ConnGood G) : Good G := by
  classical
  refine ⟨hG.finV, hG.finE, hG.no_loop, ?_, ?_⟩
  · obtain ⟨w, hw, hw'⟩ := hG.four
    have hsub : range w ⊆ {v | v ∈ V(G) ∧ deg G v ≠ 2} := by
      rintro _ ⟨i, rfl⟩
      obtain ⟨hwi, y, hy, hl⟩ := hw' i
      exact ⟨hwi, hG.deg_ne_two hy hl⟩
    have h4 : (range w).ncard = 4 := by
      rw [ncard_range_of_injective hw, Nat.card_eq_fintype_card, Fintype.card_fin]
    have := ncard_le_ncard hsub (hG.finV.subset fun v hv => hv.1)
    omega
  · intro G₁ G₂ hs hc
    have hsub : ∀ {H₁ H₂ : Graph α β}, IsGraphSeparation G H₁ H₂ →
        (V(H₁) ∩ V(H₂)).ncard ≤ 2 → V(H₁) ⊆ V(H₂) → Thin G H₁ H₂ := by
      intro H₁ H₂ hs' hc' hV
      by_cases hE : E(H₁) = ∅
      · exact Or.inl ⟨hV, hE⟩
      right
      obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hE
      obtain ⟨x, y, hl⟩ := (H₁.edge_mem_iff_exists_isLink e).mp he
      have hxy : x ≠ y := fun hxy => by subst hxy; exact hG.no_loop e x (hl.mono hs'.1)
      have hx : x ∈ V(H₁) ∩ V(H₂) := ⟨hl.left_mem, hV hl.left_mem⟩
      have hy : y ∈ V(H₁) ∩ V(H₂) := ⟨hl.right_mem, hV hl.right_mem⟩
      have hfin : (V(H₁) ∩ V(H₂)).Finite :=
        hG.finV.subset fun z hz => hs'.1.vertexSet_mono hz.1
      have hS : V(H₁) ∩ V(H₂) = {x, y} := by
        have h2 : ({x, y} : Set α).ncard = 2 := ncard_pair hxy
        have hsub' : ({x, y} : Set α) ⊆ V(H₁) ∩ V(H₂) := by
          rintro z (rfl | rfl)
          · exact hx
          · exact hy
        exact (eq_of_subset_of_ncard_le hsub' (by omega) hfin).symm
      refine ⟨by rw [hS]; exact ncard_pair hxy, fun z hz => absurd (hV hz.1) hz.2, ?_⟩
      have hdiff : V(H₁) \ V(H₂) = ∅ := sdiff_eq_empty.mpr hV
      rw [hdiff, ncard_empty, zero_add]
      have hE1 : E(H₁) ⊆ {e} := by
        intro f hf
        obtain ⟨u, w, hl'⟩ := (H₁.edge_mem_iff_exists_isLink f).mp hf
        have hu : u ∈ ({x, y} : Set α) := hS ▸ ⟨hl'.left_mem, hV hl'.left_mem⟩
        have hw : w ∈ ({x, y} : Set α) := hS ▸ ⟨hl'.right_mem, hV hl'.right_mem⟩
        have huw : u ≠ w := fun huw => by subst huw; exact hG.no_loop f u (hl'.mono hs'.1)
        have hlG := hl.mono hs'.1
        have hlG' := hl'.mono hs'.1
        rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
        · exact absurd rfl huw
        · exact hG.simple f e u w hlG' hlG
        · exact hG.simple f e w u hlG'.symm hlG
        · exact absurd rfl huw
      calc E(H₁).ncard ≤ ({e} : Set β).ncard := ncard_le_ncard hE1 (finite_singleton e)
        _ = 1 := ncard_singleton e
    have hsymm : IsGraphSeparation G G₂ G₁ := by
      obtain ⟨a, b, c, d, e⟩ := hs
      exact ⟨b, a, by rw [union_comm]; exact c, by rw [union_comm]; exact d, e.symm⟩
    by_cases h12 : V(G₁) ⊆ V(G₂)
    · exact Or.inl (hsub hs hc h12)
    by_cases h21 : V(G₂) ⊆ V(G₁)
    · exact Or.inr (hsub hsymm (by rwa [inter_comm]) h21)
    exfalso
    obtain ⟨a, ha1, ha2⟩ := not_subset.mp h12
    obtain ⟨b, hb2, hb1⟩ := not_subset.mp h21
    have haV : a ∈ V(G) := hs.1.vertexSet_mono ha1
    have hbV : b ∈ V(G) := hs.2.1.vertexSet_mono hb2
    have hXV : V(G₁) ∩ V(G₂) ⊆ V(G) := fun z hz => hs.1.vertexSet_mono hz.1
    have hr := hG.conn _ hXV hc a haV (fun h => ha2 h.2) b hbV (fun h => hb1 h.1)
    exact hb1 (hr.stays hs subset_rfl ha1 ha2).1

/-- **The property passes along isomorphisms.** -/
theorem ConnGood.of_iso {α' : Type u'} {β' : Type v'} {H : Graph α' β'} (hH : ConnGood H)
    (φ : GraphMinor.Iso H G) : ConnGood G := by
  classical
  have hVeq : V(G) = (fun a : V(H) => (φ.vertexEquiv a).1) '' univ := by
    ext x
    constructor
    · intro hx
      exact ⟨φ.vertexEquiv.symm ⟨x, hx⟩, mem_univ _, by simp⟩
    · rintro ⟨a, -, rfl⟩
      exact (φ.vertexEquiv a).2
  have hEeq : E(G) = (fun a : E(H) => (φ.edgeEquiv a).1) '' univ := by
    ext x
    constructor
    · intro hx
      exact ⟨φ.edgeEquiv.symm ⟨x, hx⟩, mem_univ _, by simp⟩
    · rintro ⟨a, -, rfl⟩
      exact (φ.edgeEquiv a).2
  have hfinVH : Finite V(H) := hH.finV.to_subtype
  have hfinEH : Finite E(H) := hH.finE.to_subtype
  -- links of `G` come from links of `H`
  have hlink : ∀ {f x y}, G.IsLink f x y → ∃ (f' : E(H)) (x' y' : V(H)),
      (φ.edgeEquiv f').1 = f ∧ (φ.vertexEquiv x').1 = x ∧ (φ.vertexEquiv y').1 = y ∧
        H.IsLink f'.1 x'.1 y'.1 := by
    intro f x y hl
    refine ⟨φ.edgeEquiv.symm ⟨f, hl.edge_mem⟩, φ.vertexEquiv.symm ⟨x, hl.left_mem⟩,
      φ.vertexEquiv.symm ⟨y, hl.right_mem⟩, by simp, by simp, by simp, ?_⟩
    rw [φ.isLink_iff]
    simpa using hl
  refine ⟨hVeq ▸ (finite_univ.image _), hEeq ▸ (finite_univ.image _), ?_, ?_, ?_, ?_⟩
  · intro f x hl
    obtain ⟨f', x', y', -, hx, hy, hl'⟩ := hlink hl
    have : x' = y' := φ.vertexEquiv.injective (Subtype.ext (hx.trans hy.symm))
    subst this
    exact hH.no_loop _ _ hl'
  · intro f g x y hf hg
    obtain ⟨f', x', y', hf', hx, hy, hl⟩ := hlink hf
    obtain ⟨g', x'', y'', hg', hx', hy', hl'⟩ := hlink hg
    have e1 : x'' = x' := φ.vertexEquiv.injective (Subtype.ext (hx'.trans hx.symm))
    have e2 : y'' = y' := φ.vertexEquiv.injective (Subtype.ext (hy'.trans hy.symm))
    subst e1 e2
    have := hH.simple _ _ _ _ hl hl'
    rw [← hf', ← hg', show f' = g' from Subtype.ext this]
  · obtain ⟨w, hw, hw'⟩ := hH.four
    choose hwV y hy e he using hw'
    refine ⟨fun i => (φ.vertexEquiv ⟨w i, hwV i⟩).1, fun i j hij => ?_, fun i => ⟨(φ.vertexEquiv _).2,
      fun j => (φ.vertexEquiv ⟨y i j, (he i j).right_mem⟩).1, fun j k hjk => ?_, fun j => ?_⟩⟩
    · have := φ.vertexEquiv.injective (Subtype.ext hij)
      exact hw (congrArg Subtype.val this)
    · have := φ.vertexEquiv.injective (Subtype.ext hjk)
      exact hy i (congrArg Subtype.val this)
    · exact ⟨(φ.edgeEquiv ⟨e i j, (he i j).edge_mem⟩).1,
        (φ.isLink_iff ⟨e i j, (he i j).edge_mem⟩ ⟨w i, hwV i⟩ ⟨y i j, (he i j).right_mem⟩).mp
          (he i j)⟩
  · intro X hXV hX a ha haX b hb hbX
    let X' : Set α' := {z | ∃ hz : z ∈ V(H), (φ.vertexEquiv ⟨z, hz⟩).1 ∈ X}
    have hX'V : X' ⊆ V(H) := fun z hz => hz.1
    have hX' : X'.ncard ≤ 2 := by
      have hinj : InjOn (fun z => if hz : z ∈ V(H) then (φ.vertexEquiv ⟨z, hz⟩).1 else a) X' := by
        intro z hz z' hz' e
        simp only [hz.1, hz'.1, ↓reduceDIte] at e
        exact congrArg Subtype.val (φ.vertexEquiv.injective (Subtype.ext e))
      have hmaps : MapsTo (fun z => if hz : z ∈ V(H) then (φ.vertexEquiv ⟨z, hz⟩).1 else a) X' X :=
        fun z hz => by simp only [hz.1, ↓reduceDIte]; exact hz.2
      have hXf : X.Finite := hVeq ▸ (finite_univ.image _) |>.subset hXV
      exact (ncard_le_ncard_of_injOn _ hmaps hinj hXf).trans hX
    set a' := φ.vertexEquiv.symm ⟨a, ha⟩
    set b' := φ.vertexEquiv.symm ⟨b, hb⟩
    have hmem : ∀ z : V(H), z.1 ∈ X' ↔ (φ.vertexEquiv z).1 ∈ X := fun z =>
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨z.2, h⟩⟩
    have ha' : a'.1 ∉ X' := by rw [hmem]; simpa [a'] using haX
    have hb' : b'.1 ∉ X' := by rw [hmem]; simpa [b'] using hbX
    have hr := hH.conn X' hX'V hX' a'.1 a'.2 ha' b'.1 b'.2 hb'
    -- map the walk
    have key : ∀ z, ReachOut H X' a'.1 z → ∀ hz : z ∈ V(H),
        ReachOut G X a (φ.vertexEquiv ⟨z, hz⟩).1 := by
      intro z hz
      induction hz with
      | refl => intro _; simp only [a', Subtype.coe_eta, Equiv.apply_symm_apply]; exact Relation.ReflTransGen.refl
      | tail _ hst ih =>
        rename_i y z _
        intro hzV
        obtain ⟨⟨f, hl⟩, hzX⟩ := hst
        refine (ih hl.left_mem).tail ⟨⟨(φ.edgeEquiv ⟨f, hl.edge_mem⟩).1, ?_⟩, ?_⟩
        · exact (φ.isLink_iff ⟨f, hl.edge_mem⟩ ⟨y, hl.left_mem⟩ ⟨z, hzV⟩).mp hl
        · rw [← hmem]; exact hzX
    simpa [b'] using key b'.1 hr b'.2

end Generic

/-! ## The elementary wall with a vertex at infinity -/

section Apex

/-- A vertex on one of the four sides of the elementary wall of height `h`: in the bottom row, in
the top row, in the left column or in the right column. -/
def IsSideVert (h : ℕ) (p : ℕ × ℕ) : Prop := p.2 = 0 ∨ p.2 = h ∨ p.1 = 0 ∨ p.1 = 2 * h + 1

/-- Adjacency in `apexWall h`: the vertex `none` is the new vertex, joined to the side
vertices. -/
def apexAdj (h : ℕ) : Option (ℕ × ℕ) → Option (ℕ × ℕ) → Prop
  | some p, some q => elementaryWallAdj h p q
  | none, some q => q ∈ elementaryWallVerts h ∧ IsSideVert h q
  | some p, none => p ∈ elementaryWallVerts h ∧ IsSideVert h p
  | none, none => False

theorem apexAdj_symm {h : ℕ} {a b : Option (ℕ × ℕ)} (hab : apexAdj h a b) : apexAdj h b a := by
  cases a <;> cases b <;> simp only [apexAdj] at hab ⊢
  · exact hab
  · exact hab
  · exact elementaryWallAdj_symm hab

theorem apexAdj_irrefl {h : ℕ} (a : Option (ℕ × ℕ)) : ¬ apexAdj h a a := by
  cases a with
  | none => simp [apexAdj]
  | some p => exact elementaryWallAdj_irrefl p

/-- **The elementary wall of height `h` with a new vertex `none`** joined to every vertex on the
four sides. -/
def apexWall (h : ℕ) : Graph (Option (ℕ × ℕ)) (Sym2 (Option (ℕ × ℕ))) where
  vertexSet := insert none (some '' elementaryWallVerts h)
  edgeSet := {e | ∃ a b, apexAdj h a b ∧ e = s(a, b)}
  IsLink e a b := apexAdj h a b ∧ e = s(a, b)
  isLink_symm e _ := ⟨fun _ _ ⟨hab, he⟩ => ⟨apexAdj_symm hab, he.trans Sym2.eq_swap⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := by
    have heq : s(_, _) = s(_, _) := h1.2.symm.trans h2.2
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink _ := Iff.rfl
  left_mem_of_isLink e a b hl := by
    obtain ⟨hab, -⟩ := hl
    cases a with
    | none => exact mem_insert _ _
    | some p =>
      cases b with
      | none => exact Or.inr ⟨p, hab.1, rfl⟩
      | some q => exact Or.inr ⟨p, hab.1, rfl⟩

variable {h : ℕ}

theorem mem_elementaryWallVerts_iff {x y : ℕ} :
    (x, y) ∈ elementaryWallVerts h ↔
      x ≤ 2 * h + 1 ∧ y ≤ h ∧ ¬ (x = 0 ∧ y = 0) ∧ ¬ (x = 2 * h + 1 ∧ y = h) := by
  simp only [elementaryWallVerts, mem_setOf_eq, ne_eq, Prod.mk.injEq]

theorem adj_right {x y : ℕ} (h1 : (x, y) ∈ elementaryWallVerts h)
    (h2 : (x + 1, y) ∈ elementaryWallVerts h) : elementaryWallAdj h (x, y) (x + 1, y) :=
  ⟨h1, h2, Or.inl ⟨rfl, Or.inl rfl⟩⟩

theorem adj_up {x y : ℕ} (h1 : (x, y) ∈ elementaryWallVerts h)
    (h2 : (x, y + 1) ∈ elementaryWallVerts h) (hodd : (x + y) % 2 = 1) :
    elementaryWallAdj h (x, y) (x, y + 1) :=
  ⟨h1, h2, Or.inr ⟨rfl, Or.inl ⟨rfl, Nat.odd_iff.mpr hodd⟩⟩⟩

/-- Proves membership in `elementaryWallVerts h` by arithmetic. -/
macro "memW" : tactic => `(tactic| (rw [mem_elementaryWallVerts_iff]; omega))

variable {X : Set (Option (ℕ × ℕ))}

theorem stepOut_ww {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) (hq : some q ∉ X) :
    StepOut (apexWall h) X (some p) (some q) :=
  ⟨⟨s(some p, some q), hpq, rfl⟩, hq⟩

theorem stepOut_wn {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) (hs : IsSideVert h p)
    (hX : none ∉ X) : StepOut (apexWall h) X (some p) none :=
  ⟨⟨s(some p, none), ⟨hp, hs⟩, rfl⟩, hX⟩

theorem reachOut_symm {α : Type u} {β : Type v} {G : Graph α β} {Y : Set α} {a b : α}
    (hab : ReachOut G Y a b) (ha : a ∉ Y) : ReachOut G Y b a := by
  suffices key : ReachOut G Y b a ∧ b ∉ Y from key.1
  induction hab with
  | refl => exact ⟨Relation.ReflTransGen.refl, ha⟩
  | tail _ hst ih =>
    obtain ⟨⟨e, hl⟩, hz⟩ := hst
    exact ⟨Relation.ReflTransGen.head ⟨⟨e, hl.symm⟩, ih.2⟩ ih.1, hz⟩

/-- Walking along row `y` from column `a` to column `b ≥ a`, both ways. -/
theorem reach_row {y a b : ℕ} (hab : a ≤ b)
    (hW : ∀ c, a ≤ c → c ≤ b → (c, y) ∈ elementaryWallVerts h)
    (hX : ∀ c, a ≤ c → c ≤ b → some (c, y) ∉ X) :
    ReachOut (apexWall h) X (some (a, y)) (some (b, y)) ∧
      ReachOut (apexWall h) X (some (b, y)) (some (a, y)) := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | succ b hab ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun c h1 h2 => hW c h1 (by omega)) (fun c h1 h2 => hX c h1 (by omega))
    have hadj := adj_right (hW b hab (by omega)) (hW (b + 1) (by omega) le_rfl)
    exact ⟨ih1.tail (stepOut_ww hadj (hX (b + 1) (by omega) le_rfl)),
      Relation.ReflTransGen.head (stepOut_ww (elementaryWallAdj_symm hadj)
        (hX b hab (by omega))) ih2⟩

/-- **Up a staircase.** From `(a, b)` with `a + b` odd, go up one row, then right one column, and
so on, until a side is reached. The vertices of the staircase after `(a, b)` are the `(c, d)` with
`d + a = c + b + 1` and `a ≤ c`, and those with `c + b = d + a` and `a < c`. -/
theorem reach_stair_up (hX0 : none ∉ X) :
    ∀ n a b, b + n = h → (a, b) ∈ elementaryWallVerts h → (a + b) % 2 = 1 →
      (∀ c d, d + a = c + b + 1 → a ≤ c → some (c, d) ∉ X) →
      (∀ c d, c + b = d + a → a < c → some (c, d) ∉ X) →
      ReachOut (apexWall h) X (some (a, b)) none := by
  intro n
  induction n with
  | zero =>
    intro a b hb hab _ _ _
    exact .single (stepOut_wn hab (Or.inr (Or.inl (by show b = h; omega))) hX0)
  | succ n ih =>
    intro a b hb hab hodd hX1 hX2
    by_cases hs : IsSideVert h (a, b)
    · exact .single (stepOut_wn hab hs hX0)
    simp only [IsSideVert, not_or] at hs
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    have hab' := hab
    rw [mem_elementaryWallVerts_iff] at hab'
    have h1 : (a, b + 1) ∈ elementaryWallVerts h := by memW
    have s1 := stepOut_ww (X := X) (adj_up hab h1 hodd) (hX1 a (b + 1) (by omega) le_rfl)
    by_cases hb1 : b + 1 = h
    · exact (Relation.ReflTransGen.single s1).tail
        (stepOut_wn h1 (Or.inr (Or.inl (by show b + 1 = h; omega))) hX0)
    have h2 : (a + 1, b + 1) ∈ elementaryWallVerts h := by memW
    have s2 := stepOut_ww (X := X) (adj_right h1 h2) (hX2 (a + 1) (b + 1) (by omega) (by omega))
    refine Relation.ReflTransGen.head s1 (Relation.ReflTransGen.head s2 ?_)
    exact ih (a + 1) (b + 1) (by omega) h2 (by omega)
      (fun c d e1 e2 => hX1 c d (by omega) (by omega))
      (fun c d e1 e2 => hX2 c d (by omega) (by omega))

/-- **Down a staircase.** From `(a, b)` with `a + b` even, go down one row, then left one column,
and so on, until a side is reached. The vertices of the staircase after `(a, b)` are the `(c, d)`
with `c + b = d + a + 1` and `d < b`, and those with `c + b = d + a`, `c < a` and `d < b`. -/
theorem reach_stair_down (hX0 : none ∉ X) :
    ∀ b a, (a, b) ∈ elementaryWallVerts h → (a + b) % 2 = 0 →
      (∀ c d, c + b = d + a + 1 → d < b → some (c, d) ∉ X) →
      (∀ c d, c + b = d + a → c < a → d < b → some (c, d) ∉ X) →
      ReachOut (apexWall h) X (some (a, b)) none := by
  intro b
  induction b with
  | zero => intro a hab _ _ _; exact .single (stepOut_wn hab (Or.inl rfl) hX0)
  | succ b ih =>
    intro a hab heven hX1 hX2
    by_cases hs : IsSideVert h (a, b + 1)
    · exact .single (stepOut_wn hab hs hX0)
    simp only [IsSideVert, not_or] at hs
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
    have hab' := hab
    rw [mem_elementaryWallVerts_iff] at hab'
    have h1 : (a, b) ∈ elementaryWallVerts h := by memW
    have s1 := stepOut_ww (X := X) (elementaryWallAdj_symm (adj_up h1 hab (by omega)))
      (hX1 a b (by omega) (by omega))
    by_cases hb0 : b = 0
    · subst hb0
      exact (Relation.ReflTransGen.single s1).tail (stepOut_wn h1 (Or.inl rfl) hX0)
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have h2 : (a', b) ∈ elementaryWallVerts h := by memW
    have s2 := stepOut_ww (X := X) (elementaryWallAdj_symm (adj_right h2 h1))
      (hX2 a' b (by omega) (by omega) (by omega))
    refine Relation.ReflTransGen.head s1 (Relation.ReflTransGen.head s2 ?_)
    exact ih a' h2 (by omega) (fun c d e1 e2 => hX1 c d (by omega) (by omega))
      (fun c d e1 e2 e3 => hX2 c d (by omega) (by omega) (by omega))

/-- Of three disjoint sets, a set of at most two elements misses one. -/
theorem disjoint_of_three {γ : Type*} {Y A B C : Set γ} (hYf : Y.Finite) (hY : Y.ncard ≤ 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    Disjoint Y A ∨ Disjoint Y B ∨ Disjoint Y C := by
  by_contra hn
  simp only [not_or, not_disjoint_iff] at hn
  obtain ⟨⟨a, haY, haA⟩, ⟨b, hbY, hbB⟩, ⟨c, hcY, hcC⟩⟩ := hn
  have hab : a ≠ b := fun e => disjoint_left.mp hAB haA (e ▸ hbB)
  have hac : a ≠ c := fun e => disjoint_left.mp hAC haA (e ▸ hcC)
  have hbc : b ≠ c := fun e => disjoint_left.mp hBC hbB (e ▸ hcC)
  have h3 : ({a, b, c} : Set γ).ncard = 3 := ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub : ({a, b, c} : Set γ) ⊆ Y := by
    rintro z (rfl | rfl | rfl)
    · exact haY
    · exact hbY
    · exact hcY
  have := ncard_le_ncard hsub hYf
  omega

/-- **If the new vertex is kept, every vertex of the wall reaches it**, when at most two vertices
are deleted. A vertex inside the wall has three paths to the sides that meet only at the vertex:
along its row to the left, along its row to the right, and along a staircase. -/
theorem reach_inf (hXf : X.Finite) (hX : X.ncard ≤ 2) (hX0 : none ∉ X) {p : ℕ × ℕ}
    (hp : p ∈ elementaryWallVerts h) (hpX : some p ∉ X) :
    ReachOut (apexWall h) X (some p) none := by
  by_cases hs : IsSideVert h p
  · exact .single (stepOut_wn hp hs hX0)
  obtain ⟨x, y⟩ := p
  simp only [IsSideVert, not_or] at hs
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
  have hp' := hp
  rw [mem_elementaryWallVerts_iff] at hp'
  let A : Set (Option (ℕ × ℕ)) := {z | ∃ c < x, z = some (c, y)}
  let B : Set (Option (ℕ × ℕ)) := {z | ∃ c, x < c ∧ z = some (c, y)}
  let C : Set (Option (ℕ × ℕ)) := {z | ∃ c d, z = some (c, d) ∧ d ≠ y ∧
    (((x + y) % 2 = 1 ∧ ((d + x = c + y + 1 ∧ x ≤ c) ∨ (c + y = d + x ∧ x < c))) ∨
      ((x + y) % 2 = 0 ∧ ((c + y = d + x + 1 ∧ d < y) ∨ (c + y = d + x ∧ c < x ∧ d < y))))}
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ ⟨c', hc', e⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    omega
  have hAC : Disjoint A C := by
    rw [disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ ⟨c', d, e, hd, -⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    omega
  have hBC : Disjoint B C := by
    rw [disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ ⟨c', d, e, hd, -⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    omega
  rcases disjoint_of_three hXf hX hAB hAC hBC with hA | hB | hC
  · -- along the row to the left side
    have hr := (reach_row (h := h) (X := X) (y := y) (Nat.zero_le x) (fun c _ hc => by memW)
      (fun c _ hc => by
        rcases Nat.lt_or_ge c x with hcx | hcx
        · exact disjoint_left.mp hA.symm ⟨c, hcx, rfl⟩
        · obtain rfl : c = x := by omega
          exact hpX)).2
    exact hr.tail (stepOut_wn (by memW) (Or.inr (Or.inr (Or.inl rfl))) hX0)
  · -- along the row to the right side
    have hr := (reach_row (h := h) (X := X) (y := y) (a := x) (b := 2 * h + 1) (by omega)
      (fun c _ hc => by memW)
      (fun c hc _ => by
        rcases Nat.lt_or_ge x c with hcx | hcx
        · exact disjoint_left.mp hB.symm ⟨c, hcx, rfl⟩
        · obtain rfl : c = x := by omega
          exact hpX)).1
    exact hr.tail (stepOut_wn (by memW) (Or.inr (Or.inr (Or.inr rfl))) hX0)
  · -- along a staircase
    have hnC : ∀ c d, some (c, d) ∈ C → some (c, d) ∉ X := fun c d hcd hX' =>
      disjoint_left.mp hC hX' hcd
    rcases Nat.mod_two_eq_zero_or_one (x + y) with he | ho
    · exact reach_stair_down hX0 y x hp he
        (fun c d e1 e2 => hnC c d ⟨c, d, rfl, by omega, Or.inr ⟨he, Or.inl ⟨e1, e2⟩⟩⟩)
        (fun c d e1 e2 e3 => hnC c d ⟨c, d, rfl, by omega, Or.inr ⟨he, Or.inr ⟨e1, e2, e3⟩⟩⟩)
    · exact reach_stair_up hX0 (h - y) x y (by omega) hp ho
        (fun c d e1 e2 => hnC c d ⟨c, d, rfl, by omega, Or.inl ⟨ho, Or.inl ⟨e1, e2⟩⟩⟩)
        (fun c d e1 e2 => hnC c d ⟨c, d, rfl, by omega, Or.inl ⟨ho, Or.inr ⟨e1, e2⟩⟩⟩)

/-! ### When the new vertex is deleted

Then at most one vertex `x` of the wall is deleted as well. We do not ask that `x` is a vertex of
the wall. -/

section NoInf

variable (x : ℕ × ℕ) (hXx : ∀ p, some p ∈ X → p = x)
include hXx

theorem not_mem_of_ne {q : ℕ × ℕ} (hq : q ≠ x) : some q ∉ X := fun h' => hq (hXx q h')

theorem not_mem_of_row {c y : ℕ} (hy : y ≠ x.2) : some (c, y) ∉ X :=
  not_mem_of_ne x hXx fun e => hy (by rw [← e])

/-- In a row other than the row of `x`, every vertex reaches the vertex in column `1`. -/
theorem reach_rep {c y : ℕ} (hy : y ≠ x.2) (hc : (c, y) ∈ elementaryWallVerts h) :
    ReachOut (apexWall h) X (some (c, y)) (some (1, y)) := by
  have hc' := hc
  rw [mem_elementaryWallVerts_iff] at hc'
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · exact .single (stepOut_ww (adj_right hc (by memW)) (not_mem_of_row x hXx hy))
  · exact (reach_row (h := h) (X := X) (y := y) (a := 1) (b := c) hc0 (fun c' h1 h2 => by memW)
      (fun c' _ _ => not_mem_of_row x hXx hy)).2

/-- Two consecutive rows other than the row of `x` are joined by a vertical edge. -/
theorem reach_rep_succ {y : ℕ} (hy1 : y ≠ x.2) (hy2 : y + 1 ≠ x.2) (hyh : y + 1 ≤ h) :
    ReachOut (apexWall h) X (some (1, y)) (some (1, y + 1)) := by
  rcases Nat.mod_two_eq_zero_or_one y with he | ho
  · exact .single (stepOut_ww (adj_up (by memW) (by memW) (by omega)) (not_mem_of_row x hXx hy2))
  · have h0 : (0, y) ∈ elementaryWallVerts h := by memW
    have h0' : (0, y + 1) ∈ elementaryWallVerts h := by memW
    refine .head (stepOut_ww (elementaryWallAdj_symm (adj_right h0 (by memW)))
      (not_mem_of_row x hXx hy1)) ?_
    refine .head (stepOut_ww (adj_up h0 h0' (by omega)) (not_mem_of_row x hXx hy2)) ?_
    exact .single (stepOut_ww (adj_right h0' (by memW)) (not_mem_of_row x hXx hy2))

/-- The rows just below and just above `x` are joined around `x`, through the first two columns or
the last two columns of the row of `x`. -/
theorem reach_rep_around (he : Even h) {k : ℕ} (hk : k + 1 = x.2) (hkh : k + 2 ≤ h) :
    ReachOut (apexWall h) X (some (1, k)) (some (1, k + 2)) := by
  obtain ⟨m, hm⟩ := he
  have hr0 : k ≠ x.2 := by omega
  have hr2 : k + 2 ≠ x.2 := by omega
  rcases Nat.lt_or_ge x.1 2 with hx | hx
  · -- around the right end
    have hn : ∀ c, 2 ≤ c → some (c, k + 1) ∉ X := fun c hc =>
      not_mem_of_ne x hXx fun e => by rw [← e] at hx; simp only at hx; omega
    have row0 := reach_row (h := h) (X := X) (y := k) (a := 1) (b := 2 * h + 1) (by omega)
      (fun c _ _ => by memW) (fun c _ _ => not_mem_of_row x hXx hr0)
    have row0' := reach_row (h := h) (X := X) (y := k) (a := 1) (b := 2 * h) (by omega)
      (fun c _ _ => by memW) (fun c _ _ => not_mem_of_row x hXx hr0)
    rcases Nat.mod_two_eq_zero_or_one k with hke | hko
    · have row2 := reach_row (h := h) (X := X) (y := k + 2) (a := 1) (b := 2 * h) (by omega)
        (fun c _ _ => by memW) (fun c _ _ => not_mem_of_row x hXx hr2)
      refine row0.1.trans (.head (stepOut_ww (adj_up (by memW) (by memW) (by omega))
        (hn _ (by omega))) ?_)
      refine .head (stepOut_ww (elementaryWallAdj_symm (adj_right (by memW) (by memW)))
        (hn _ (by omega))) ?_
      refine .head (stepOut_ww (adj_up (h := h) (x := 2 * h) (y := k + 1) (by memW) (by memW)
        (by omega)) (not_mem_of_row x hXx hr2)) ?_
      exact row2.2
    · have row2 := reach_row (h := h) (X := X) (y := k + 2) (a := 1) (b := 2 * h + 1) (by omega)
        (fun c _ _ => by memW) (fun c _ _ => not_mem_of_row x hXx hr2)
      refine row0'.1.trans (.head (stepOut_ww (adj_up (by memW) (by memW) (by omega))
        (hn _ (by omega))) ?_)
      refine .head (stepOut_ww (adj_right (by memW) (by memW)) (hn _ (by omega))) ?_
      refine .head (stepOut_ww (adj_up (h := h) (x := 2 * h + 1) (y := k + 1) (by memW) (by memW)
        (by omega)) (not_mem_of_row x hXx hr2)) ?_
      exact row2.2
  · -- around the left end
    have hn : ∀ c, c ≤ 1 → some (c, k + 1) ∉ X := fun c hc =>
      not_mem_of_ne x hXx fun e => by rw [← e] at hx; simp only at hx; omega
    rcases Nat.mod_two_eq_zero_or_one k with hke | hko
    · refine .head (stepOut_ww (adj_up (by memW) (by memW) (by omega)) (hn 1 le_rfl)) ?_
      refine .head (stepOut_ww (elementaryWallAdj_symm (adj_right (h := h) (x := 0) (y := k + 1)
        (by memW) (by memW))) (hn 0 (by omega))) ?_
      refine .head (stepOut_ww (adj_up (h := h) (x := 0) (y := k + 1) (by memW) (by memW)
        (by omega)) (not_mem_of_row x hXx hr2)) ?_
      exact .single (stepOut_ww (adj_right (by memW) (by memW)) (not_mem_of_row x hXx hr2))
    · refine .head (stepOut_ww (elementaryWallAdj_symm (adj_right (h := h) (x := 0) (y := k)
        (by memW) (by memW))) (not_mem_of_row x hXx hr0)) ?_
      refine .head (stepOut_ww (adj_up (h := h) (x := 0) (y := k) (by memW) (by memW) (by omega))
        (hn 0 (by omega))) ?_
      refine .head (stepOut_ww (adj_right (h := h) (x := 0) (y := k + 1) (by memW) (by memW))
        (hn 1 le_rfl)) ?_
      exact .single (stepOut_ww (adj_up (by memW) (by memW) (by omega)) (not_mem_of_row x hXx hr2))

/-- A vertex in the row of `x` reaches the vertex in column `1` of another row: along its vertical
edge, or through a neighbour in its row that has one. -/
theorem reach_rep_of_row (he : Even h) (hh : 2 ≤ h) {c : ℕ}
    (hc : (c, x.2) ∈ elementaryWallVerts h) (hcx : (c, x.2) ≠ x) :
    ∃ y', y' ≠ x.2 ∧ y' ≤ h ∧ ReachOut (apexWall h) X (some (c, x.2)) (some (1, y')) := by
  obtain ⟨m, hm⟩ := he
  have hc' := hc
  rw [mem_elementaryWallVerts_iff] at hc'
  set y0 := x.2 with hy0
  have hn : ∀ {c' y'}, (c', y') ≠ x → some (c', y') ∉ X := fun e => not_mem_of_ne x hXx e
  by_cases hup : (c + y0) % 2 = 1 ∧ y0 < h ∧ ¬ (c = 2 * h + 1 ∧ y0 + 1 = h)
  · have h1 : (c, y0 + 1) ∈ elementaryWallVerts h := by memW
    have hy : y0 + 1 ≠ x.2 := by omega
    exact ⟨y0 + 1, hy, by omega, .head (stepOut_ww (adj_up hc h1 hup.1)
      (not_mem_of_row x hXx hy)) (reach_rep x hXx hy h1)⟩
  by_cases hdown : (c + y0) % 2 = 0 ∧ 1 ≤ y0 ∧ ¬ (c = 0 ∧ y0 = 1)
  · obtain ⟨k, hk⟩ : ∃ k, y0 = k + 1 := ⟨y0 - 1, by omega⟩
    have h1 : (c, k) ∈ elementaryWallVerts h := by memW
    have hy : k ≠ x.2 := by omega
    have hadj := elementaryWallAdj_symm (adj_up (h := h) (x := c) (y := k) h1 (by rw [← hk]; exact hc)
      (by omega))
    rw [← hk] at hadj
    exact ⟨k, hy, by omega, .head (stepOut_ww hadj (not_mem_of_row x hXx hy))
      (reach_rep x hXx hy h1)⟩
  rcases Nat.mod_two_eq_zero_or_one (c + y0) with hpar | hpar
  · -- the bottom row, `c` even: a neighbour `c ± 1` has an edge up
    have hy0 : y0 = 0 := by omega
    have hy1 : (1 : ℕ) ≠ x.2 := by omega
    have key : ∀ n, (n = c - 1 ∨ n = c + 1) → (n, y0) ≠ x →
        ReachOut (apexWall h) X (some (c, x.2)) (some (1, 1)) := by
      intro n hn' hnx
      have hnW : (n, y0) ∈ elementaryWallVerts h := by memW
      have hn1 : (n, 1) ∈ elementaryWallVerts h := by memW
      have hadj : elementaryWallAdj h (c, y0) (n, y0) := by
        rcases hn' with rfl | rfl
        · have := adj_right (h := h) (x := c - 1) (y := y0) hnW
            (by rw [show c - 1 + 1 = c by omega]; exact hc)
          rw [show c - 1 + 1 = c by omega] at this
          exact elementaryWallAdj_symm this
        · exact adj_right hc hnW
      refine .head (stepOut_ww hadj (hn hnx)) ?_
      have hup' := adj_up (h := h) (x := n) (y := y0) hnW (by rw [hy0]; exact hn1) (by omega)
      rw [hy0] at hup' ⊢
      exact .head (stepOut_ww hup' (not_mem_of_row x hXx hy1)) (reach_rep x hXx hy1 hn1)
    by_cases hl : (c - 1, y0) = x
    · exact ⟨1, hy1, by omega, key (c + 1) (Or.inr rfl) fun e => by
        rw [← hl] at e; simp only [Prod.mk.injEq] at e; omega⟩
    · exact ⟨1, hy1, by omega, key (c - 1) (Or.inl rfl) hl⟩
  · -- the top row, `c` odd: a neighbour `c ± 1` has an edge down
    have hyh : y0 = h := by omega
    have hy1 : h - 1 ≠ x.2 := by omega
    have key : ∀ n, (n = c - 1 ∨ n = c + 1) → (n, y0) ≠ x →
        ReachOut (apexWall h) X (some (c, x.2)) (some (1, h - 1)) := by
      intro n hn' hnx
      have hnW : (n, y0) ∈ elementaryWallVerts h := by memW
      have hn1 : (n, h - 1) ∈ elementaryWallVerts h := by memW
      have hadj : elementaryWallAdj h (c, y0) (n, y0) := by
        rcases hn' with rfl | rfl
        · have := adj_right (h := h) (x := c - 1) (y := y0) hnW
            (by rw [show c - 1 + 1 = c by omega]; exact hc)
          rw [show c - 1 + 1 = c by omega] at this
          exact elementaryWallAdj_symm this
        · exact adj_right hc hnW
      refine .head (stepOut_ww hadj (hn hnx)) ?_
      have hdn := adj_up (h := h) (x := n) (y := h - 1) hn1
        (by rw [show h - 1 + 1 = y0 by omega]; exact hnW) (by omega)
      rw [show h - 1 + 1 = y0 by omega] at hdn
      exact .head (stepOut_ww (elementaryWallAdj_symm hdn) (not_mem_of_row x hXx hy1))
        (reach_rep x hXx hy1 hn1)
    by_cases hl : (c - 1, y0) = x
    · exact ⟨h - 1, hy1, by omega, key (c + 1) (Or.inr rfl) fun e => by
        rw [← hl] at e; simp only [Prod.mk.injEq] at e; omega⟩
    · exact ⟨h - 1, hy1, by omega, key (c - 1) (Or.inl rfl) hl⟩

/-- Rows from `y₁` up to `y`, none of them the row of `x`, are joined. -/
theorem reach_rep_down {y₁ y : ℕ} (hle : y₁ ≤ y) (hyh : y ≤ h)
    (hz : ∀ z, y₁ ≤ z → z ≤ y → z ≠ x.2) :
    ReachOut (apexWall h) X (some (1, y)) (some (1, y₁)) := by
  induction y, hle using Nat.le_induction with
  | base => exact .refl
  | succ y hle ih =>
    have h1 := reach_rep_succ x hXx (hz y hle (by omega)) (hz (y + 1) (by omega) le_rfl) hyh
    exact (reachOut_symm h1 (not_mem_of_row x hXx (hz y hle (by omega)))).trans
      (ih (by omega) (fun z h1 h2 => hz z h1 (by omega)))

/-- **If the new vertex is deleted, the wall without `x` is connected.** Every vertex reaches the
vertex in column `1` of row `0`, or of row `1` when `x` is in row `0`. -/
theorem reach_noinf (hh : 2 ≤ h) (he : Even h) {p q : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h)
    (hq : q ∈ elementaryWallVerts h) (hpx : p ≠ x) (hqx : q ≠ x) :
    ReachOut (apexWall h) X (some p) (some q) := by
  set ys := if x.2 = 0 then 1 else 0 with hys
  have hA : ∀ y, y ≤ h → y ≠ x.2 → ReachOut (apexWall h) X (some (1, y)) (some (1, ys)) := by
    intro y hyh hy
    by_cases e : x.2 = 0
    · simp only [hys, e, if_true]
      exact reach_rep_down (h := h) x hXx (y₁ := 1) (by omega) hyh (fun z h1 _ => by omega)
    · simp only [hys, e, if_false]
      rcases Nat.lt_or_gt_of_ne hy with hlt | hgt
      · exact reach_rep_down (h := h) x hXx (Nat.zero_le y) hyh (fun z _ h2 => by omega)
      · obtain ⟨k, hk⟩ : ∃ k, x.2 = k + 1 := ⟨x.2 - 1, by omega⟩
        have r1 := reach_rep_down (h := h) x hXx (y₁ := k + 2) (y := y) (by omega) hyh
          (fun z h1 _ => by omega)
        have r2 := reachOut_symm (reach_rep_around (h := h) x hXx he hk.symm (by omega))
          (not_mem_of_row x hXx (by omega))
        have r3 := reach_rep_down (h := h) x hXx (y₁ := 0) (y := k) (Nat.zero_le k) (by omega)
          (fun z _ h2 => by omega)
        exact r1.trans (r2.trans r3)
  have hB : ∀ r ∈ elementaryWallVerts h, r ≠ x →
      ReachOut (apexWall h) X (some r) (some (1, ys)) := by
    intro r hr hrx
    obtain ⟨c, y⟩ := r
    have hr' := hr
    rw [mem_elementaryWallVerts_iff] at hr'
    by_cases hy : y = x.2
    · rw [hy] at hr hrx ⊢
      obtain ⟨y', hy', hy'h, hr''⟩ := reach_rep_of_row x hXx he hh hr hrx
      exact hr''.trans (hA y' hy'h hy')
    · exact (reach_rep x hXx hy hr).trans (hA y hr'.2.1 hy)
  exact (hB p hp hpx).trans (reachOut_symm (hB q hq hqx) (not_mem_of_ne x hXx hqx))

end NoInf

/-- Proves that two options of points differ, by arithmetic. -/
macro "ne_tac" : tactic => `(tactic| (simp only [ne_eq, reduceCtorEq, not_false_eq_true,
  Option.some.injEq, Prod.mk.injEq] <;> omega))

theorem injective_three {γ : Type*} {a b c : γ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem injective_four {γ : Type*} {a b c d : γ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- **The elementary wall with the vertex at infinity stays connected when two vertices are
deleted**, for `h ≥ 2` even. -/
theorem apexWall_connGood (hh : 2 ≤ h) (he : Even h) : ConnGood (apexWall h) := by
  have hfinW : (elementaryWallVerts h).Finite := elementaryWall_finite_V h
  have hfinV : V(apexWall h).Finite := (hfinW.image _).insert none
  refine ⟨hfinV, ?_, ?_, ?_, ?_, ?_⟩
  · refine ((hfinV.prod hfinV).image fun ab => s(ab.1, ab.2)).subset ?_
    rintro e ⟨a, b, hab, rfl⟩
    exact ⟨(a, b), ⟨(apexWall h).left_mem_of_isLink ⟨hab, rfl⟩,
      (apexWall h).left_mem_of_isLink ⟨apexAdj_symm hab, rfl⟩⟩, rfl⟩
  · intro e v hl
    exact apexAdj_irrefl v hl.1
  · intro e f u v he hf
    exact he.2.trans hf.2.symm
  · have hs : ∀ p, p ∈ elementaryWallVerts h → IsSideVert h p →
        apexAdj h (some p) none := fun p hp hs => ⟨hp, hs⟩
    have lk : ∀ {a b}, apexAdj h a b → ∃ e, (apexWall h).IsLink e a b := fun hab => ⟨_, hab, rfl⟩
    refine ⟨![some (1, 0), some (2 * h + 1, 0), some (0, h), some (2 * h, h)],
      injective_four (by ne_tac) (by ne_tac) (by ne_tac) (by ne_tac) (by ne_tac) (by ne_tac),
      fun i => ?_⟩
    fin_cases i
    · refine ⟨Or.inr ⟨(1, 0), by memW, rfl⟩, ![some (2, 0), some (1, 1), none],
        injective_three (by ne_tac) (by ne_tac) (by ne_tac), fun j => ?_⟩
      fin_cases j
      · exact lk (adj_right (h := h) (x := 1) (y := 0) (by memW) (by memW))
      · exact lk (adj_up (h := h) (x := 1) (y := 0) (by memW) (by memW) (by omega))
      · exact lk (hs (1, 0) (by memW) (Or.inl rfl))
    · refine ⟨Or.inr ⟨(2 * h + 1, 0), by memW, rfl⟩, ![some (2 * h, 0), some (2 * h + 1, 1), none],
        injective_three (by ne_tac) (by ne_tac) (by ne_tac), fun j => ?_⟩
      fin_cases j
      · exact lk (elementaryWallAdj_symm (adj_right (h := h) (x := 2 * h) (y := 0) (by memW)
          (by memW)))
      · exact lk (adj_up (h := h) (x := 2 * h + 1) (y := 0) (by memW) (by memW) (by omega))
      · exact lk (hs _ (by memW) (Or.inl rfl))
    · obtain ⟨m, hm⟩ := he
      refine ⟨Or.inr ⟨(0, h), by memW, rfl⟩, ![some (1, h), some (0, h - 1), none],
        injective_three (by ne_tac) (by ne_tac) (by ne_tac), fun j => ?_⟩
      fin_cases j
      · exact lk (adj_right (h := h) (x := 0) (y := h) (by memW) (by memW))
      · have := adj_up (h := h) (x := 0) (y := h - 1) (by memW)
          (by rw [show h - 1 + 1 = h by omega]; memW) (by omega)
        rw [show h - 1 + 1 = h by omega] at this
        exact lk (elementaryWallAdj_symm this)
      · exact lk (hs _ (by memW) (Or.inr (Or.inl rfl)))
    · obtain ⟨m, hm⟩ := he
      refine ⟨Or.inr ⟨(2 * h, h), by memW, rfl⟩, ![some (2 * h - 1, h), some (2 * h, h - 1), none],
        injective_three (by ne_tac) (by ne_tac) (by ne_tac), fun j => ?_⟩
      fin_cases j
      · have := adj_right (h := h) (x := 2 * h - 1) (y := h) (by memW)
          (by rw [show 2 * h - 1 + 1 = 2 * h by omega]; memW)
        rw [show 2 * h - 1 + 1 = 2 * h by omega] at this
        exact lk (elementaryWallAdj_symm this)
      · have := adj_up (h := h) (x := 2 * h) (y := h - 1) (by memW)
          (by rw [show h - 1 + 1 = h by omega]; memW) (by omega)
        rw [show h - 1 + 1 = h by omega] at this
        exact lk (elementaryWallAdj_symm this)
      · exact lk (hs _ (by memW) (Or.inr (Or.inl rfl)))
  · intro X hXV hX a ha haX b hb hbX
    have hXf : X.Finite := hfinV.subset hXV
    have toW : ∀ {a}, a ∈ V(apexWall h) → a ≠ none → ∃ p ∈ elementaryWallVerts h, a = some p := by
      rintro a (rfl | ⟨p, hp, rfl⟩) hne
      · exact absurd rfl hne
      · exact ⟨p, hp, rfl⟩
    by_cases h0 : none ∈ X
    · obtain ⟨p, hp, rfl⟩ := toW ha fun e => haX (e ▸ h0)
      obtain ⟨q, hq, rfl⟩ := toW hb fun e => hbX (e ▸ h0)
      -- at most one vertex of the wall is deleted
      have huniq : ∀ p₁ p₂, some p₁ ∈ X → some p₂ ∈ X → p₁ = p₂ := by
        intro p₁ p₂ h1 h2
        by_contra hne
        have h3 : ({none, some p₁, some p₂} : Set (Option (ℕ × ℕ))).ncard = 3 :=
          ncard_eq_three.mpr ⟨_, _, _, by simp, by simp, by simpa using hne, rfl⟩
        have hsub : ({none, some p₁, some p₂} : Set (Option (ℕ × ℕ))) ⊆ X := by
          rintro z (rfl | rfl | rfl)
          · exact h0
          · exact h1
          · exact h2
        have := ncard_le_ncard hsub hXf
        omega
      by_cases hx : ∃ x, some x ∈ X
      · obtain ⟨x, hx⟩ := hx
        exact reach_noinf x (fun p' hp' => huniq p' x hp' hx) hh he hp hq
          (fun e => haX (e ▸ hx)) (fun e => hbX (e ▸ hx))
      · push Not at hx
        have h00 : ((0, 0) : ℕ × ℕ) ∉ elementaryWallVerts h := by
          rw [mem_elementaryWallVerts_iff]; omega
        exact reach_noinf (0, 0) (fun p' hp' => absurd hp' (hx p')) hh he hp hq
          (fun e => h00 (e ▸ hp)) (fun e => h00 (e ▸ hq))
    · have hinf : ∀ {c}, c ∈ V(apexWall h) → c ∉ X → ReachOut (apexWall h) X c none := by
        intro c hc hcX
        by_cases hc0 : c = none
        · rw [hc0]; exact .refl
        · obtain ⟨p, hp, rfl⟩ := toW hc hc0
          exact reach_inf hXf hX h0 hp hcX
      exact (hinf ha haX).trans (reachOut_symm (hinf hb hbX) hbX)

/-- **The elementary wall with the vertex at infinity is a subdivision of a simple 3-connected
graph**, and so is every graph isomorphic to it. -/
theorem isSubdivision_of_iso_apexWall {α : Type u} {β : Type v} {G : Graph α β} (hh : 2 ≤ h)
    (he : Even h) (φ : GraphMinor.Iso (apexWall h) G) :
    GraphMinor.GM14.IsSubdivisionOfSimpleThreeConnected G :=
  good_sub ((apexWall_connGood hh he).of_iso φ).good

end Apex

end GraphMinor.GM13
