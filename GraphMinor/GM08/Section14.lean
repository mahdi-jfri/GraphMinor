module

public import GraphMinor.GM08.Section13
public import GraphMinor.GM08.Section14Chain
public import GraphMinor.GM08.Section14Sim

/-!
# Graph Minors VIII, Section 14: Trains and Concatenations (pages 278–279)

This file completes the formalization of Section 14 of N. Robertson and P. D. Seymour,
*Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288:

- Graft isomorphism properties (`IsGraftIso.refl`, `IsGraftIso.symm`, `IsGraftIso.trans`,
  `isGraftSimulatedIn_of_isGraftIso`, `isWellRootedGraftClass_isoGraftClass`).
- `IsTwoPieceGluing`: splitting a 2-piece graft gluing along its shared boundary vertices into an
  isomorphic direct sum followed by finitely many vertex identifications.
- `theorem_14_3`: (14.3) (page 279), every $k$-train over $\mathscr{A}$ belongs to
  $W(\mathscr{A}^* \oplus \mathscr{B}^* \oplus \mathscr{A}^*) \cup
   W(\mathscr{A}^* \oplus \mathscr{A}^*) \cup \mathscr{A}$ where $\mathscr{B}$ is the class of all
  $k$-chains over $\mathscr{A}$.
- `theorem_14_4`: (14.4) (page 279), if $\mathscr{A}$ is well-rooted then so is $L^k(\mathscr{A})$.
- `theorem_14_5`: (14.5) (page 279), if $\mathscr{A}$ is well-rooted then the class of all
  concatenations over $\mathscr{A}$ is well-rooted.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Graph

universe u v u' v'

/-! ## Graft isomorphism and $\mathscr{A}^*$ -/

theorem IsGraftIso.refl {α : Type u} {β : Type v} (X : Graft α β) : IsGraftIso X X :=
  ⟨⟨Equiv.refl _, Equiv.refl _, fun _ _ _ => Iff.rfl⟩, fun _ => Iff.rfl⟩

theorem IsGraftIso.symm {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} (h : IsGraftIso Y X) : IsGraftIso X Y := by
  obtain ⟨φ, hT⟩ := h
  refine ⟨⟨φ.vertexEquiv.symm, φ.edgeEquiv.symm, fun e x y => ?_⟩, fun u => ?_⟩
  · have hlink := φ.isLink_iff (φ.edgeEquiv.symm e) (φ.vertexEquiv.symm x) (φ.vertexEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at hlink
    exact hlink.symm
  · have hu := hT (φ.vertexEquiv.symm u)
    simp only [Equiv.apply_symm_apply] at hu
    exact hu.symm

theorem IsGraftIso.trans {α₁ : Type*} {β₁ : Type*} {α₂ : Type*} {β₂ : Type*}
    {α₃ : Type*} {β₃ : Type*} {X₁ : Graft α₁ β₁} {X₂ : Graft α₂ β₂} {X₃ : Graft α₃ β₃}
    (h₁₂ : IsGraftIso X₁ X₂) (h₂₃ : IsGraftIso X₂ X₃) : IsGraftIso X₁ X₃ := by
  obtain ⟨φ₁, hT₁⟩ := h₁₂
  obtain ⟨φ₂, hT₂⟩ := h₂₃
  refine ⟨⟨φ₁.vertexEquiv.trans φ₂.vertexEquiv, φ₁.edgeEquiv.trans φ₂.edgeEquiv,
    fun e x y => (φ₁.isLink_iff e x y).trans (φ₂.isLink_iff _ _ _)⟩,
    fun u => (hT₁ u).trans (hT₂ (φ₁.vertexEquiv u))⟩

theorem subset_isoGraftClass {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) :
    𝒜 ⊆ isoGraftClass 𝒜 :=
  fun X hX => ⟨X, hX, IsGraftIso.refl X⟩

/-- If $Y$ is isomorphic to $X$, then $Y$ is simulated in $X$. -/
theorem isGraftSimulatedIn_of_isGraftIso {α : Type u} {β : Type v}
    {Y X : Graft α β} (h : IsGraftIso Y X) : IsGraftSimulatedIn Y X := by
  classical
  obtain ⟨φ, hT⟩ := h
  let ηv : α → Set α := fun u => if hu : u ∈ V(Y.G) then {(φ.vertexEquiv ⟨u, hu⟩).1} else ∅
  let ηe : β → β := fun e => if he : e ∈ E(Y.G) then (φ.edgeEquiv ⟨e, he⟩).1 else e
  have hηv_eq : ∀ {u : α} (hu : u ∈ V(Y.G)), ηv u = {(φ.vertexEquiv ⟨u, hu⟩).1} :=
    fun hu => by simp [ηv, hu]
  have hηe_eq : ∀ {e : β} (he : e ∈ E(Y.G)), ηe e = (φ.edgeEquiv ⟨e, he⟩).1 :=
    fun he => by simp [ηe, he]
  refine ⟨ηv, ηe, ?_, ?_, ?_⟩
  · refine {
      vertex_nonempty := fun u hu => by
        rw [hηv_eq hu]
        exact singleton_nonempty _
      vertex_subset := fun u hu x hx => by
        rw [hηv_eq hu, mem_singleton_iff] at hx
        exact hx ▸ (φ.vertexEquiv ⟨u, hu⟩).2
      edge_mem := fun e he => by
        rw [hηe_eq he]
        exact (φ.edgeEquiv ⟨e, he⟩).2
      vertex_disjoint := fun u₁ hu₁ u₂ hu₂ hne => by
        rw [hηv_eq hu₁, hηv_eq hu₂, disjoint_singleton]
        intro heq
        apply hne
        have hsub : φ.vertexEquiv ⟨u₁, hu₁⟩ = φ.vertexEquiv ⟨u₂, hu₂⟩ := Subtype.ext heq
        exact congrArg Subtype.val (φ.vertexEquiv.injective hsub)
      edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
        rw [hηe_eq he₁, hηe_eq he₂] at heq
        have hsub : φ.edgeEquiv ⟨e₁, he₁⟩ = φ.edgeEquiv ⟨e₂, he₂⟩ := Subtype.ext heq
        exact congrArg Subtype.val (φ.edgeEquiv.injective hsub)
      inc_iff := fun u hu e he => by
        rw [hηv_eq hu, hηe_eq he]
        simp only [mem_singleton_iff, exists_eq_left]
        constructor
        · rintro ⟨w, hlink⟩
          have hw : w ∈ V(Y.G) := hlink.right_mem
          have hlink' := (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨w, hw⟩).mp hlink
          exact hlink'.inc_left
        · rintro ⟨x, hlink'⟩
          have hx : x ∈ V(X.G) := hlink'.right_mem
          let w := φ.vertexEquiv.symm ⟨x, hx⟩
          have hlink : Y.G.IsLink e u w.1 := by
            have := (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ w).mpr
              (by simpa [w] using hlink')
            exact this
          exact hlink.inc_left
      isLoopAt_iff := fun u hu e he => by
        rw [hηv_eq hu, hηe_eq he]
        simp only [mem_singleton_iff]
        constructor
        · intro hloop x ⟨y, hl⟩
          have hl_loop : X.G.IsLink (φ.edgeEquiv ⟨e, he⟩).1
              (φ.vertexEquiv ⟨u, hu⟩).1 (φ.vertexEquiv ⟨u, hu⟩).1 :=
            (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨u, hu⟩).mp hloop
          rcases hl.eq_and_eq_or_eq_and_eq hl_loop with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
        · intro hall
          have heX : (φ.edgeEquiv ⟨e, he⟩).1 ∈ E(X.G) := (φ.edgeEquiv ⟨e, he⟩).2
          obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet heX
          have hx := hall x hl.inc_left
          have hy := hall y hl.inc_right
          subst hx hy
          exact (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨u, hu⟩).mpr hl
      connected := fun u hu => by
        let x₀ := (φ.vertexEquiv ⟨u, hu⟩).1
        have hx₀_mem : x₀ ∈ V(X.G.deleteEdges (ηe '' E(Y.G))) := (φ.vertexEquiv ⟨u, hu⟩).2
        let K := (X.G.deleteEdges (ηe '' E(Y.G))).induce {x₀}
        have hK_le : K ≤ X.G.deleteEdges (ηe '' E(Y.G)) :=
          (X.G.deleteEdges (ηe '' E(Y.G))).induce_le (singleton_subset_iff.mpr hx₀_mem)
        have hVK : V(K) = ηv u := by
          rw [vertexSet_induce, hηv_eq hu]
        refine ⟨K, hK_le, hVK, ⟨x₀, by simp [K]⟩, ?_⟩
        intro a ha b hb
        rw [vertexSet_induce, mem_singleton_iff] at ha hb
        subst ha hb
        exact Relation.ReflTransGen.refl }
  · have hbij : Set.BijOn (fun u => if hu : u ∈ V(Y.G) then (φ.vertexEquiv ⟨u, hu⟩).1 else u)
        Y.T X.T := by
      refine ⟨fun u hu => ?_, fun u₁ hu₁ u₂ hu₂ heq => ?_, fun x hx => ?_⟩
      · have huV : u ∈ V(Y.G) := Y.T_subset hu
        simp only [huV, ↓reduceDIte]
        exact (hT ⟨u, huV⟩).mp hu
      · have hu₁V : u₁ ∈ V(Y.G) := Y.T_subset hu₁
        have hu₂V : u₂ ∈ V(Y.G) := Y.T_subset hu₂
        simp only [hu₁V, hu₂V, ↓reduceDIte] at heq
        exact congrArg Subtype.val (φ.vertexEquiv.injective (Subtype.ext heq))
      · have hxV : x ∈ V(X.G) := X.T_subset hx
        let u := φ.vertexEquiv.symm ⟨x, hxV⟩
        have huT : u.1 ∈ Y.T := (hT u).mpr (by simpa [u] using hx)
        refine ⟨u.1, huT, ?_⟩
        simp [u, u.2]
    exact (Set.BijOn.ncard_eq hbij).symm
  · intro u hu
    have huV : u ∈ V(Y.G) := Y.T_subset hu
    refine ⟨(φ.vertexEquiv ⟨u, huV⟩).1, ?_, (hT ⟨u, huV⟩).mp hu⟩
    rw [hηv_eq huV]
    exact mem_singleton _

/-- Graph Minors VIII, Section 14 (page 279):
"Evidently if $\mathscr{A}$ is well-rooted then so is $\mathscr{A}^*$." -/
theorem isWellRootedGraftClass_isoGraftClass {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} (h𝒜 : IsWellRootedGraftClass 𝒜) :
    IsWellRootedGraftClass (isoGraftClass 𝒜) := by
  intro X hX
  choose Y hY_mem hY_iso using hX
  obtain ⟨i, j, hij, hsim⟩ := h𝒜 Y hY_mem
  have hsim₁ : IsGraftSimulatedIn (X i) (Y i) :=
    isGraftSimulatedIn_of_isGraftIso (hY_iso i).symm
  have hsim₂ : IsGraftSimulatedIn (Y j) (X j) :=
    isGraftSimulatedIn_of_isGraftIso (hY_iso j)
  exact ⟨i, j, hij, (hsim₁.trans hsim).trans hsim₂⟩

/-! ## Mapping a graft along an equivalence on $\alpha$ -/

/-- The graft obtained by mapping the vertices of `A` along a bijection `f : α ≃ α`. -/
def Graft.mapEquiv {α : Type u} {β : Type v} (A : Graft α β) (f : α ≃ α) : Graft α β where
  G := A.G.map f
  T := f '' A.T
  T_subset := image_mono A.T_subset
  finite_G := ⟨A.finite_G.1.image f, A.finite_G.2⟩

@[simp]
theorem graft_mapEquiv_vertexSet {α : Type u} {β : Type v} (A : Graft α β) (f : α ≃ α) :
    V((A.mapEquiv f).G) = f '' V(A.G) :=
  rfl

@[simp]
theorem graft_mapEquiv_edgeSet {α : Type u} {β : Type v} (A : Graft α β) (f : α ≃ α) :
    E((A.mapEquiv f).G) = E(A.G) := by
  simp [Graft.mapEquiv]

theorem isGraftIso_mapEquiv {α : Type u} {β : Type v} (A : Graft α β) (f : α ≃ α) :
    IsGraftIso A (A.mapEquiv f) := by
  refine ⟨{
    vertexEquiv := {
      toFun := fun u => ⟨f u.1, mem_image_of_mem f u.2⟩
      invFun := fun v => ⟨f.symm v.1, by
        obtain ⟨u, hu, huv⟩ := v.2
        simpa [← huv] using hu⟩
      left_inv := fun u => Subtype.ext (f.symm_apply_apply u.1)
      right_inv := fun v => Subtype.ext (f.apply_symm_apply v.1) }
    edgeEquiv := {
      toFun := fun e => ⟨e.1, by simp [e.2]⟩
      invFun := fun e => ⟨e.1, by simpa using e.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    isLink_iff := fun e x y => by
      simp only [Graft.mapEquiv, map_isLink]
      constructor
      · intro hl
        exact ⟨x.1, y.1, hl, rfl, rfl⟩
      · rintro ⟨x₀, y₀, hl₀, hx₀, hy₀⟩
        have hx := f.injective hx₀
        have hy := f.injective hy₀
        subst hx hy
        exact hl₀ }, fun u => ?_⟩
  simp only [Graft.mapEquiv, mem_image]
  constructor
  · intro hu
    exact ⟨u.1, hu, rfl⟩
  · rintro ⟨w, hw, hwu⟩
    exact f.injective hwu ▸ hw

/-! ## Disjoint union of two edge-disjoint graphs and `WiGraftClass` properties -/

/-- Given two edge-disjoint graphs $G_1$ and $G_2$, their union on $V(G_1) \cup V(G_2)$ with links
given by $G_1.\text{IsLink} \lor G_2.\text{IsLink}$. -/
def edgeDisjointGraphUnion {α : Type u} {β : Type v}
    (G₁ G₂ : Graph α β) (hdisj : Disjoint E(G₁) E(G₂)) : Graph α β where
  vertexSet := V(G₁) ∪ V(G₂)
  IsLink e x y := G₁.IsLink e x y ∨ G₂.IsLink e x y
  isLink_symm _ _ := ⟨fun _ _ h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := by
    rcases h with h1 | h2 <;> rcases h' with h1' | h2'
    · exact G₁.eq_or_eq_of_isLink_of_isLink h1 h1'
    · exact False.elim (hdisj.notMem_of_mem_left h1.edge_mem h2'.edge_mem)
    · exact False.elim (hdisj.notMem_of_mem_left h1'.edge_mem h2.edge_mem)
    · exact G₂.eq_or_eq_of_isLink_of_isLink h2 h2'
  left_mem_of_isLink _ _ _ h :=
    h.elim (fun h1 => Or.inl h1.left_mem) (fun h2 => Or.inr h2.left_mem)

@[simp]
theorem edgeDisjointGraphUnion_vertexSet {α : Type u} {β : Type v}
    (G₁ G₂ : Graph α β) (hdisj : Disjoint E(G₁) E(G₂)) :
    V(edgeDisjointGraphUnion G₁ G₂ hdisj) = V(G₁) ∪ V(G₂) :=
  rfl

@[simp]
theorem edgeDisjointGraphUnion_isLink {α : Type u} {β : Type v}
    (G₁ G₂ : Graph α β) (hdisj : Disjoint E(G₁) E(G₂)) (e : β) (x y : α) :
    (edgeDisjointGraphUnion G₁ G₂ hdisj).IsLink e x y ↔ G₁.IsLink e x y ∨ G₂.IsLink e x y :=
  Iff.rfl

theorem le_edgeDisjointGraphUnion_left {α : Type u} {β : Type v}
    (G₁ G₂ : Graph α β) (hdisj : Disjoint E(G₁) E(G₂)) :
    G₁ ≤ edgeDisjointGraphUnion G₁ G₂ hdisj :=
  ⟨subset_union_left, fun _ _ _ hl => Or.inl hl⟩

theorem le_edgeDisjointGraphUnion_right {α : Type u} {β : Type v}
    (G₁ G₂ : Graph α β) (hdisj : Disjoint E(G₁) E(G₂)) :
    G₂ ≤ edgeDisjointGraphUnion G₁ G₂ hdisj :=
  ⟨subset_union_right, fun _ _ _ hl => Or.inr hl⟩

@[simp]
theorem edgeDisjointGraphUnion_edgeSet {α : Type u} {β : Type v}
    (G₁ G₂ : Graph α β) (hdisj : Disjoint E(G₁) E(G₂)) :
    E(edgeDisjointGraphUnion G₁ G₂ hdisj) = E(G₁) ∪ E(G₂) := by
  ext e
  constructor
  · intro he
    obtain ⟨x, y, hl₁ | hl₂⟩ := exists_isLink_of_mem_edgeSet he
    · exact Or.inl hl₁.edge_mem
    · exact Or.inr hl₂.edge_mem
  · rintro (he₁ | he₂)
    · obtain ⟨x, y, hl₁⟩ := exists_isLink_of_mem_edgeSet he₁
      exact (hl₁.mono (le_edgeDisjointGraphUnion_left G₁ G₂ hdisj)).edge_mem
    · obtain ⟨x, y, hl₂⟩ := exists_isLink_of_mem_edgeSet he₂
      exact (hl₂.mono (le_edgeDisjointGraphUnion_right G₁ G₂ hdisj)).edge_mem

/-- Given two vertex-disjoint and edge-disjoint grafts $A$ and $B$, their direct sum graft
$A \oplus B$. -/
def mkGraftDirectSum {α : Type u} {β : Type v}
    (A B : Graft α β) (hE : Disjoint E(A.G) E(B.G)) : Graft α β where
  G := edgeDisjointGraphUnion A.G B.G hE
  T := A.T ∪ B.T
  T_subset := union_subset_union A.T_subset B.T_subset
  finite_G := ⟨A.finite_G.1.union B.finite_G.1,
    by rw [edgeDisjointGraphUnion_edgeSet]; exact A.finite_G.2.union B.finite_G.2⟩

@[simp]
theorem mkGraftDirectSum_vertexSet {α : Type u} {β : Type v}
    (A B : Graft α β) (hE : Disjoint E(A.G) E(B.G)) :
    V((mkGraftDirectSum A B hE).G) = V(A.G) ∪ V(B.G) :=
  rfl

@[simp]
theorem mkGraftDirectSum_edgeSet {α : Type u} {β : Type v}
    (A B : Graft α β) (hE : Disjoint E(A.G) E(B.G)) :
    E((mkGraftDirectSum A B hE).G) = E(A.G) ∪ E(B.G) :=
  edgeDisjointGraphUnion_edgeSet A.G B.G hE

theorem isGraftDirectSum_mkGraftDirectSum {α : Type u} {β : Type v}
    (A B : Graft α β) (hV : Disjoint V(A.G) V(B.G)) (hE : Disjoint E(A.G) E(B.G)) :
    IsGraftDirectSum (mkGraftDirectSum A B hE) A B := by
  refine ⟨V(A.G), subset_union_left, ?_, ?_, ?_, ?_, ?_⟩
  · intro e x y hl
    rcases hl with hlA | hlB
    · exact iff_of_true hlA.left_mem hlA.right_mem
    · exact iff_of_false (hV.notMem_of_mem_right hlB.left_mem)
        (hV.notMem_of_mem_right hlB.right_mem)
  · ext e x y
    · simp [mkGraftDirectSum]
    · simp only [induce_isLink, mkGraftDirectSum, edgeDisjointGraphUnion_isLink]
      constructor
      · intro hlA
        exact ⟨Or.inl hlA, hlA.left_mem, hlA.right_mem⟩
      · rintro ⟨hlA | hlB, hxA, _⟩
        · exact hlA
        · exact False.elim (hV.notMem_of_mem_left hxA hlB.left_mem)
  · have hdiff : (V(A.G) ∪ V(B.G)) \ V(A.G) = V(B.G) :=
      union_sdiff_cancel_left hV.inter_eq.subset
    ext e x y
    · simp [mkGraftDirectSum, hdiff]
    · simp only [induce_isLink, mkGraftDirectSum, edgeDisjointGraphUnion_vertexSet, hdiff,
        edgeDisjointGraphUnion_isLink]
      constructor
      · intro hlB
        exact ⟨Or.inr hlB, hlB.left_mem, hlB.right_mem⟩
      · rintro ⟨hlA | hlB, hxB, _⟩
        · exact False.elim (hV.notMem_of_mem_left hlA.left_mem hxB)
        · exact hlB
  · ext x
    simp only [mkGraftDirectSum, mem_inter_iff, mem_union]
    constructor
    · intro hxA
      exact ⟨Or.inl hxA, A.T_subset hxA⟩
    · rintro ⟨hxA | hxB, hxVA⟩
      · exact hxA
      · exact False.elim (hV.notMem_of_mem_left hxVA (B.T_subset hxB))
  · ext x
    simp only [mkGraftDirectSum, mem_sdiff, mem_union]
    constructor
    · intro hxB
      exact ⟨Or.inr hxB, hV.notMem_of_mem_right (B.T_subset hxB)⟩
    · rintro ⟨hxA | hxB, hnotA⟩
      · exact False.elim (hnotA (A.T_subset hxA))
      · exact hxB

/-- If `f` fixes every vertex of `G`, then `G.map f = G`. -/
theorem map_eq_self_of_forall_mem {α : Type u} {β : Type v} {G : Graph α β} {f : α → α}
    (hf : ∀ x ∈ V(G), f x = x) : G.map f = G := by
  ext e x y
  · simp only [vertexSet_map, mem_image]
    constructor
    · rintro ⟨x₀, hx₀, rfl⟩
      rwa [hf x₀ hx₀]
    · intro hx
      exact ⟨e, hx, hf e hx⟩
  · simp only [map_isLink, Relation.Map]
    constructor
    · rintro ⟨x₀, y₀, hl₀, rfl, rfl⟩
      rwa [hf x₀ hl₀.left_mem, hf y₀ hl₀.right_mem]
    · intro hl
      exact ⟨x, y, hl, hf x hl.left_mem, hf y hl.right_mem⟩

/-! ## Two-piece graft gluings and vertex splitting -/

/-- A graft $X$ is a *two-piece gluing* of $A$ and $B$ along $V(A.G) \cap V(B.G)$ if $A.G$ and $B.G$
are edge-disjoint subgraphs of $X.G$ with union $X.G$, their shared vertices lie in $A.T \cap B.T$,
$X.T \subseteq A.T \cup B.T$, and $(A.T \cup B.T) \setminus (V(A.G) \cap V(B.G)) \subseteq X.T$. -/
structure IsTwoPieceGluing {α : Type u} {β : Type v} (X A B : Graft α β) : Prop where
  le_A : A.G ≤ X.G
  le_B : B.G ≤ X.G
  vertexSet_union : V(A.G) ∪ V(B.G) = V(X.G)
  edgeSet_union : E(A.G) ∪ E(B.G) = E(X.G)
  edge_disjoint : Disjoint E(A.G) E(B.G)
  inter_sub_TA : V(A.G) ∩ V(B.G) ⊆ A.T
  inter_sub_TB : V(A.G) ∩ V(B.G) ⊆ B.T
  T_sub_union : X.T ⊆ A.T ∪ B.T
  union_diff_sub_T : (A.T ∪ B.T) \ (V(A.G) ∩ V(B.G)) ⊆ X.T

/-- `ObtainedByVertexIdChain m X₁ X₂` means $X_2$ is obtained from $X_1$ by $m$ vertex
identifications of the form `identifyVerticesFun t₁ t₂ t₂` (where $t_1, t_2 \in T$ are identified
into $t = t_2$). -/
inductive ObtainedByVertexIdChain {α : Type u} {β : Type v} :
    ℕ → Graft α β → Graft α β → Prop
  | zero (X : Graft α β) : ObtainedByVertexIdChain 0 X X
  | step {m : ℕ} {X₁ X₂ X₃ : Graft α β}
      (hchain : ObtainedByVertexIdChain m X₁ X₂)
      (t₁ t₂ : α) (ht₁ : t₁ ∈ X₂.T) (ht₂ : t₂ ∈ X₂.T) (hne : t₁ ≠ t₂)
      (hG : X₃.G = X₂.G.map (identifyVerticesFun t₁ t₂ t₂))
      (hT : X₃.T = X₂.T \ {t₁, t₂} ∨ X₃.T = (X₂.T \ {t₁, t₂}) ∪ {t₂}) :
      ObtainedByVertexIdChain (m + 1) X₁ X₃

theorem ObtainedByVertexIdChain.trans {α : Type u} {β : Type v}
    {m₁ m₂ : ℕ} {X₁ X₂ X₃ : Graft α β}
    (h₁ : ObtainedByVertexIdChain m₁ X₁ X₂)
    (h₂ : ObtainedByVertexIdChain m₂ X₂ X₃) :
    ObtainedByVertexIdChain (m₁ + m₂) X₁ X₃ := by
  induction h₂ with
  | zero _ => simpa using h₁
  | step _ t₁ t₂ ht₁ ht₂ hne hG hT ih =>
    rw [← Nat.add_assoc]
    exact ObtainedByVertexIdChain.step (ih h₁) t₁ t₂ ht₁ ht₂ hne hG hT

theorem mem_WiGraftClass_of_obtainedByVertexIdChain {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {m : ℕ} {X₁ X₂ : Graft α β}
    (hX₁ : X₁ ∈ 𝒜) (hchain : ObtainedByVertexIdChain m X₁ X₂) :
    X₂ ∈ WiGraftClass m 𝒜 := by
  induction hchain with
  | zero _ => exact hX₁
  | step _ t₁ t₂ ht₁ ht₂ hne hG hT ih =>
    exact ⟨_, ih hX₁, t₁, ht₁, t₂, ht₂, hne, t₂, fun h => h.2 (Or.inr rfl), hG, hT⟩

theorem mem_WGraftClass_of_obtainedByVertexIdChain {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {m : ℕ} {X₁ X₂ : Graft α β}
    (hX₁ : X₁ ∈ 𝒜) (hchain : ObtainedByVertexIdChain m X₁ X₂) :
    X₂ ∈ WGraftClass 𝒜 :=
  mem_iUnion.mpr ⟨m, mem_WiGraftClass_of_obtainedByVertexIdChain hX₁ hchain⟩

theorem obtainedByVertexIdChain_mkGraftDirectSum_right {α : Type u} {β : Type v}
    {C Y₁ Y₂ : Graft α β} {m : ℕ}
    (hchain : ObtainedByVertexIdChain m Y₁ Y₂)
    (hV₁ : Disjoint V(C.G) V(Y₁.G))
    (hE₁ : Disjoint E(C.G) E(Y₁.G)) :
    ∃ (_hV₂ : Disjoint V(C.G) V(Y₂.G)) (hE₂ : Disjoint E(C.G) E(Y₂.G)),
      ObtainedByVertexIdChain m
        (mkGraftDirectSum C Y₁ hE₁) (mkGraftDirectSum C Y₂ hE₂) := by
  induction hchain with
  | zero _ => exact ⟨hV₁, hE₁, ObtainedByVertexIdChain.zero _⟩
  | @step m Y₁ Y₂ Y₃ _ t₁ t₂ ht₁ ht₂ hne hG hT ih =>
    obtain ⟨hV₂, hE₂, hchain₂⟩ := ih hV₁ hE₁
    have ht₁_V : t₁ ∈ V(Y₂.G) := Y₂.T_subset ht₁
    have ht₂_V : t₂ ∈ V(Y₂.G) := Y₂.T_subset ht₂
    have hVY₃_sub : V(Y₃.G) ⊆ V(Y₂.G) := by
      rw [hG, vertexSet_map]
      rintro _ ⟨x, hx, rfl⟩
      by_cases h : x = t₁ ∨ x = t₂
      · rcases h with rfl | rfl <;> simp [identifyVerticesFun, ht₂_V]
      · rw [not_or] at h
        rw [identifyVerticesFun_of_ne h.1 h.2]
        exact hx
    have hEY₃_sub : E(Y₃.G) ⊆ E(Y₂.G) := by
      rw [hG]
      simp
    have hV₃ : Disjoint V(C.G) V(Y₃.G) := hV₂.mono_right hVY₃_sub
    have hE₃ : Disjoint E(C.G) E(Y₃.G) := hE₂.mono_right hEY₃_sub
    let g := identifyVerticesFun t₁ t₂ t₂
    have hgC : ∀ x ∈ V(C.G), g x = x := by
      intro x hx
      have hx₁ : x ≠ t₁ := fun h => hV₂.notMem_of_mem_left hx (h ▸ ht₁_V)
      have hx₂ : x ≠ t₂ := fun h => hV₂.notMem_of_mem_left hx (h ▸ ht₂_V)
      exact identifyVerticesFun_of_ne hx₁ hx₂
    have hG_eq : (mkGraftDirectSum C Y₃ hE₃).G = (mkGraftDirectSum C Y₂ hE₂).G.map g := by
      ext e x y
      · simp only [mkGraftDirectSum, edgeDisjointGraphUnion_vertexSet, hG, vertexSet_map,
          image_union]
        have himgC : g '' V(C.G) = V(C.G) := by
          ext z
          simp only [mem_image]
          exact ⟨by rintro ⟨w, hw, rfl⟩; rwa [hgC w hw], fun hz => ⟨z, hz, hgC z hz⟩⟩
        rw [himgC]
      · simp only [mkGraftDirectSum, edgeDisjointGraphUnion_isLink, map_isLink,
          Relation.Map, hG]
        constructor
        · rintro (hlC | ⟨x₀, y₀, hlY, rfl, rfl⟩)
          · exact ⟨x, y, Or.inl hlC, hgC x hlC.left_mem, hgC y hlC.right_mem⟩
          · exact ⟨x₀, y₀, Or.inr hlY, rfl, rfl⟩
        · rintro ⟨x₀, y₀, hlC | hlY, rfl, rfl⟩
          · have hx₀ : g x₀ = x₀ := hgC x₀ hlC.left_mem
            have hy₀ : g y₀ = y₀ := hgC y₀ hlC.right_mem
            change C.G.IsLink e (g x₀) (g y₀) ∨ _
            rw [hx₀, hy₀]
            exact Or.inl hlC
          · exact Or.inr ⟨x₀, y₀, hlY, rfl, rfl⟩
    have ht₁_notC : t₁ ∉ C.T := fun h => hV₂.notMem_of_mem_left (C.T_subset h) ht₁_V
    have ht₂_notC : t₂ ∉ C.T := fun h => hV₂.notMem_of_mem_left (C.T_subset h) ht₂_V
    have hC_diff : C.T \ {t₁, t₂} = C.T := by
      ext x
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun h => h.1,
        fun hx => ⟨hx, by rintro (rfl | rfl); exact ht₁_notC hx; exact ht₂_notC hx⟩⟩
    have hT_eq : (mkGraftDirectSum C Y₃ hE₃).T = (mkGraftDirectSum C Y₂ hE₂).T \ {t₁, t₂} ∨
        (mkGraftDirectSum C Y₃ hE₃).T = ((mkGraftDirectSum C Y₂ hE₂).T \ {t₁, t₂}) ∪ {t₂} := by
      rcases hT with hT₁ | hT₂
      · left
        simp only [mkGraftDirectSum, hT₁, union_sdiff_distrib, hC_diff]
      · right
        simp only [mkGraftDirectSum, hT₂, union_sdiff_distrib, hC_diff, union_assoc]
    exact ⟨hV₃, hE₃, ObtainedByVertexIdChain.step hchain₂ t₁ t₂
      (Or.inr ht₁) (Or.inr ht₂) hne hG_eq hT_eq⟩

/-- Base case of two-piece gluing: when $V(A.G)$ and $V(B.G)$ are disjoint, $X$ is literally
`mkGraftDirectSum A B h.edge_disjoint`. -/
theorem eq_mkGraftDirectSum_of_isTwoPieceGluing_disjoint {α : Type u} {β : Type v}
    {X A B : Graft α β} (h : IsTwoPieceGluing X A B) (hV : Disjoint V(A.G) V(B.G)) :
    X = mkGraftDirectSum A B h.edge_disjoint := by
  have hG : X.G = edgeDisjointGraphUnion A.G B.G h.edge_disjoint := by
    ext e x y
    · exact Set.ext_iff.mp h.vertexSet_union.symm e
    · simp only [edgeDisjointGraphUnion_isLink]
      constructor
      · intro hlX
        have he : e ∈ E(X.G) := hlX.edge_mem
        rw [← h.edgeSet_union] at he
        rcases he with heA | heB
        · exact Or.inl ((h.le_A.isLink_iff heA).mpr hlX)
        · exact Or.inr ((h.le_B.isLink_iff heB).mpr hlX)
      · rintro (hlA | hlB)
        · exact hlA.mono h.le_A
        · exact hlB.mono h.le_B
  have hT : X.T = A.T ∪ B.T := by
    apply Subset.antisymm h.T_sub_union
    have hdiff := h.union_diff_sub_T
    rwa [hV.inter_eq, sdiff_empty] at hdiff
  cases X
  dsimp [mkGraftDirectSum] at hG hT ⊢
  congr

/-- Single-vertex splitting step for `IsTwoPieceGluing`: if $y \in V(A.G) \cap V(B.G)$ and
$y' \notin V(X.G)$, swapping $y$ and $y'$ in $A$ produces an isomorphic graft $A'$ and a glued
graft $X'$ with $V(A'.G) \cap V(B.G) = (V(A.G) \cap V(B.G)) \setminus \{y\}$ such that $X$ is
obtained from $X'$ by identifying $y'$ and $y$ into $y$. -/
theorem isTwoPieceGluing_split_step {α : Type u} {β : Type v} [DecidableEq α]
    {X A B : Graft α β} (h : IsTwoPieceGluing X A B)
    {y y' : α} (hy : y ∈ V(A.G) ∩ V(B.G)) (hy' : y' ∉ V(X.G)) :
    let f := Equiv.swap y y'
    let A' := A.mapEquiv f
    let hE' : Disjoint E(A'.G) E(B.G) := by
      rw [graft_mapEquiv_edgeSet]; exact h.edge_disjoint
    let X' : Graft α β := {
      G := edgeDisjointGraphUnion A'.G B.G hE'
      T := X.T ∪ {y', y}
      T_subset := by
        rw [edgeDisjointGraphUnion_vertexSet]
        have hyA : y ∈ V(A.G) := hy.1
        have hyB : y ∈ V(B.G) := hy.2
        have hy'_A' : y' ∈ V(A'.G) := by
          simp only [A', graft_mapEquiv_vertexSet, mem_image]
          exact ⟨y, hyA, Equiv.swap_apply_left y y'⟩
        intro z hz
        rcases hz with hzX | hzy
        · have hz_union : z ∈ V(A.G) ∪ V(B.G) := by
            rw [h.vertexSet_union]; exact X.T_subset hzX
          rcases hz_union with hzA | hzB
          · by_cases hzy : z = y
            · subst hzy; exact Or.inr hyB
            · have hzy' : z ≠ y' := fun h => hy' (h ▸ X.T_subset hzX)
              left
              simp only [A', graft_mapEquiv_vertexSet, mem_image]
              exact ⟨z, hzA, Equiv.swap_apply_of_ne_of_ne hzy hzy'⟩
          · exact Or.inr hzB
        · simp only [mem_insert_iff, mem_singleton_iff] at hzy
          rcases hzy with rfl | rfl
          · exact Or.inl hy'_A'
          · exact Or.inr hyB
      finite_G := ⟨(A'.finite_G.1).union B.finite_G.1,
        by rw [edgeDisjointGraphUnion_edgeSet]; exact (A'.finite_G.2).union B.finite_G.2⟩ }
    IsGraftIso A A' ∧
    V(A'.G) = (V(A.G) \ {y}) ∪ {y'} ∧
    V(A'.G) ∩ V(B.G) = (V(A.G) ∩ V(B.G)) \ {y} ∧
    IsTwoPieceGluing X' A' B ∧
    ObtainedByVertexIdChain 1 X' X := by
  dsimp only
  let f := Equiv.swap y y'
  let A' := A.mapEquiv f
  have hE' : Disjoint E(A'.G) E(B.G) := by
    rw [graft_mapEquiv_edgeSet]; exact h.edge_disjoint
  have hyA : y ∈ V(A.G) := hy.1
  have hyB : y ∈ V(B.G) := hy.2
  have hy'_notA : y' ∉ V(A.G) := fun hA => hy' (h.le_A.vertexSet_mono hA)
  have hy'_notB : y' ∉ V(B.G) := fun hB => hy' (h.le_B.vertexSet_mono hB)
  have hy_ne_y' : y ≠ y' := fun heq => hy'_notA (heq ▸ hyA)
  have hVA' : V(A'.G) = (V(A.G) \ {y}) ∪ {y'} := by
    ext z
    simp only [A', graft_mapEquiv_vertexSet, mem_image, mem_union, mem_sdiff,
      mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hwy : w = y
      · subst hwy
        simp [f, Equiv.swap_apply_left]
      · have hwy' : w ≠ y' := fun heq => hy'_notA (heq ▸ hw)
        rw [show f w = w from Equiv.swap_apply_of_ne_of_ne hwy hwy']
        exact Or.inl ⟨hw, hwy⟩
    · rintro (⟨hzA, hzy⟩ | hz_eq)
      · have hzy' : z ≠ y' := fun heq => hy'_notA (heq ▸ hzA)
        exact ⟨z, hzA, Equiv.swap_apply_of_ne_of_ne hzy hzy'⟩
      · exact ⟨y, hyA, (Equiv.swap_apply_left y y').trans hz_eq.symm⟩
  have hTA' : A'.T = (A.T \ {y}) ∪ {y'} := by
    have hyTA : y ∈ A.T := h.inter_sub_TA hy
    ext z
    simp only [A', Graft.mapEquiv, mem_image, mem_union, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hwy : w = y
      · subst hwy
        simp [f, Equiv.swap_apply_left]
      · have hwy' : w ≠ y' := fun heq => hy'_notA (heq ▸ A.T_subset hw)
        rw [show f w = w from Equiv.swap_apply_of_ne_of_ne hwy hwy']
        exact Or.inl ⟨hw, hwy⟩
    · rintro (⟨hzT, hzy⟩ | hz_eq)
      · have hzy' : z ≠ y' := fun heq => hy'_notA (heq ▸ A.T_subset hzT)
        exact ⟨z, hzT, Equiv.swap_apply_of_ne_of_ne hzy hzy'⟩
      · exact ⟨y, hyTA, (Equiv.swap_apply_left y y').trans hz_eq.symm⟩
  have hinter' : V(A'.G) ∩ V(B.G) = (V(A.G) ∩ V(B.G)) \ {y} := by
    rw [hVA']
    ext z
    simp only [mem_inter_iff, mem_union, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hzA, hzy⟩ | hz_eq, hzB⟩
      · exact ⟨⟨hzA, hzB⟩, hzy⟩
      · exact False.elim (hy'_notB (hz_eq ▸ hzB))
    · rintro ⟨⟨hzA, hzB⟩, hzy⟩
      exact ⟨Or.inl ⟨hzA, hzy⟩, hzB⟩
  refine ⟨isGraftIso_mapEquiv A f, hVA', hinter', ?_, ?_⟩
  · refine {
      le_A := le_edgeDisjointGraphUnion_left A'.G B.G hE'
      le_B := le_edgeDisjointGraphUnion_right A'.G B.G hE'
      vertexSet_union := rfl
      edgeSet_union := (edgeDisjointGraphUnion_edgeSet A'.G B.G hE').symm
      edge_disjoint := hE'
      inter_sub_TA := by
        rw [hinter', hTA']
        intro z ⟨hz, hzy⟩
        exact Or.inl ⟨h.inter_sub_TA hz, hzy⟩
      inter_sub_TB := by
        rw [hinter']
        exact sdiff_subset.trans h.inter_sub_TB
      T_sub_union := by
        rw [hTA']
        intro z hz
        simp only [mem_union, mem_insert_iff, mem_singleton_iff, mem_sdiff] at hz ⊢
        rcases hz with hzX | rfl | rfl
        · by_cases hzy : z = y
          · subst hzy
            exact Or.inr (h.inter_sub_TB hy)
          · rcases h.T_sub_union hzX with hzA | hzB
            · exact Or.inl (Or.inl ⟨hzA, hzy⟩)
            · exact Or.inr hzB
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr (h.inter_sub_TB hy)
      union_diff_sub_T := by
        rw [hinter', hTA']
        intro z ⟨hz_union, hz_not_inter⟩
        simp only [mem_union, mem_insert_iff, mem_singleton_iff]
        by_cases hzy' : z = y'
        · exact Or.inr (Or.inl hzy')
        · by_cases hzy : z = y
          · exact Or.inr (Or.inr hzy)
          · left
            apply h.union_diff_sub_T
            refine ⟨?_, fun hz_inter => hz_not_inter ⟨hz_inter, hzy⟩⟩
            rcases hz_union with (⟨hzA, _⟩ | rfl) | hzB
            · exact Or.inl hzA
            · exact False.elim (hzy' rfl)
            · exact Or.inr hzB }
  · let g := identifyVerticesFun y' y y
    have hgf_A : ∀ w ∈ V(A.G), g (f w) = w := by
      intro w hw
      by_cases hwy : w = y
      · subst hwy
        simp [f, g, Equiv.swap_apply_left]
      · have hwy' : w ≠ y' := fun heq => hy'_notA (heq ▸ hw)
        rw [show f w = w from Equiv.swap_apply_of_ne_of_ne hwy hwy']
        exact identifyVerticesFun_of_ne hwy' hwy
    have hg_B : ∀ w ∈ V(B.G), g w = w := by
      intro w hw
      by_cases hwy : w = y
      · subst hwy
        simp [g]
      · have hwy' : w ≠ y' := fun heq => hy'_notB (heq ▸ hw)
        exact identifyVerticesFun_of_ne hwy' hwy
    have hG_map : X.G = (edgeDisjointGraphUnion A'.G B.G hE').map g := by
      ext e u v
      · simp only [vertexSet_map, edgeDisjointGraphUnion_vertexSet, image_union, A',
          graft_mapEquiv_vertexSet]
        rw [← image_comp]
        have himgA : (g ∘ f) '' V(A.G) = V(A.G) := by
          ext z
          simp only [mem_image, comp_apply]
          exact ⟨by rintro ⟨w, hw, rfl⟩; rwa [hgf_A w hw], fun hz => ⟨z, hz, hgf_A z hz⟩⟩
        have himgB : g '' V(B.G) = V(B.G) := by
          ext z
          simp only [mem_image]
          exact ⟨by rintro ⟨w, hw, rfl⟩; rwa [hg_B w hw], fun hz => ⟨z, hz, hg_B z hz⟩⟩
        rw [himgA, himgB, h.vertexSet_union]
      · simp only [map_isLink, Relation.Map, edgeDisjointGraphUnion_isLink, A', Graft.mapEquiv]
        constructor
        · intro hlX
          have he : e ∈ E(X.G) := hlX.edge_mem
          rw [← h.edgeSet_union] at he
          rcases he with heA | heB
          · have hlA := (h.le_A.isLink_iff heA).mpr hlX
            exact ⟨f u, f v, Or.inl ⟨u, v, hlA, rfl, rfl⟩,
              hgf_A u hlA.left_mem, hgf_A v hlA.right_mem⟩
          · have hlB := (h.le_B.isLink_iff heB).mpr hlX
            exact ⟨u, v, Or.inr hlB, hg_B u hlB.left_mem, hg_B v hlB.right_mem⟩
        · rintro ⟨x₀, y₀, ⟨u₀, v₀, hlA, rfl, rfl⟩ | hlB, rfl, rfl⟩
          · rw [hgf_A u₀ hlA.left_mem, hgf_A v₀ hlA.right_mem]
            exact hlA.mono h.le_A
          · rw [hg_B x₀ hlB.left_mem, hg_B y₀ hlB.right_mem]
            exact hlB.mono h.le_B
    have hy'_notT : y' ∉ X.T := fun hT => hy' (X.T_subset hT)
    have hT_opt : X.T = (X.T ∪ {y', y}) \ {y', y} ∨
        X.T = ((X.T ∪ {y', y}) \ {y', y}) ∪ {y} := by
      by_cases hyT : y ∈ X.T
      · right
        ext z
        simp only [mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff]
        constructor
        · intro hz
          by_cases hzy : z = y
          · exact Or.inr hzy
          · exact Or.inl ⟨Or.inl hz, not_or.mpr ⟨fun h => hy'_notT (h ▸ hz), hzy⟩⟩
        · rintro (⟨hz | rfl | rfl, hnot⟩ | rfl)
          · exact hz
          · exact False.elim (hnot (Or.inl rfl))
          · exact False.elim (hnot (Or.inr rfl))
          · exact hyT
      · left
        ext z
        simp only [mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
        constructor
        · intro hz
          exact ⟨Or.inl hz, not_or.mpr ⟨fun h => hy'_notT (h ▸ hz), fun h => hyT (h ▸ hz)⟩⟩
        · rintro ⟨hz | rfl | rfl, hnot⟩
          · exact hz
          · exact False.elim (hnot (Or.inl rfl))
          · exact False.elim (hnot (Or.inr rfl))
    exact ObtainedByVertexIdChain.step (ObtainedByVertexIdChain.zero _)
      y' y (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hy_ne_y'.symm hG_map hT_opt

/-- By induction on $|V(A.G) \cap V(B.G)|$, any two-piece gluing $X$ of $A$ and $B$ (both vertex-
disjoint from a finite set $S$) is obtained by a chain of vertex identifications from a direct sum
$A' \oplus B$ where $A'$ is isomorphic to $A$ and vertex-disjoint from $S$. -/
theorem exists_iso_and_vertexIdChain_of_isTwoPieceGluing {α : Type u} {β : Type v}
    [Infinite α] {S : Set α} (hS : S.Finite) :
    ∀ (n : ℕ) {X A B : Graft α β} (_h : IsTwoPieceGluing X A B)
      (_hcard : (V(A.G) ∩ V(B.G)).ncard = n)
      (_hAS : Disjoint V(A.G) S) (_hBS : Disjoint V(B.G) S),
      ∃ (A' : Graft α β) (_hV : Disjoint V(A'.G) V(B.G)) (hE : Disjoint E(A'.G) E(B.G)) (m : ℕ),
        IsGraftIso A A' ∧
        E(A'.G) = E(A.G) ∧
        Disjoint V(A'.G) S ∧
        ObtainedByVertexIdChain m (mkGraftDirectSum A' B hE) X
  | 0, X, A, B, h, hcard, hAS, _ => by
    have hinter_fin : (V(A.G) ∩ V(B.G)).Finite := A.finite_G.1.subset inter_subset_left
    have hinter_empty : V(A.G) ∩ V(B.G) = ∅ :=
      (ncard_eq_zero hinter_fin).mp hcard
    have hV : Disjoint V(A.G) V(B.G) := disjoint_iff_inter_eq_empty.mpr hinter_empty
    have hX_eq := eq_mkGraftDirectSum_of_isTwoPieceGluing_disjoint h hV
    refine ⟨A, hV, h.edge_disjoint, 0, IsGraftIso.refl A, rfl, hAS, ?_⟩
    rw [← hX_eq]
    exact ObtainedByVertexIdChain.zero _
  | n + 1, X, A, B, h, hcard, hAS, hBS => by
    classical
    have hinter_fin : (V(A.G) ∩ V(B.G)).Finite := A.finite_G.1.subset inter_subset_left
    have hinter_nonempty : (V(A.G) ∩ V(B.G)).Nonempty := by
      rw [← ncard_pos hinter_fin]
      omega
    obtain ⟨y, hy⟩ := hinter_nonempty
    obtain ⟨y', hy'_not⟩ := (X.finite_G.1.union hS).exists_notMem
    have hy'_notX : y' ∉ V(X.G) := fun hX => hy'_not (Or.inl hX)
    have hy'_notS : y' ∉ S := fun hS' => hy'_not (Or.inr hS')
    obtain ⟨hiso₁, hVA₁, hinter₁, hgluing₁, hchain₁⟩ :=
      isTwoPieceGluing_split_step h hy hy'_notX
    have hcard₁ : (V((A.mapEquiv (Equiv.swap y y')).G) ∩ V(B.G)).ncard = n := by
      rw [hinter₁, ncard_sdiff_singleton_of_mem hy, hcard]
      rfl
    have hA₁S : Disjoint V((A.mapEquiv (Equiv.swap y y')).G) S := by
      rw [hVA₁, disjoint_union_left]
      refine ⟨hAS.mono_left sdiff_subset, ?_⟩
      rwa [disjoint_singleton_left]
    obtain ⟨A', hV', hE', m, hiso₂, hEA', hA'S, hchain₂⟩ :=
      exists_iso_and_vertexIdChain_of_isTwoPieceGluing hS n hgluing₁ hcard₁ hA₁S hBS
    rw [graft_mapEquiv_edgeSet] at hEA'
    exact ⟨A', hV', hE', m + 1, hiso₁.trans hiso₂, hEA', hA'S, hchain₂.trans hchain₁⟩

/-- Corollary of `exists_iso_and_vertexIdChain_of_isTwoPieceGluing` for two pieces: if
`IsTwoPieceGluing X A B` with $A \in \mathscr{A}$ and $B \in \mathscr{B}$, then
$X \in W(\mathscr{A}^* \oplus \mathscr{B}^*)$. -/
theorem mem_WGraftClass_of_isTwoPieceGluing {α : Type u} {β : Type v} [Infinite α]
    {𝒜 ℬ : Set (Graft α β)} {X A B : Graft α β}
    (h : IsTwoPieceGluing X A B) (hA : A ∈ 𝒜) (hB : B ∈ ℬ) :
    X ∈ WGraftClass (graftDirectSumClass (isoGraftClass 𝒜) (isoGraftClass ℬ)) := by
  obtain ⟨A', hV, hE, m, hisoA, _, _, hchain⟩ :=
    exists_iso_and_vertexIdChain_of_isTwoPieceGluing finite_empty
      (V(A.G) ∩ V(B.G)).ncard h rfl (disjoint_empty _) (disjoint_empty _)
  have hsum : mkGraftDirectSum A' B hE ∈
      graftDirectSumClass (isoGraftClass 𝒜) (isoGraftClass ℬ) :=
    ⟨A', ⟨A, hA, hisoA⟩, B, subset_isoGraftClass ℬ hB,
      isGraftDirectSum_mkGraftDirectSum A' B hV hE⟩
  exact mem_WGraftClass_of_obtainedByVertexIdChain hsum hchain

/-- Corollary of `exists_iso_and_vertexIdChain_of_isTwoPieceGluing` for three pieces: if
`IsTwoPieceGluing X A M₂` and `IsTwoPieceGluing M₂ M B` with $A \in \mathscr{A}$,
$M \in \mathscr{B}$, and $B \in \mathscr{A}$, then
$X \in W(\mathscr{A}^* \oplus (\mathscr{B}^* \oplus \mathscr{A}^*))$. -/
theorem mem_WGraftClass_of_isThreePieceGluing {α : Type u} {β : Type v} [Infinite α]
    {𝒜 ℬ : Set (Graft α β)} {X A M₂ M B : Graft α β}
    (h₁ : IsTwoPieceGluing X A M₂) (h₂ : IsTwoPieceGluing M₂ M B)
    (hA : A ∈ 𝒜) (hM : M ∈ ℬ) (hB : B ∈ 𝒜) :
    X ∈ WGraftClass (graftDirectSumClass (isoGraftClass 𝒜)
      (graftDirectSumClass (isoGraftClass ℬ) (isoGraftClass 𝒜))) := by
  obtain ⟨A', hV₁, hE₁, m₁, hisoA, _, _, hchain₁⟩ :=
    exists_iso_and_vertexIdChain_of_isTwoPieceGluing finite_empty
      (V(A.G) ∩ V(M₂.G)).ncard h₁ rfl (disjoint_empty _) (disjoint_empty _)
  have hMS : Disjoint V(M.G) V(A'.G) :=
    hV₁.symm.mono_left h₂.le_A.vertexSet_mono
  have hBS : Disjoint V(B.G) V(A'.G) :=
    hV₁.symm.mono_left h₂.le_B.vertexSet_mono
  obtain ⟨M', hV₂, hE₂, m₂, hisoM, hEM', hM'A', hchain₂⟩ :=
    exists_iso_and_vertexIdChain_of_isTwoPieceGluing A'.finite_G.1
      (V(M.G) ∩ V(B.G)).ncard h₂ rfl hMS hBS
  let Y₀ := mkGraftDirectSum M' B hE₂
  have hVY₀ : Disjoint V(A'.G) V(Y₀.G) := by
    rw [mkGraftDirectSum_vertexSet, disjoint_union_right]
    exact ⟨hM'A'.symm, hBS.symm⟩
  have hEY₀ : Disjoint E(A'.G) E(Y₀.G) := by
    rw [mkGraftDirectSum_edgeSet, disjoint_union_right, hEM']
    exact ⟨hE₁.mono_right h₂.le_A.edgeSet_mono, hE₁.mono_right h₂.le_B.edgeSet_mono⟩
  obtain ⟨_, hE₁', hchain_lifted⟩ :=
    obtainedByVertexIdChain_mkGraftDirectSum_right hchain₂ hVY₀ hEY₀
  have hchain_total : ObtainedByVertexIdChain (m₂ + m₁) (mkGraftDirectSum A' Y₀ hEY₀) X :=
    hchain_lifted.trans hchain₁
  have hY₀_mem : Y₀ ∈ graftDirectSumClass (isoGraftClass ℬ) (isoGraftClass 𝒜) :=
    ⟨M', ⟨M, hM, hisoM⟩, B, subset_isoGraftClass 𝒜 hB,
      isGraftDirectSum_mkGraftDirectSum M' B hV₂ hE₂⟩
  have hX₀_mem : mkGraftDirectSum A' Y₀ hEY₀ ∈
      graftDirectSumClass (isoGraftClass 𝒜)
        (graftDirectSumClass (isoGraftClass ℬ) (isoGraftClass 𝒜)) :=
    ⟨A', ⟨A, hA, hisoA⟩, Y₀, hY₀_mem, isGraftDirectSum_mkGraftDirectSum A' Y₀ hVY₀ hEY₀⟩
  exact mem_WGraftClass_of_obtainedByVertexIdChain hX₀_mem hchain_total



/-! ## Interval subgraphs and subgrafts of a `GraftPathDecomposition` -/

/-- The union of vertex sets $\bigcup_{a \le i \le b} V(G_i)$ for an index interval $[a, b]$. -/
def GraftPathDecomposition.intervalVerts {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) : Set α :=
  ⋃ (i : Fin D.r) (_ : a ≤ i.1 ∧ i.1 ≤ b), V(D.G i)

/-- The union of edge sets $\bigcup_{a \le i \le b} E(G_i)$ for an index interval $[a, b]$. -/
def GraftPathDecomposition.intervalEdges {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) : Set β :=
  ⋃ (i : Fin D.r) (_ : a ≤ i.1 ∧ i.1 ≤ b), E(D.G i)

theorem GraftPathDecomposition.intervalVerts_subset {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) :
    D.intervalVerts a b ⊆ V(X.G) := by
  rintro v ⟨_, ⟨i, rfl⟩, ⟨_, ⟨_, rfl⟩, hv⟩⟩
  exact (D.le_G i).vertexSet_mono hv

theorem GraftPathDecomposition.intervalEdges_subset {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) :
    D.intervalEdges a b ⊆ E(X.G) := by
  rintro e ⟨_, ⟨i, rfl⟩, ⟨_, ⟨_, rfl⟩, he⟩⟩
  exact (D.le_G i).edgeSet_mono he

theorem GraftPathDecomposition.endpoints_mem_intervalVerts {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) :
    ∀ ⦃e x y⦄, e ∈ D.intervalEdges a b → X.G.IsLink e x y →
      x ∈ D.intervalVerts a b ∧ y ∈ D.intervalVerts a b := by
  rintro e x y ⟨_, ⟨i, rfl⟩, ⟨_, ⟨hab, rfl⟩, he⟩⟩ hl
  have hli : (D.G i).IsLink e x y := ((D.le_G i).isLink_iff he).mpr hl
  exact ⟨mem_iUnion₂.2 ⟨i, hab, hli.left_mem⟩, mem_iUnion₂.2 ⟨i, hab, hli.right_mem⟩⟩

theorem GraftPathDecomposition.inc_mem_intervalVerts {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) :
    ∀ ⦃e x⦄, e ∈ D.intervalEdges a b → X.G.Inc e x → x ∈ D.intervalVerts a b := by
  rintro e x he ⟨y, hl⟩
  exact (D.endpoints_mem_intervalVerts a b he hl).1

/-- The interval subgraph $G_{[a, b]}$ of $X.G$. -/
def GraftPathDecomposition.intervalGraph {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) :
    Graph α β :=
  subgraphOfVertsEdges X.G (D.intervalVerts a b) (D.intervalEdges a b)
    (D.intervalVerts_subset a b) (D.endpoints_mem_intervalVerts a b)

theorem GraftPathDecomposition.intervalGraph_le {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) :
    D.intervalGraph a b ≤ X.G :=
  subgraphOfVertsEdges_le X.G _ _ _ _

@[simp]
theorem GraftPathDecomposition.intervalGraph_vertexSet_eq {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) :
    V(D.intervalGraph a b) = D.intervalVerts a b :=
  rfl

@[simp]
theorem GraftPathDecomposition.intervalGraph_isLink {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ)
    (e : β) (x y : α) :
    (D.intervalGraph a b).IsLink e x y ↔ e ∈ D.intervalEdges a b ∧ X.G.IsLink e x y :=
  Iff.rfl

theorem GraftPathDecomposition.intervalGraph_edgeSet_eq {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (a b : ℕ) :
    E(D.intervalGraph a b) = D.intervalEdges a b := by
  ext e
  constructor
  · intro he
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
    exact (D.intervalGraph_isLink a b e x y).mp hl |>.1
  · intro he
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet (D.intervalEdges_subset a b he)
    exact ((D.intervalGraph_isLink a b e x y).mpr ⟨he, hl⟩).edge_mem

theorem GraftPathDecomposition.part_le_intervalGraph {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {a b : ℕ} (i : Fin D.r) (hab : a ≤ i.1 ∧ i.1 ≤ b) :
    D.G i ≤ D.intervalGraph a b := by
  refine ⟨fun v hv => mem_iUnion₂.2 ⟨i, hab, hv⟩, fun e x y hlink => ?_⟩
  rw [D.intervalGraph_isLink]
  exact ⟨mem_iUnion₂.2 ⟨i, hab, hlink.edge_mem⟩, hlink.mono (D.le_G i)⟩

theorem GraftPathDecomposition.intervalGraph_single {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (i : Fin D.r) :
    D.intervalGraph i.1 i.1 = D.G i := by
  ext v x y
  · rw [D.intervalGraph_vertexSet_eq]
    simp only [intervalVerts, mem_iUnion]
    constructor
    · rintro ⟨j, ⟨hij, hji⟩, hv⟩
      have hjeq : j = i := Fin.ext (by omega)
      rwa [hjeq] at hv
    · exact fun hv => ⟨i, ⟨le_refl _, le_refl _⟩, hv⟩
  · rw [D.intervalGraph_isLink]
    constructor
    · rintro ⟨⟨_, ⟨j, rfl⟩, ⟨_, ⟨⟨hij, hji⟩, rfl⟩, he⟩⟩, hlink⟩
      have hjeq : j = i := Fin.ext (by omega)
      subst hjeq
      exact ((D.le_G j).isLink_iff he).2 hlink
    · intro hlink
      exact ⟨mem_iUnion₂.2 ⟨i, ⟨le_refl _, le_refl _⟩, hlink.edge_mem⟩,
        hlink.mono (D.le_G i)⟩

theorem GraftPathDecomposition.intervalGraph_zero_last {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) :
    D.intervalGraph 0 (D.r - 1) = X.G := by
  ext v x y
  · rw [D.intervalGraph_vertexSet_eq]
    constructor
    · exact fun hv => D.intervalVerts_subset 0 (D.r - 1) hv
    · intro hv
      rw [← D.vertexSet_iUnion, mem_iUnion] at hv
      obtain ⟨i, hvi⟩ := hv
      exact mem_iUnion₂.2 ⟨i, ⟨Nat.zero_le _, Nat.le_sub_one_of_lt i.2⟩, hvi⟩
  · rw [D.intervalGraph_isLink]
    constructor
    · exact fun h => h.2
    · intro hlink
      obtain ⟨i, hei⟩ := D.exists_mem_edgeSet hlink.edge_mem
      exact ⟨mem_iUnion₂.2 ⟨i, ⟨Nat.zero_le _, Nat.le_sub_one_of_lt i.2⟩, hei⟩, hlink⟩

/-- For an index interval $[a, b]$ with $a \le b < D.r$, the interval graft $X_{[a, b]}$ has graph
$G_{[a, b]}$ and root set $Y_a \cup Y_{b+1}$. -/
def GraftPathDecomposition.intervalGraft {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    (a b : ℕ) (hab : a ≤ b) (hb : b < D.r) : Graft α β where
  G := D.intervalGraph a b
  T := D.Y ⟨a, by omega⟩ ∪ D.Y ⟨b + 1, by omega⟩
  T_subset := by
    rw [D.intervalGraph_vertexSet_eq]
    rintro v (hva | hvb)
    · have hvG : v ∈ V(D.G ⟨a, by omega⟩) :=
        D.Y_subset ⟨a, by omega⟩ (Or.inl hva)
      exact mem_iUnion₂.2 ⟨⟨a, by omega⟩, ⟨le_refl a, hab⟩, hvG⟩
    · have hvG : v ∈ V(D.G ⟨b, hb⟩) :=
        D.Y_subset ⟨b, hb⟩ (Or.inr hvb)
      exact mem_iUnion₂.2 ⟨⟨b, hb⟩, ⟨hab, le_refl b⟩, hvG⟩
  finite_G := ⟨X.finite_G.1.subset (D.intervalGraph_le a b).vertexSet_mono,
    X.finite_G.2.subset (D.intervalGraph_le a b).edgeSet_mono⟩

@[simp]
theorem GraftPathDecomposition.intervalGraft_G {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    (a b : ℕ) (hab : a ≤ b) (hb : b < D.r) :
    (D.intervalGraft a b hab hb).G = D.intervalGraph a b :=
  rfl

@[simp]
theorem GraftPathDecomposition.intervalGraft_T {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    (a b : ℕ) (hab : a ≤ b) (hb : b < D.r) :
    (D.intervalGraft a b hab hb).T = D.Y ⟨a, by omega⟩ ∪ D.Y ⟨b + 1, by omega⟩ :=
  rfl

theorem GraftPathDecomposition.intervalGraft_single {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (i : Fin D.r) :
    D.intervalGraft i.1 i.1 (le_refl _) i.2 = D.partGraft i := by
  apply Graft.ext
  · exact D.intervalGraph_single i
  · rfl

theorem GraftPathDecomposition.intervalGraft_zero_last {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) :
    D.intervalGraft 0 (D.r - 1) (Nat.zero_le _) (by have := D.hr; omega) = X := by
  have hr := D.hr
  apply Graft.ext
  · exact D.intervalGraph_zero_last
  · change D.Y ⟨0, Nat.zero_lt_succ D.r⟩ ∪ D.Y ⟨D.r - 1 + 1, by omega⟩ = X.T
    have hlast : (⟨D.r - 1 + 1, by omega⟩ : Fin (D.r + 1)) = Fin.last D.r :=
      Fin.ext (by dsimp [Fin.last]; omega)
    rw [hlast, D.T_eq]

/-- Splitting $X_{[a, c]}$ at $b$ ($a \le b < c < D.r$) gives a two-piece gluing of $X_{[a, b]}$
and $X_{[b + 1, c]}$. -/
theorem GraftPathDecomposition.isTwoPieceGluing_intervalGraft {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b + 1 ≤ c) (hc : c < D.r) :
    IsTwoPieceGluing (D.intervalGraft a c (by omega) hc)
      (D.intervalGraft a b hab (by omega))
      (D.intervalGraft (b + 1) c hbc hc) where
  le_A := by
    refine ⟨?_, ?_⟩
    · rintro v ⟨_, ⟨i, rfl⟩, ⟨_, ⟨⟨hai, hib⟩, rfl⟩, hv⟩⟩
      exact mem_iUnion₂.2 ⟨i, ⟨hai, by omega⟩, hv⟩
    · intro e x y hlink
      simp only [intervalGraft_G, intervalGraph_isLink] at hlink ⊢
      rcases hlink with ⟨⟨_, ⟨i, rfl⟩, ⟨_, ⟨⟨hai, hib⟩, rfl⟩, he⟩⟩, hlink⟩
      exact ⟨mem_iUnion₂.2 ⟨i, ⟨hai, by omega⟩, he⟩, hlink⟩
  le_B := by
    refine ⟨?_, ?_⟩
    · rintro v ⟨_, ⟨i, rfl⟩, ⟨_, ⟨⟨hbi, hic⟩, rfl⟩, hv⟩⟩
      exact mem_iUnion₂.2 ⟨i, ⟨by omega, hic⟩, hv⟩
    · intro e x y hlink
      simp only [intervalGraft_G, intervalGraph_isLink] at hlink ⊢
      rcases hlink with ⟨⟨_, ⟨i, rfl⟩, ⟨_, ⟨⟨hbi, hic⟩, rfl⟩, he⟩⟩, hlink⟩
      exact ⟨mem_iUnion₂.2 ⟨i, ⟨by omega, hic⟩, he⟩, hlink⟩
  vertexSet_union := by
    simp only [intervalGraft_G, intervalGraph_vertexSet_eq]
    ext v
    simp only [mem_union, intervalVerts, mem_iUnion]
    constructor
    · rintro (⟨i, ⟨hai, hib⟩, hv⟩ | ⟨i, ⟨hbi, hic⟩, hv⟩)
      · exact ⟨i, ⟨hai, by omega⟩, hv⟩
      · exact ⟨i, ⟨by omega, hic⟩, hv⟩
    · rintro ⟨i, ⟨hai, hic⟩, hv⟩
      by_cases hib : i.1 ≤ b
      · exact Or.inl ⟨i, ⟨hai, hib⟩, hv⟩
      · exact Or.inr ⟨i, ⟨by omega, hic⟩, hv⟩
  edgeSet_union := by
    simp only [intervalGraft_G, intervalGraph_edgeSet_eq]
    ext e
    simp only [mem_union, intervalEdges, mem_iUnion]
    constructor
    · rintro (⟨i, ⟨hai, hib⟩, he⟩ | ⟨i, ⟨hbi, hic⟩, he⟩)
      · exact ⟨i, ⟨hai, by omega⟩, he⟩
      · exact ⟨i, ⟨by omega, hic⟩, he⟩
    · rintro ⟨i, ⟨hai, hic⟩, he⟩
      by_cases hib : i.1 ≤ b
      · exact Or.inl ⟨i, ⟨hai, hib⟩, he⟩
      · exact Or.inr ⟨i, ⟨by omega, hic⟩, he⟩
  edge_disjoint := by
    simp only [intervalGraft_G, intervalGraph_edgeSet_eq]
    rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
    rintro e ⟨⟨_, ⟨i, rfl⟩, ⟨_, ⟨⟨_, hib⟩, rfl⟩, hei⟩⟩,
      ⟨_, ⟨j, rfl⟩, ⟨_, ⟨⟨hbj, _⟩, rfl⟩, hej⟩⟩⟩
    have hij : i ≠ j := by
      intro h
      subst h
      omega
    exact (D.edge_disjoint i j hij).notMem_of_mem_left hei hej
  inter_sub_TA := by
    simp only [intervalGraft_G, intervalGraph_vertexSet_eq]
    rintro v ⟨⟨_, ⟨i, rfl⟩, ⟨_, ⟨⟨_, hib⟩, rfl⟩, hvi⟩⟩,
      ⟨_, ⟨j, rfl⟩, ⟨_, ⟨⟨hbj, _⟩, rfl⟩, hvj⟩⟩⟩
    right
    exact D.inter_subset_Y_succ (i := ⟨b, by omega⟩) hib (by change b < j.1; omega)
      (by dsimp; omega) ⟨hvi, hvj⟩
  inter_sub_TB := by
    simp only [intervalGraft_G, intervalGraph_vertexSet_eq]
    rintro v ⟨⟨_, ⟨i, rfl⟩, ⟨_, ⟨⟨_, hib⟩, rfl⟩, hvi⟩⟩,
      ⟨_, ⟨j, rfl⟩, ⟨_, ⟨⟨hbj, _⟩, rfl⟩, hvj⟩⟩⟩
    left
    exact D.inter_subset_Y_succ (i := ⟨b, by omega⟩) hib (by change b < j.1; omega)
      (by dsimp; omega) ⟨hvi, hvj⟩
  T_sub_union := by
    rintro v (hva | hvc)
    · exact Or.inl (Or.inl hva)
    · exact Or.inr (Or.inr hvc)
  union_diff_sub_T := by
    simp only [intervalGraft_G, intervalGraph_vertexSet_eq, intervalGraft_T]
    rintro v ⟨(hva | hvb) | (hvb | hvc), hnot_inter⟩
    · exact Or.inl hva
    · exfalso
      apply hnot_inter
      have hvb_left : v ∈ V(D.G ⟨b, by omega⟩) :=
        D.Y_subset ⟨b, by omega⟩ (Or.inr hvb)
      have hvb_right : v ∈ V(D.G ⟨b + 1, by omega⟩) :=
        D.Y_subset ⟨b + 1, by omega⟩ (Or.inl hvb)
      exact ⟨mem_iUnion₂.2 ⟨⟨b, by omega⟩, ⟨hab, le_refl b⟩, hvb_left⟩,
        mem_iUnion₂.2 ⟨⟨b + 1, by omega⟩, ⟨le_refl (b + 1), hbc⟩, hvb_right⟩⟩
    · exfalso
      apply hnot_inter
      have hvb_left : v ∈ V(D.G ⟨b, by omega⟩) :=
        D.Y_subset ⟨b, by omega⟩ (Or.inr hvb)
      have hvb_right : v ∈ V(D.G ⟨b + 1, by omega⟩) :=
        D.Y_subset ⟨b + 1, by omega⟩ (Or.inl hvb)
      exact ⟨mem_iUnion₂.2 ⟨⟨b, by omega⟩, ⟨hab, le_refl b⟩, hvb_left⟩,
        mem_iUnion₂.2 ⟨⟨b + 1, by omega⟩, ⟨le_refl (b + 1), hbc⟩, hvb_right⟩⟩
    · exact Or.inr hvc

/-- When $D.r \ge 3$, the middle subgraphs $G_1, \dots, G_{r-2}$ and boundary sets
$Y_1, \dots, Y_{r-1}$ form a path-decomposition of the middle interval graft
$X_{[1, r-2]}$ over $\mathscr{A}$. -/
def GraftPathDecomposition.middlePathDecomposition {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (hr3 : 3 ≤ D.r) :
    GraftPathDecomposition 𝒜 (D.intervalGraft 1 (D.r - 2) (by omega) (by omega)) where
  r := D.r - 2
  hr := by omega
  G i := D.G ⟨i.1 + 1, by have := i.2; omega⟩
  Y i := D.Y ⟨i.1 + 1, by have := i.2; omega⟩
  Y_subset i := D.Y_subset ⟨i.1 + 1, by have := i.2; omega⟩
  le_G i := D.part_le_intervalGraph (a := 1) (b := D.r - 2)
    ⟨i.1 + 1, by have := i.2; omega⟩ ⟨by dsimp; omega, by dsimp; have : i.1 < D.r - 2 := i.2; omega⟩
  mem_𝒜 i := D.mem_𝒜 ⟨i.1 + 1, by have := i.2; omega⟩
  vertexSet_iUnion := by
    change (⋃ i : Fin (D.r - 2), V(D.G ⟨i.1 + 1, _⟩)) =
      V(D.intervalGraph 1 (D.r - 2))
    rw [D.intervalGraph_vertexSet_eq]
    ext v
    simp only [intervalVerts, mem_iUnion]
    constructor
    · rintro ⟨i, hv⟩
      have hi : i.1 < D.r - 2 := i.2
      exact ⟨⟨i.1 + 1, by omega⟩, ⟨by dsimp; omega, by dsimp; omega⟩, hv⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, hv⟩
      have hj : j.1 < D.r := j.2
      refine ⟨⟨j.1 - 1, by omega⟩, ?_⟩
      have heq : (⟨j.1 - 1 + 1, by omega⟩ : Fin D.r) = j := Fin.ext (by dsimp; omega)
      rwa [heq]
  edgeSet_iUnion := by
    change (⋃ i : Fin (D.r - 2), E(D.G ⟨i.1 + 1, _⟩)) =
      E(D.intervalGraph 1 (D.r - 2))
    rw [D.intervalGraph_edgeSet_eq]
    ext e
    simp only [intervalEdges, mem_iUnion]
    constructor
    · rintro ⟨i, he⟩
      have hi : i.1 < D.r - 2 := i.2
      exact ⟨⟨i.1 + 1, by omega⟩, ⟨by dsimp; omega, by dsimp; omega⟩, he⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, he⟩
      have hj : j.1 < D.r := j.2
      refine ⟨⟨j.1 - 1, by omega⟩, ?_⟩
      have heq : (⟨j.1 - 1 + 1, by omega⟩ : Fin D.r) = j := Fin.ext (by dsimp; omega)
      rwa [heq]
  edge_disjoint i j hij := by
    apply D.edge_disjoint
    intro h
    apply hij
    have hi := i.2
    have hj := j.2
    have hval : i.1 + 1 = j.1 + 1 := Fin.ext_iff.mp h
    exact Fin.ext (by omega)
  vertex_inter_subset h i j hhi hij := by
    have hh := h.2
    have hi := i.2
    have hj := j.2
    exact D.vertex_inter_subset ⟨h.1 + 1, by omega⟩ ⟨i.1 + 1, by omega⟩ ⟨j.1 + 1, by omega⟩
      (by change h.1 + 1 ≤ i.1 + 1; have : h.1 ≤ i.1 := hhi; omega)
      (by change i.1 + 1 ≤ j.1 + 1; have : i.1 ≤ j.1 := hij; omega)
  adj_vertex_inter i hi := by
    have hi_lt := i.2
    exact D.adj_vertex_inter ⟨i.1 + 1, by omega⟩ (by change i.1 + 1 + 1 < D.r; omega)
  T_eq := rfl

/-- In a $k$-train $X$ with $r \ge 3$, if $P_1, \dots, P_k$ are $k$ mutually vertex-disjoint paths
of $X.G$ from $Y_1$ to $Y_{r-1}$, then each $P_p$ is a subgraph of the middle interval graph
$G_{[1, r-2]}$. -/
theorem GraftPathDecomposition.middle_paths_le_intervalGraph {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (hr3 : 3 ≤ D.r)
    {k : ℕ} (hY_card : ∀ (i : ℕ) (hi : i < D.r + 1), 1 ≤ i → i < D.r → (D.Y ⟨i, hi⟩).ncard = k)
    {P : Fin k → Graph α β}
    (hP_path : ∀ p : Fin k,
      IsGraphPathFromTo X.G (P p) (D.Y ⟨1, by omega⟩) (D.Y ⟨D.r - 1, by omega⟩))
    (hP_disj : ∀ p q : Fin k, p ≠ q → Disjoint V(P p) V(P q))
    (p : Fin k) :
    P p ≤ D.intervalGraph 1 (D.r - 2) := by
  let y₁ : Fin (D.r + 1) := ⟨1, by omega⟩
  let y₂ : Fin (D.r + 1) := ⟨D.r - 1, by omega⟩
  have hy₁_sub : D.Y y₁ ⊆ V(X.G) :=
    (subset_union_right.trans (D.Y_subset ⟨0, D.hr⟩)).trans (D.le_G ⟨0, D.hr⟩).vertexSet_mono
  have hy₂_sub : D.Y y₂ ⊆ V(X.G) :=
    (subset_union_left.trans (D.Y_subset ⟨D.r - 1, by omega⟩)).trans
      (D.le_G ⟨D.r - 1, by omega⟩).vertexSet_mono
  have hy₁_one : (D.Y y₁ ∩ V(P p)).ncard = 1 := by
    refine (ncard_eq_one_and_iUnion_eq_of_disjoint_nonempty
      (X.finite_G.1.subset hy₁_sub) (hY_card 1 (by omega) (le_refl 1) (by omega))
      (fun _ => inter_subset_left) (fun q => ?_)
      (fun q₁ q₂ hne => (hP_disj q₁ q₂ hne).mono inter_subset_right inter_subset_right)).1 p
    obtain ⟨u, hu, _, _, ⟨wq⟩⟩ := hP_path q
    exact ⟨u, hu, wq.head_mem⟩
  have hy₂_one : (D.Y y₂ ∩ V(P p)).ncard = 1 := by
    refine (ncard_eq_one_and_iUnion_eq_of_disjoint_nonempty
      (X.finite_G.1.subset hy₂_sub) (hY_card (D.r - 1) (by omega) (by omega) (by omega))
      (fun _ => inter_subset_left) (fun q => ?_)
      (fun q₁ q₂ hne => (hP_disj q₁ q₂ hne).mono inter_subset_right inter_subset_right)).1 p
    obtain ⟨_, _, v, hv, ⟨wq⟩⟩ := hP_path q
    exact ⟨v, hv, wq.last_mem⟩
  obtain ⟨u, hu, v, hv, ⟨wp⟩⟩ := hP_path p
  have hlen := wp.length_verts
  have hu_unique : ∀ x ∈ D.Y y₁ ∩ V(P p), x = u := by
    obtain ⟨z, hz⟩ := ncard_eq_one.mp hy₁_one
    have hu_z : u = z := mem_singleton_iff.mp (hz ▸ ⟨hu, wp.head_mem⟩)
    intro x hx
    exact (mem_singleton_iff.mp (hz ▸ hx)).trans hu_z.symm
  have hv_unique : ∀ x ∈ D.Y y₂ ∩ V(P p), x = v := by
    obtain ⟨z, hz⟩ := ncard_eq_one.mp hy₂_one
    have hv_z : v = z := mem_singleton_iff.mp (hz ▸ ⟨hv, wp.last_mem⟩)
    intro x hx
    exact (mem_singleton_iff.mp (hz ▸ hx)).trans hv_z.symm
  let g_pen : Fin D.r := ⟨D.r - 2, by omega⟩
  have hg_pen_succ : g_pen.succ = y₂ := Fin.ext (by dsimp [g_pen, y₂]; omega)
  -- No edge of P p belongs to E(D.G 0)
  have hno_edge_0 : ∀ (s : ℕ) (hs : s < wp.edges.length),
      wp.edges[s]'hs ∉ E(D.G ⟨0, D.hr⟩) := by
    intro s hs he0
    have hlG : X.G.IsLink (wp.edges[s]'hs) (wp.verts[s]'(by omega))
        (wp.verts[s + 1]'(by omega)) :=
      (wp.isLink_step s hs).mono wp.le_G
    have hl0 : (D.G ⟨0, D.hr⟩).IsLink (wp.edges[s]'hs) (wp.verts[s]'(by omega))
        (wp.verts[s + 1]'(by omega)) :=
      ((D.le_G ⟨0, D.hr⟩).isLink_iff he0).mpr hlG
    let g0 : Fin D.r := ⟨0, D.hr⟩
    let S₀ : Set α := ⋃ (l : Fin D.r) (_ : l ≤ g0), V(D.G l)
    have hs1_S₀ : wp.verts[s + 1]'(by omega) ∈ S₀ :=
      mem_biUnion (show g0 ≤ g0 from le_refl g0) hl0.right_mem
    by_cases hlast_S₀ : wp.verts[wp.edges.length]'(by omega) ∈ S₀
    · simp only [S₀, mem_iUnion, exists_prop] at hlast_S₀
      obtain ⟨l, hl_le, hvl⟩ := hlast_S₀
      rw [wp.last_eq] at hvl
      have hv_G : v ∈ V(D.G g_pen) :=
        D.Y_subset g_pen (Or.inr (hg_pen_succ.symm ▸ hv))
      have hv_y1 : v ∈ D.Y y₁ :=
        D.inter_subset_Y_succ (i := g0) hl_le
          (by change 0 < D.r - 2; omega) (by change 0 + 1 < D.r; omega) ⟨hvl, hv_G⟩
      have hvu : v = u := hu_unique v ⟨hv_y1, wp.last_mem⟩
      have heq : wp.verts[wp.edges.length]'(by omega) = wp.verts[0]'(by omega) := by
        rw [wp.last_eq, wp.head_eq, hvu]
      have hinj := (List.nodup_iff_injective_getElem.mp wp.nodup_verts)
        (a₁ := ⟨wp.edges.length, by omega⟩) (a₂ := ⟨0, by omega⟩) heq
      have : wp.edges.length = 0 := Fin.ext_iff.mp hinj
      omega
    · obtain ⟨t, ht, hst, _, htS₀, ht1S₀⟩ :=
        wp.exists_step_exit S₀ (by omega : s + 1 ≤ wp.edges.length) (by omega) hs1_S₀ hlast_S₀
      have hlt_G : X.G.IsLink (wp.edges[t]'ht) (wp.verts[t]'(by omega))
          (wp.verts[t + 1]'(by omega)) :=
        (wp.isLink_step t ht).mono wp.le_G
      have hvt_y1 : wp.verts[t]'(by omega) ∈ D.Y y₁ :=
        D.left_mem_Y_succ_of_isLink_notMem_le (i := g0) (by change 0 + 1 < D.r; omega)
          hlt_G htS₀ ht1S₀
      have hvt_u : wp.verts[t]'(by omega) = wp.verts[0]'(by omega) := by
        rw [wp.head_eq]
        exact hu_unique _ ⟨hvt_y1, wp.getElem_verts_mem t (by omega)⟩
      have hinj := (List.nodup_iff_injective_getElem.mp wp.nodup_verts)
        (a₁ := ⟨t, by omega⟩) (a₂ := ⟨0, by omega⟩) hvt_u
      have : t = 0 := Fin.ext_iff.mp hinj
      omega
  -- No edge of P p belongs to E(D.G (D.r - 1))
  have hno_edge_last : ∀ (s : ℕ) (hs : s < wp.edges.length),
      wp.edges[s]'hs ∉ E(D.G ⟨D.r - 1, by omega⟩) := by
    intro s hs helast
    have hlG : X.G.IsLink (wp.edges[s]'hs) (wp.verts[s]'(by omega))
        (wp.verts[s + 1]'(by omega)) :=
      (wp.isLink_step s hs).mono wp.le_G
    have hllast : (D.G ⟨D.r - 1, by omega⟩).IsLink (wp.edges[s]'hs)
        (wp.verts[s]'(by omega)) (wp.verts[s + 1]'(by omega)) :=
      ((D.le_G ⟨D.r - 1, by omega⟩).isLink_iff helast).mpr hlG
    let S₁ : Set α := ⋃ (l : Fin D.r) (_ : l ≤ g_pen), V(D.G l)
    have h0_S₁ : wp.verts[0]'(by omega) ∈ S₁ := by
      rw [wp.head_eq]
      have hu_G1 : u ∈ V(D.G ⟨1, by omega⟩) := D.Y_subset ⟨1, by omega⟩ (Or.inl hu)
      exact mem_biUnion (show (⟨1, by omega⟩ : Fin D.r) ≤ g_pen by change 1 ≤ D.r - 2; omega)
        hu_G1
    by_cases hs_S₁ : wp.verts[s]'(by omega) ∈ S₁
    · simp only [S₁, mem_iUnion, exists_prop] at hs_S₁
      obtain ⟨l, hl_le, hxl⟩ := hs_S₁
      have hvs_y2 : wp.verts[s]'(by omega) ∈ D.Y y₂ := by
        rw [← hg_pen_succ]
        exact D.inter_subset_Y_succ (i := g_pen) hl_le
          (by change D.r - 2 < D.r - 1; omega) (by change D.r - 2 + 1 < D.r; omega)
          ⟨hxl, hllast.left_mem⟩
      have hvs_v : wp.verts[s]'(by omega) = wp.verts[wp.edges.length]'(by omega) := by
        rw [wp.last_eq]
        exact hv_unique _ ⟨hvs_y2, wp.getElem_verts_mem s (by omega)⟩
      have hinj := (List.nodup_iff_injective_getElem.mp wp.nodup_verts)
        (a₁ := ⟨s, by omega⟩) (a₂ := ⟨wp.edges.length, by omega⟩) hvs_v
      have : s = wp.edges.length := Fin.ext_iff.mp hinj
      omega
    · obtain ⟨t, ht, _, hts, htS₁, ht1S₁⟩ :=
        wp.exists_step_exit S₁ (Nat.zero_le s) (by omega) h0_S₁ hs_S₁
      have hlt_G : X.G.IsLink (wp.edges[t]'ht) (wp.verts[t]'(by omega))
          (wp.verts[t + 1]'(by omega)) :=
        (wp.isLink_step t ht).mono wp.le_G
      have hvt_y2 : wp.verts[t]'(by omega) ∈ D.Y y₂ := by
        rw [← hg_pen_succ]
        exact D.left_mem_Y_succ_of_isLink_notMem_le (i := g_pen)
          (by change D.r - 2 + 1 < D.r; omega) hlt_G htS₁ ht1S₁
      have hvt_v : wp.verts[t]'(by omega) = wp.verts[wp.edges.length]'(by omega) := by
        rw [wp.last_eq]
        exact hv_unique _ ⟨hvt_y2, wp.getElem_verts_mem t (by omega)⟩
      have hinj := (List.nodup_iff_injective_getElem.mp wp.nodup_verts)
        (a₁ := ⟨t, by omega⟩) (a₂ := ⟨wp.edges.length, by omega⟩) hvt_v
      have : t = wp.edges.length := Fin.ext_iff.mp hinj
      omega
  -- Every edge of P p lies in D.intervalEdges 1 (D.r - 2)
  have hedges_mid : ∀ e ∈ E(P p), e ∈ D.intervalEdges 1 (D.r - 2) := by
    intro e he
    rw [wp.edgeSet_eq, mem_ofPred_eq, List.mem_iff_getElem] at he
    obtain ⟨s, hs, rfl⟩ := he
    have heX : wp.edges[s]'hs ∈ E(X.G) := wp.le_G.edgeSet_mono (by
      rw [wp.edgeSet_eq]
      exact List.getElem_mem hs)
    obtain ⟨m, hem⟩ := D.exists_mem_edgeSet heX
    have hm_lt := m.2
    have hm0 : m.1 ≠ 0 := by
      intro h0
      have hmeq : m = ⟨0, D.hr⟩ := Fin.ext h0
      exact hno_edge_0 s hs (hmeq ▸ hem)
    have hmlast : m.1 ≠ D.r - 1 := by
      intro hlast
      have hmeq : m = ⟨D.r - 1, by omega⟩ := Fin.ext hlast
      exact hno_edge_last s hs (hmeq ▸ hem)
    exact mem_iUnion₂.2 ⟨m, ⟨by omega, by omega⟩, hem⟩
  -- Every vertex of P p lies in V(D.intervalGraph 1 (D.r - 2))
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [D.intervalGraph_vertexSet_eq]
    rw [wp.vertexSet_eq, mem_ofPred_eq, List.mem_iff_getElem] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    by_cases hedges : wp.edges.length = 0
    · have hs0 : s = 0 := by omega
      subst hs0
      rw [wp.head_eq]
      exact mem_iUnion₂.2 ⟨⟨1, by omega⟩, ⟨le_refl 1, by change 1 ≤ D.r - 2; omega⟩,
        D.Y_subset ⟨1, by omega⟩ (Or.inl hu)⟩
    · by_cases hs_lt : s < wp.edges.length
      · have hl := (wp.isLink_step s hs_lt).mono wp.le_G
        have he_mem : wp.edges[s]'hs_lt ∈ E(P p) := by
          rw [wp.edgeSet_eq]
          exact List.getElem_mem hs_lt
        exact D.inc_mem_intervalVerts 1 (D.r - 2) (hedges_mid _ he_mem) hl.inc_left
      · have hs_eq : s = wp.edges.length := by omega
        have hprev : s - 1 < wp.edges.length := by omega
        have hl := (wp.isLink_step (s - 1) hprev).mono wp.le_G
        have he_mem : wp.edges[s - 1]'hprev ∈ E(P p) := by
          rw [wp.edgeSet_eq]
          exact List.getElem_mem hprev
        have hinc : X.G.Inc (wp.edges[s - 1]'hprev) (wp.verts[s]'hs) := by
          convert hl.inc_right using 2
          omega
        exact D.inc_mem_intervalVerts 1 (D.r - 2) (hedges_mid _ he_mem) hinc
  · intro e x y hlink
    rw [D.intervalGraph_isLink]
    exact ⟨hedges_mid e hlink.edge_mem, hlink.mono wp.le_G⟩

/-- In a $k$-train $X$ over $\mathscr{A}$ with $r \ge 3$, the middle interval graft
$X_{[1, r-2]}$ belongs to `kChainClass 𝒜 k`. -/
theorem GraftPathDecomposition.middle_intervalGraft_mem_kChainClass {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (hr3 : 3 ≤ D.r)
    {k : ℕ} (hY_card : ∀ (i : ℕ) (hi : i < D.r + 1), 1 ≤ i → i < D.r → (D.Y ⟨i, hi⟩).ncard = k)
    (hpaths : HasDisjointGraphPathsFromTo X.G
      (D.Y ⟨1, by omega⟩) (D.Y ⟨D.r - 1, by omega⟩) k) :
    D.intervalGraft 1 (D.r - 2) (by omega) (by omega) ∈ kChainClass 𝒜 k := by
  obtain ⟨P, hP_path, hP_disj⟩ := hpaths
  refine ⟨D.middlePathDecomposition hr3, ?_, P, ?_, hP_disj⟩
  · intro i
    have hi := i.2
    change i.1 < D.r - 2 + 1 at hi
    exact hY_card (i.1 + 1) (by omega) (by omega) (by omega)
  · intro p
    have hle := D.middle_paths_le_intervalGraph hr3 hY_card hP_path hP_disj p
    obtain ⟨u, hu, v, hv, ⟨wp⟩⟩ := hP_path p
    have hu' : u ∈ (D.middlePathDecomposition hr3).Y
        ⟨0, Nat.zero_lt_succ (D.middlePathDecomposition hr3).r⟩ := hu
    have hv' : v ∈ (D.middlePathDecomposition hr3).Y
        (Fin.last (D.middlePathDecomposition hr3).r) := by
      change v ∈ D.Y ⟨D.r - 2 + 1, _⟩
      have heq : (⟨D.r - 2 + 1, by omega⟩ : Fin (D.r + 1)) = ⟨D.r - 1, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rwa [heq]
    exact ⟨u, hu', v, hv', ⟨{
      verts := wp.verts
      edges := wp.edges
      le_G := hle
      length_verts := wp.length_verts
      nodup_verts := wp.nodup_verts
      head_eq := wp.head_eq
      last_eq := wp.last_eq
      vertexSet_eq := wp.vertexSet_eq
      edgeSet_eq := wp.edgeSet_eq
      isLink_step := wp.isLink_step
    }⟩⟩

/-! ## Numbered results (14.3), (14.4), and (14.5) -/

/-- **Graph Minors VIII, (14.3)** (page 279):
"(14.3) *Every $k$-train over $\mathcal{A}$ belongs to
$W(\mathcal{A}^* \oplus \mathcal{B}^* \oplus \mathcal{A}^*) \cup
W(\mathcal{A}^* \oplus \mathcal{A}^*) \cup \mathcal{A}$ where $\mathcal{B}$ is the class of all
$k$-chains over $\mathcal{A}$.*" -/
theorem theorem_14_3_proof {α : Type u} {β : Type v} [Infinite α]
    (𝒜 : Set (Graft α β)) (k : ℕ) :
    let ℬ := kChainClass 𝒜 k
    LKGraftClass k 𝒜 ⊆
      WGraftClass (graftDirectSumClass (isoGraftClass 𝒜)
        (graftDirectSumClass (isoGraftClass ℬ) (isoGraftClass 𝒜))) ∪
      WGraftClass (graftDirectSumClass (isoGraftClass 𝒜) (isoGraftClass 𝒜)) ∪
      𝒜 := by
  intro ℬ X ⟨D, hY_card, hpaths⟩
  have hr := D.hr
  by_cases hr1 : D.r = 1
  · -- Case r = 1: X ∈ 𝒜
    right
    have h0_mem : D.partGraft ⟨0, hr⟩ ∈ 𝒜 := D.mem_𝒜 ⟨0, hr⟩
    have h_eq : D.partGraft ⟨0, hr⟩ = X := by
      rw [← D.intervalGraft_single ⟨0, hr⟩]
      have hlast := D.intervalGraft_zero_last
      simpa [hr1] using hlast
    rwa [h_eq] at h0_mem
  by_cases hr2 : D.r = 2
  · -- Case r = 2: X ∈ W(𝒜^* ⊕ 𝒜^*)
    left; right
    have hgluing : IsTwoPieceGluing (D.intervalGraft 0 1 (by omega) (by omega))
        (D.intervalGraft 0 0 (le_refl 0) hr)
        (D.intervalGraft 1 1 (le_refl 1) (by omega)) :=
      D.isTwoPieceGluing_intervalGraft (le_refl 0) (le_refl 1) (by omega)
    have hX_eq : D.intervalGraft 0 1 (by omega) (by omega) = X := by
      have hlast := D.intervalGraft_zero_last
      simpa [hr2] using hlast
    rw [hX_eq, D.intervalGraft_single ⟨0, hr⟩, D.intervalGraft_single ⟨1, by omega⟩] at hgluing
    exact mem_WGraftClass_of_isTwoPieceGluing hgluing
      (D.mem_𝒜 ⟨0, hr⟩) (D.mem_𝒜 ⟨1, by omega⟩)
  · -- Case r ≥ 3: X ∈ W(𝒜^* ⊕ (ℬ^* ⊕ 𝒜^*))
    left; left
    have hr3 : 3 ≤ D.r := by omega
    have hM_mem : D.intervalGraft 1 (D.r - 2) (by omega) (by omega) ∈ ℬ :=
      D.middle_intervalGraft_mem_kChainClass hr3 hY_card (hpaths hr3)
    have hgluing₁ : IsTwoPieceGluing (D.intervalGraft 0 (D.r - 1) (Nat.zero_le _) (by omega))
        (D.intervalGraft 0 0 (le_refl 0) hr)
        (D.intervalGraft 1 (D.r - 1) (by omega) (by omega)) :=
      D.isTwoPieceGluing_intervalGraft (le_refl 0) (by omega) (by omega)
    rw [D.intervalGraft_zero_last, D.intervalGraft_single ⟨0, hr⟩] at hgluing₁
    have hgluing₂ : IsTwoPieceGluing (D.intervalGraft 1 (D.r - 1) (by omega) (by omega))
        (D.intervalGraft 1 (D.r - 2) (by omega) (by omega))
        (D.partGraft ⟨D.r - 1, by omega⟩) := by
      rw [← D.intervalGraft_single ⟨D.r - 1, by omega⟩]
      convert D.isTwoPieceGluing_intervalGraft (a := 1) (b := D.r - 2) (c := D.r - 1)
        (by omega) (by omega) (by omega) using 2
      change D.r - 1 = D.r - 2 + 1
      omega
    exact mem_WGraftClass_of_isThreePieceGluing hgluing₁ hgluing₂
      (D.mem_𝒜 ⟨0, hr⟩) hM_mem (D.mem_𝒜 ⟨D.r - 1, by omega⟩)

/-- A subset of a well-rooted class of grafts is well-rooted. -/
theorem isWellRootedGraftClass_mono {α : Type u} {β : Type v}
    {𝒜 ℬ : Set (Graft α β)} (hsub : 𝒜 ⊆ ℬ) (hℬ : IsWellRootedGraftClass ℬ) :
    IsWellRootedGraftClass 𝒜 :=
  fun X hX => hℬ X (fun n => hsub (hX n))

/-- **Graph Minors VIII, (14.4)** (page 279):
"(14.4) *If $\mathcal{A}$ is well-rooted then so is $L^k(\mathcal{A})$.*" -/
theorem theorem_14_4_proof {α : Type u} {β : Type v} [Infinite α]
    (𝒜 : Set (Graft α β)) (k : ℕ) (h𝒜 : IsWellRootedGraftClass 𝒜) :
    IsWellRootedGraftClass (LKGraftClass k 𝒜) := by
  let ℬ := kChainClass 𝒜 k
  have h𝒜_iso : IsWellRootedGraftClass (isoGraftClass 𝒜) :=
    isWellRootedGraftClass_isoGraftClass h𝒜
  have hℬ : IsWellRootedGraftClass ℬ := theorem_14_2_proof h𝒜 k
  have hℬ_iso : IsWellRootedGraftClass (isoGraftClass ℬ) :=
    isWellRootedGraftClass_isoGraftClass hℬ
  have h₁ : IsWellRootedGraftClass
      (WGraftClass (graftDirectSumClass (isoGraftClass 𝒜)
        (graftDirectSumClass (isoGraftClass ℬ) (isoGraftClass 𝒜)))) :=
    theorem_13_3_proof (theorem_13_1_proof h𝒜_iso (theorem_13_1_proof hℬ_iso h𝒜_iso))
  have h₂ : IsWellRootedGraftClass
      (WGraftClass (graftDirectSumClass (isoGraftClass 𝒜) (isoGraftClass 𝒜))) :=
    theorem_13_3_proof (theorem_13_1_proof h𝒜_iso h𝒜_iso)
  exact isWellRootedGraftClass_mono (theorem_14_3_proof 𝒜 k)
    (theorem_4_2_proof (theorem_4_2_proof h₁ h₂) h𝒜)

/-- Every graft in $\mathscr{A}$ is a 1-term $k$-train over $\mathscr{A}$, so
$\mathscr{A} \subseteq L^k(\mathscr{A})$. -/
theorem subset_LKGraftClass {α : Type u} {β : Type v}
    (k : ℕ) (𝒜 : Set (Graft α β)) :
    𝒜 ⊆ LKGraftClass k 𝒜 := by
  intro X hX
  let D : GraftPathDecomposition 𝒜 X := {
    r := 1
    hr := le_refl 1
    G := fun _ => X.G
    Y := fun i => if i.1 = 0 then X.T else ∅
    Y_subset := fun i => by
      rintro v (hv | hv)
      · by_cases hi0 : i.1 = 0
        · simp only [Fin.val_castSucc, hi0, ↓reduceIte] at hv
          exact X.T_subset hv
        · simp only [Fin.val_castSucc, hi0, ↓reduceIte] at hv
          exact False.elim hv
      · have hi1 : i.succ.1 ≠ 0 := by
          change i.1 + 1 ≠ 0
          omega
        simp only [hi1, ↓reduceIte] at hv
        exact False.elim hv
    le_G := fun _ => le_refl X.G
    mem_𝒜 := fun i => by
      have hi0 : i.1 = 0 := by
        have := i.2
        change i.1 < 1 at this
        omega
      have hi1 : i.succ.1 ≠ 0 := by
        change i.1 + 1 ≠ 0
        omega
      have h_eq : Graft.mk X.G ((if i.castSucc.1 = 0 then X.T else ∅) ∪
          (if i.succ.1 = 0 then X.T else ∅)) (by
            simp only [Fin.val_castSucc, hi0, ↓reduceIte, hi1, union_empty]
            exact X.T_subset) X.finite_G = X := by
        apply Graft.ext
        · rfl
        · change (if i.1 = 0 then X.T else ∅) ∪ (if i.succ.1 = 0 then X.T else ∅) = X.T
          simp
      rwa [h_eq]
    vertexSet_iUnion := iUnion_const V(X.G)
    edgeSet_iUnion := iUnion_const E(X.G)
    edge_disjoint := fun i j hij => by
      exfalso
      apply hij
      ext
      have hi := i.2
      have hj := j.2
      change i.1 < 1 at hi
      change j.1 < 1 at hj
      omega
    vertex_inter_subset := fun _ _ _ _ _ => inter_subset_left
    adj_vertex_inter := fun i hi => by omega
    T_eq := by simp [Fin.last]
  }
  refine ⟨D, ?_, ?_⟩
  · intro i _ h1 hi
    change 1 ≤ i at h1
    change i < 1 at hi
    omega
  · intro hr3
    change 3 ≤ 1 at hr3
    omega

/-- Monotonicity of $L^k$: if $\mathscr{A} \subseteq \mathscr{B}$, then
$L^k(\mathscr{A}) \subseteq L^k(\mathscr{B})$. -/
theorem LKGraftClass_mono {α : Type u} {β : Type v} (k : ℕ)
    {𝒜 ℬ : Set (Graft α β)} (hsub : 𝒜 ⊆ ℬ) :
    LKGraftClass k 𝒜 ⊆ LKGraftClass k ℬ := by
  rintro X ⟨D, hY, hpaths⟩
  refine ⟨{
    r := D.r
    hr := D.hr
    G := D.G
    Y := D.Y
    Y_subset := D.Y_subset
    le_G := D.le_G
    mem_𝒜 := fun i => hsub (D.mem_𝒜 i)
    vertexSet_iUnion := D.vertexSet_iUnion
    edgeSet_iUnion := D.edgeSet_iUnion
    edge_disjoint := D.edge_disjoint
    vertex_inter_subset := D.vertex_inter_subset
    adj_vertex_inter := D.adj_vertex_inter
    T_eq := D.T_eq
  }, hY, hpaths⟩

/-- Monotonicity of $C^k$: if $\mathscr{A} \subseteq \mathscr{B}$, then
$C^k(\mathscr{A}) \subseteq C^k(\mathscr{B})$. -/
theorem CKGraftClass_mono {α : Type u} {β : Type v} (k : ℕ) :
    ∀ {𝒜 ℬ : Set (Graft α β)}, 𝒜 ⊆ ℬ → CKGraftClass k 𝒜 ⊆ CKGraftClass k ℬ := by
  induction k with
  | zero =>
    intro 𝒜 ℬ hsub
    exact LKGraftClass_mono 0 hsub
  | succ k ih =>
    intro 𝒜 ℬ hsub
    exact ih (LKGraftClass_mono (k + 1) hsub)

/-- For every $k$ and $\mathscr{A}$, $C^k(\mathscr{A}) \subseteq C^{k+1}(\mathscr{A})$. -/
theorem CKGraftClass_subset_succ {α : Type u} {β : Type v}
    (k : ℕ) (𝒜 : Set (Graft α β)) :
    CKGraftClass k 𝒜 ⊆ CKGraftClass (k + 1) 𝒜 :=
  CKGraftClass_mono k (subset_LKGraftClass (k + 1) 𝒜)

/-- If $k \le m$, then $C^k(\mathscr{A}) \subseteq C^m(\mathscr{A})$. -/
theorem CKGraftClass_mono_nat {α : Type u} {β : Type v}
    {k m : ℕ} (hkm : k ≤ m) (𝒜 : Set (Graft α β)) :
    CKGraftClass k 𝒜 ⊆ CKGraftClass m 𝒜 := by
  have haux : ∀ d : ℕ, CKGraftClass k 𝒜 ⊆ CKGraftClass (k + d) 𝒜 := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih => exact ih.trans (CKGraftClass_subset_succ (k + d) 𝒜)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  exact haux d

/-- If every graft in $\mathscr{A}$ has index $\le k_0$ and $k > k_0$, then
$L^k(\mathscr{A}) = \mathscr{A}$. -/
theorem LKGraftClass_eq_self_of_gt_index {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {k₀ k : ℕ}
    (hidx : ∀ Y ∈ 𝒜, Y.index ≤ k₀) (hk : k₀ < k) :
    LKGraftClass k 𝒜 = 𝒜 := by
  apply Subset.antisymm _ (subset_LKGraftClass k 𝒜)
  rintro X ⟨D, hY_card, _⟩
  have hr := D.hr
  by_cases hr1 : D.r = 1
  · have h0_mem : D.partGraft ⟨0, hr⟩ ∈ 𝒜 := D.mem_𝒜 ⟨0, hr⟩
    have h_eq : D.partGraft ⟨0, hr⟩ = X := by
      rw [← D.intervalGraft_single ⟨0, hr⟩]
      have hlast := D.intervalGraft_zero_last
      simpa [hr1] using hlast
    rwa [h_eq] at h0_mem
  · exfalso
    have h1_lt : 1 < D.r := by omega
    have hcard1 : (D.Y ⟨1, by omega⟩).ncard = k :=
      hY_card 1 (by omega) (le_refl 1) h1_lt
    have hsub : D.Y ⟨1, by omega⟩ ⊆ (D.partGraft ⟨0, hr⟩).T :=
      subset_union_right
    have hfin : (D.partGraft ⟨0, hr⟩).T.Finite :=
      (D.partGraft ⟨0, hr⟩).finite_G.1.subset (D.partGraft ⟨0, hr⟩).T_subset
    have hle_T : (D.Y ⟨1, by omega⟩).ncard ≤ (D.partGraft ⟨0, hr⟩).index :=
      ncard_le_ncard hsub hfin
    have hle_k0 : (D.partGraft ⟨0, hr⟩).index ≤ k₀ :=
      hidx (D.partGraft ⟨0, hr⟩) (D.mem_𝒜 ⟨0, hr⟩)
    omega

/-- If every graft in $\mathscr{A}$ has index $\le k_0$, then for every $k \ge k_0$,
$C^k(\mathscr{A}) = C^{k_0}(\mathscr{A})$. -/
theorem CKGraftClass_eq_of_ge_index {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {k₀ k : ℕ}
    (hidx : ∀ Y ∈ 𝒜, Y.index ≤ k₀) (hk : k₀ ≤ k) :
    CKGraftClass k 𝒜 = CKGraftClass k₀ 𝒜 := by
  have haux : ∀ d : ℕ, CKGraftClass (k₀ + d) 𝒜 = CKGraftClass k₀ 𝒜 := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      change CKGraftClass (k₀ + d) (LKGraftClass (k₀ + d + 1) 𝒜) = CKGraftClass k₀ 𝒜
      rw [LKGraftClass_eq_self_of_gt_index hidx (by omega), ih]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact haux d

/-- If $\mathscr{A}$ is well-rooted, then $C^k(\mathscr{A})$ is well-rooted for every $k \ge 0$. -/
theorem isWellRootedGraftClass_CKGraftClass {α : Type u} {β : Type v} [Infinite α]
    (k : ℕ) :
    ∀ {𝒜 : Set (Graft α β)}, IsWellRootedGraftClass 𝒜 →
      IsWellRootedGraftClass (CKGraftClass k 𝒜) := by
  induction k with
  | zero =>
    intro 𝒜 h𝒜
    exact theorem_14_4_proof 𝒜 0 h𝒜
  | succ k ih =>
    intro 𝒜 h𝒜
    exact ih (theorem_14_4_proof 𝒜 (k + 1) h𝒜)

/-- **Graph Minors VIII, (14.5)** (page 279):
"(14.5) *If $\mathcal{A}$ is well-rooted, then the class of all concatenations over $\mathcal{A}$
is well-rooted.*" -/
theorem theorem_14_5_proof {α : Type u} {β : Type v} [Infinite α]
    (𝒜 : Set (Graft α β)) (h𝒜 : IsWellRootedGraftClass 𝒜) :
    IsWellRootedGraftClass (concatenationClass 𝒜) := by
  obtain ⟨k₀, hk₀⟩ := theorem_4_1_proof h𝒜
  have hsub : concatenationClass 𝒜 ⊆ CKGraftClass k₀ 𝒜 := by
    rintro X ⟨k, hXk⟩
    rcases le_or_gt k k₀ with hle | hgt
    · exact CKGraftClass_mono_nat hle 𝒜 hXk
    · rwa [CKGraftClass_eq_of_ge_index hk₀ (le_of_lt hgt)] at hXk
  exact isWellRootedGraftClass_mono hsub (isWellRootedGraftClass_CKGraftClass k₀ h𝒜)

end GraphMinor.GM08
