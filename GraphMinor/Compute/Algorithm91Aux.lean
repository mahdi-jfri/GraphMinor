module

public import GraphMinor.Compute.Specs9

/-!
# Auxiliary Lemmas and Finite Recipe Construction for GM XIII (9.1)

This file provides the combinatorial and graph-theoretic foundations for the algorithm of
**Graph Minors XIII, (9.1)** (page 98):
1. **General Subdivision Lifting (`IsCliqueModel.lift_subdivision`):** Lifting a `K_p`-model
   (`IsCliqueModel`) along an injective vertex map and a family of pairwise internally disjoint
   subdivision walks.
2. **Subwall Configurations (`SubwallParam`):** Finite parameter space of `k` subwalls of an
   elementary wall of height `h`, together with the punctured model graph `G_punct` and eye model
   graph `G_eye`.
3. **Finite Recipes (`Recipe`, `evalRecipe`):** Existence of a finite recipe in `allRecipes p h k`
   whose materialization in `x.G` is a valid `K_p`-model (`IsCliqueModel x.G.toSimpleGraph p`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators Graph

/-! ### Section 1: General Subdivision Lifting for `IsCliqueModel` -/

/-- Whether a list of vertices `L : List α` forms a walk in `G : SimpleGraph α` (every consecutive
pair is adjacent in `G`). -/
def IsSimpleGraphWalkList {α : Type*} (G : SimpleGraph α) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => G.Adj a b ∧ IsSimpleGraphWalkList G (b :: rest)

theorem isSimpleGraphWalkList_iff_isSimpleWalkList {n : ℕ} (G : MultiDigraph n) :
    ∀ L : List (Fin n), IsSimpleGraphWalkList G.toSimpleGraph L ↔ WallOfHeight.IsSimpleWalkList G L
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | _ :: b :: rest =>
    and_congr_right fun _ => isSimpleGraphWalkList_iff_isSimpleWalkList G (b :: rest)

theorem isSimpleGraphWalkList_append_singleton_prefix {α : Type*} {G : SimpleGraph α} :
    ∀ {L : List α} {z : α},
      IsSimpleGraphWalkList G (L ++ [z]) →
      IsSimpleGraphWalkList G L ∧
        ∀ hne : L ≠ [], G.Adj (L.getLast hne) z
  | [], _, _ => ⟨trivial, fun hne => False.elim (hne rfl)⟩
  | [a], z, hw => by
    dsimp [IsSimpleGraphWalkList] at hw
    exact ⟨trivial, fun _ => hw.1⟩
  | a :: b :: rest, z, hw => by
    change G.Adj a b ∧ IsSimpleGraphWalkList G ((b :: rest) ++ [z]) at hw
    obtain ⟨hrest, hlast⟩ := isSimpleGraphWalkList_append_singleton_prefix hw.2
    refine ⟨⟨hw.1, hrest⟩, fun _ => ?_⟩
    rw [List.getLast_cons (List.cons_ne_nil b rest)]
    exact hlast (List.cons_ne_nil b rest)

private lemma reachable_induce_head_of_walkList {α : Type*} [DecidableEq α]
    {G : SimpleGraph α} {S : Finset α} :
    ∀ {L : List α} (hne : L ≠ [])
      (_hw : IsSimpleGraphWalkList G L)
      (hmem : ∀ x ∈ L, x ∈ S)
      (y : α) (hy : y ∈ L),
      (G.induce (S : Set α)).Reachable
        ⟨L.head hne, hmem _ (List.head_mem hne)⟩
        ⟨y, hmem y hy⟩
  | [], hne, _, _, _, _ => False.elim (hne rfl)
  | [_], _, _, _, _, hy => by
    rcases List.mem_singleton.mp hy with rfl
    exact Reachable.refl _
  | a :: b :: rest, _, ⟨hadj, hrest⟩, hmem, y, hy => by
    have haS : a ∈ S := hmem a List.mem_cons_self
    have hbS : b ∈ S := hmem b (List.mem_cons_of_mem a List.mem_cons_self)
    have hadj_ind : (G.induce (S : Set α)).Adj ⟨a, haS⟩ ⟨b, hbS⟩ := hadj
    rcases List.mem_cons.mp hy with rfl | hy_tail
    · exact Reachable.refl _
    · have hrec := reachable_induce_head_of_walkList (List.cons_ne_nil b rest) hrest
        (fun x hx => hmem x (List.mem_cons_of_mem a hx)) y hy_tail
      exact (Adj.reachable hadj_ind).trans hrec

theorem reachable_induce_of_walkList {α : Type*} [DecidableEq α]
    {G : SimpleGraph α} {S : Finset α} {L : List α}
    (hw : IsSimpleGraphWalkList G L) (hS : ∀ x ∈ L, x ∈ S)
    {x y : α} (hx : x ∈ L) (hy : y ∈ L) :
    (G.induce (S : Set α)).Reachable ⟨x, hS x hx⟩ ⟨y, hS y hy⟩ := by
  have hne : L ≠ [] := List.ne_nil_of_mem hx
  exact (reachable_induce_head_of_walkList hne hw hS x hx).symm.trans
    (reachable_induce_head_of_walkList hne hw hS y hy)

/-- Lift a family of branch sets `S₁ : Fin p → Finset α` along `φ : α → β` and a family `e : ι` of
subdivided edges with start vertices `u_e : ι → α` and internal vertex lists `L_e : ι → List β`. -/
def liftSubdivisionModel {p : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]
    (S₁ : Fin p → Finset α) (φ : α → β) (u_e : ι → α) (L_e : ι → List β) (idx : Fin p) :
    Finset β :=
  (S₁ idx).image φ ∪
    Finset.univ.biUnion (fun e : ι => if u_e e ∈ S₁ idx then (L_e e).toFinset else ∅)

theorem mem_liftSubdivisionModel {p : ℕ} {α β ι : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]
    (S₁ : Fin p → Finset α) (φ : α → β) (u_e : ι → α) (L_e : ι → List β)
    (idx : Fin p) (w : β) :
    w ∈ liftSubdivisionModel S₁ φ u_e L_e idx ↔
      (∃ x ∈ S₁ idx, φ x = w) ∨ (∃ e : ι, u_e e ∈ S₁ idx ∧ w ∈ L_e e) := by
  unfold liftSubdivisionModel
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨e, hmem⟩
    split_ifs at hmem with hu
    · exact ⟨e, hu, List.mem_toFinset.mp hmem⟩
    · exact False.elim (Finset.notMem_empty w hmem)
  · rintro ⟨e, hu, hw⟩
    refine ⟨e, ?_⟩
    simp [hu, hw]

/-- **General Subdivision Lifting Lemma for `IsCliqueModel`:**
If `S₁ : Fin p → Finset (Fin n₁)` is a `K_p`-model in `G₁` with `S₁ idx ⊆ V₁` for all `idx`, and
`φ : Fin n₁ → Fin n₂` is injective on `V₁` such that every edge of `G₁` on `V₁` is either an edge of
`G₂` or subdivided by a walk `φ (u_e e) :: (L_e e ++ [φ (v_e e)])` in `G₂` whose internal vertices
`L_e e` are pairwise disjoint and avoid `φ '' V₁`, then `liftSubdivisionModel S₁ φ u_e L_e` is a
`K_p`-model in `G₂`. -/
theorem IsCliqueModel.lift_subdivision {p n₁ n₂ : ℕ} {ι : Type*} [Fintype ι]
    {G₁ : SimpleGraph (Fin n₁)} {V₁ : Finset (Fin n₁)}
    {S₁ : Fin p → Finset (Fin n₁)}
    (hK₁ : IsCliqueModel G₁ p S₁)
    (hS₁_sub : ∀ idx : Fin p, S₁ idx ⊆ V₁)
    {G₂ : SimpleGraph (Fin n₂)}
    (φ : Fin n₁ → Fin n₂)
    (u_e v_e : ι → Fin n₁)
    (L_e : ι → List (Fin n₂))
    (hφ_inj : ∀ x ∈ V₁, ∀ y ∈ V₁, φ x = φ y → x = y)
    (_hu_mem : ∀ e : ι, u_e e ∈ V₁)
    (hwalk : ∀ e : ι, IsSimpleGraphWalkList G₂ (φ (u_e e) :: (L_e e ++ [φ (v_e e)])))
    (havoid : ∀ e : ι, ∀ x ∈ V₁, φ x ∉ L_e e)
    (hdisj_L : ∀ e₁ e₂ : ι, e₁ ≠ e₂ → List.Disjoint (L_e e₁) (L_e e₂))
    (hadj_cov : ∀ x ∈ V₁, ∀ y ∈ V₁, G₁.Adj x y →
      G₂.Adj (φ x) (φ y) ∨ ∃ e : ι, (u_e e = x ∧ v_e e = y) ∨ (u_e e = y ∧ v_e e = x)) :
    IsCliqueModel G₂ p (liftSubdivisionModel S₁ φ u_e L_e) := by
  let S₂ := liftSubdivisionModel S₁ φ u_e L_e
  have hprefix_walk : ∀ e : ι, IsSimpleGraphWalkList G₂ (φ (u_e e) :: L_e e) ∧
      G₂.Adj ((φ (u_e e) :: L_e e).getLast (List.cons_ne_nil _ _)) (φ (v_e e)) := by
    intro e
    have hw : IsSimpleGraphWalkList G₂ ((φ (u_e e) :: L_e e) ++ [φ (v_e e)]) := hwalk e
    obtain ⟨h1, h2⟩ := isSimpleGraphWalkList_append_singleton_prefix hw
    exact ⟨h1, h2 (List.cons_ne_nil _ _)⟩
  have hprefix_sub : ∀ (idx : Fin p) (e : ι), u_e e ∈ S₁ idx →
      ∀ z ∈ (φ (u_e e) :: L_e e), z ∈ S₂ idx := by
    intro idx e hu z hz
    rw [mem_liftSubdivisionModel]
    rcases List.mem_cons.mp hz with rfl | hzL
    · exact Or.inl ⟨u_e e, hu, rfl⟩
    · exact Or.inr ⟨e, hu, hzL⟩
  have hfull_sub : ∀ (idx : Fin p) (e : ι), u_e e ∈ S₁ idx → v_e e ∈ S₁ idx →
      ∀ z ∈ (φ (u_e e) :: (L_e e ++ [φ (v_e e)])), z ∈ S₂ idx := by
    intro idx e hu hv z hz
    rw [mem_liftSubdivisionModel]
    rcases List.mem_cons.mp hz with rfl | hz_tail
    · exact Or.inl ⟨u_e e, hu, rfl⟩
    · rcases List.mem_append.mp hz_tail with hzL | hz_end
      · exact Or.inr ⟨e, hu, hzL⟩
      · rcases List.mem_singleton.mp hz_end with rfl
        exact Or.inl ⟨v_e e, hv, rfl⟩
  have hstep_reach : ∀ (idx : Fin p) (x y : Fin n₁) (hx : x ∈ S₁ idx) (hy : y ∈ S₁ idx),
      G₁.Adj x y →
      (G₂.induce (S₂ idx : Set (Fin n₂))).Reachable
        ⟨φ x, (mem_liftSubdivisionModel S₁ φ u_e L_e idx (φ x)).mpr (Or.inl ⟨x, hx, rfl⟩)⟩
        ⟨φ y, (mem_liftSubdivisionModel S₁ φ u_e L_e idx (φ y)).mpr (Or.inl ⟨y, hy, rfl⟩)⟩ := by
    intro idx x y hx hy hadj
    rcases hadj_cov x (hS₁_sub idx hx) y (hS₁_sub idx hy) hadj with hadj₂ | ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Adj.reachable hadj₂
    · exact reachable_induce_of_walkList (hwalk e) (hfull_sub idx e hx hy)
        List.mem_cons_self (by simp)
    · exact (reachable_induce_of_walkList (hwalk e) (hfull_sub idx e hy hx)
        List.mem_cons_self (by simp)).symm
  have hwalk₁_reach : ∀ (idx : Fin p) (a b : (S₁ idx : Set (Fin n₁))),
      (G₁.induce (S₁ idx : Set (Fin n₁))).Walk a b →
      (G₂.induce (S₂ idx : Set (Fin n₂))).Reachable
        ⟨φ a.1, (mem_liftSubdivisionModel S₁ φ u_e L_e idx (φ a.1)).mpr (Or.inl ⟨a.1, a.2, rfl⟩)⟩
        ⟨φ b.1, (mem_liftSubdivisionModel S₁ φ u_e L_e idx (φ b.1)).mpr (Or.inl ⟨b.1, b.2, rfl⟩)⟩ := by
    intro idx a b w
    induction w with
    | nil => exact Reachable.refl _
    | @cons u v c hadj _ ih =>
      exact (hstep_reach idx u.1 v.1 u.2 v.2 hadj).trans ih
  refine ⟨fun idx => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · obtain ⟨⟨x₀, hx₀⟩, hconn₁⟩ := hK₁.1 idx
    have hφx₀ : φ x₀ ∈ S₂ idx :=
      (mem_liftSubdivisionModel S₁ φ u_e L_e idx (φ x₀)).mpr (Or.inl ⟨x₀, hx₀, rfl⟩)
    have hto_base : ∀ z : (S₂ idx : Set (Fin n₂)),
        (G₂.induce (S₂ idx : Set (Fin n₂))).Reachable ⟨φ x₀, hφx₀⟩ z := by
      rintro ⟨z, hz⟩
      rcases (mem_liftSubdivisionModel S₁ φ u_e L_e idx z).mp hz with ⟨x, hx, rfl⟩ | ⟨e, hu, hzL⟩
      · rcases hconn₁.preconnected ⟨x₀, hx₀⟩ ⟨x, hx⟩ with ⟨w⟩
        exact hwalk₁_reach idx ⟨x₀, hx₀⟩ ⟨x, hx⟩ w
      · rcases hconn₁.preconnected ⟨x₀, hx₀⟩ ⟨u_e e, hu⟩ with ⟨w⟩
        have hr1 := hwalk₁_reach idx ⟨x₀, hx₀⟩ ⟨u_e e, hu⟩ w
        have hr2 := reachable_induce_of_walkList (hprefix_walk e).1 (hprefix_sub idx e hu)
          List.mem_cons_self (List.mem_cons_of_mem _ hzL)
        exact hr1.trans hr2
    refine ⟨⟨φ x₀, hφx₀⟩, ?_⟩
    have : Nonempty (S₂ idx : Set (Fin n₂)) := ⟨⟨φ x₀, hφx₀⟩⟩
    exact ⟨fun a b => (hto_base a).symm.trans (hto_base b)⟩
  · rw [Finset.disjoint_left]
    intro w hwi hwj
    rcases (mem_liftSubdivisionModel S₁ φ u_e L_e i w).mp hwi with ⟨x, hxi, heq₁⟩ | ⟨e₁, hu₁, hw₁⟩
    · rcases (mem_liftSubdivisionModel S₁ φ u_e L_e j w).mp hwj with ⟨y, hyj, heq₂⟩ | ⟨e₂, _, hw₂⟩
      · have hxy : x = y := hφ_inj x (hS₁_sub i hxi) y (hS₁_sub j hyj) (heq₁.trans heq₂.symm)
        subst hxy
        exact Finset.disjoint_left.mp (hK₁.2.1 i j hij) hxi hyj
      · exact havoid e₂ x (hS₁_sub i hxi) (heq₁ ▸ hw₂)
    · rcases (mem_liftSubdivisionModel S₁ φ u_e L_e j w).mp hwj with ⟨y, hyj, heq₂⟩ | ⟨e₂, hu₂, hw₂⟩
      · exact havoid e₁ y (hS₁_sub j hyj) (heq₂ ▸ hw₁)
      · by_cases he : e₁ = e₂
        · subst he
          exact Finset.disjoint_left.mp (hK₁.2.1 i j hij) hu₁ hu₂
        · exact List.disjoint_left.mp (hdisj_L e₁ e₂ he) hw₁ hw₂
  · obtain ⟨x, hxi, y, hyj, hadj⟩ := hK₁.2.2 i j hij
    rcases hadj_cov x (hS₁_sub i hxi) y (hS₁_sub j hyj) hadj with hadj₂ | ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨φ x, (mem_liftSubdivisionModel S₁ φ u_e L_e i (φ x)).mpr (Or.inl ⟨x, hxi, rfl⟩),
        φ y, (mem_liftSubdivisionModel S₁ φ u_e L_e j (φ y)).mpr (Or.inl ⟨y, hyj, rfl⟩), hadj₂⟩
    · have hw_mem : (φ (u_e e) :: L_e e).getLast (List.cons_ne_nil _ _) ∈ S₂ i :=
        hprefix_sub i e hxi _ (List.getLast_mem (List.cons_ne_nil _ _))
      have hy_mem : φ (v_e e) ∈ S₂ j :=
        (mem_liftSubdivisionModel S₁ φ u_e L_e j (φ (v_e e))).mpr (Or.inl ⟨v_e e, hyj, rfl⟩)
      exact ⟨(φ (u_e e) :: L_e e).getLast (List.cons_ne_nil _ _), hw_mem,
        φ (v_e e), hy_mem, (hprefix_walk e).2⟩
    · have hx_mem : φ (v_e e) ∈ S₂ i :=
        (mem_liftSubdivisionModel S₁ φ u_e L_e i (φ (v_e e))).mpr (Or.inl ⟨v_e e, hxi, rfl⟩)
      have hw_mem : (φ (u_e e) :: L_e e).getLast (List.cons_ne_nil _ _) ∈ S₂ j :=
        hprefix_sub j e hyj _ (List.getLast_mem (List.cons_ne_nil _ _))
      exact ⟨φ (v_e e), hx_mem,
        (φ (u_e e) :: L_e e).getLast (List.cons_ne_nil _ _), hw_mem, (hprefix_walk e).2.symm⟩

/-! ### Section 2: Subwall Configurations, Punctured Model Graph `G_punct`, and Finite Recipes -/

/-- Valid subwall parameter `(h', i, j)` inside an elementary wall of height `h`. -/
structure SubwallParam (h : ℕ) where
  h' : ℕ
  i : ℕ
  j : ℕ
  h2' : 2 ≤ h'
  he' : Even h'
  hle : h' ≤ h
  hi_even : Even i
  hj_even : Even j
  hi_le : i ≤ 2 * h - 2 * h'
  hj_le : j ≤ h - h'
  deriving DecidableEq

namespace SubwallParam

variable {h : ℕ} (s : SubwallParam h)

/-- Shift a branch-vertex index `u : Fin (elemWallNumVerts s.h')` into `Fin (elemWallNumVerts h)`. -/
def shiftVert (u : Fin (elemWallNumVerts s.h')) : Fin (elemWallNumVerts h) :=
  shiftElemWallVertIdx s.i s.j s.h' h (by have := s.h2'; omega) s.hle s.hi_le s.hj_le u

/-- The 4 corner indices of `s` in `Fin (elemWallNumVerts h)`. -/
def cornerIdx (m : Fin 4) : Fin (elemWallNumVerts h) :=
  s.shiftVert (elemWallCornerIdx s.h2' m)

/-- The `Finset` of all branch-vertex indices of `s` in `Fin (elemWallNumVerts h)`. -/
def vertSet : Finset (Fin (elemWallNumVerts h)) :=
  Finset.univ.image s.shiftVert

/-- The `Finset` of the 4 corner indices of `s` in `Fin (elemWallNumVerts h)`. -/
def cornerSet : Finset (Fin (elemWallNumVerts h)) :=
  Finset.univ.image s.cornerIdx

/-- The non-corner branch-vertex indices of `s` in `Fin (elemWallNumVerts h)`. -/
def nonCornerVertSet : Finset (Fin (elemWallNumVerts h)) :=
  s.vertSet \ s.cornerSet

theorem cornerIdx_mem_vertSet (m : Fin 4) : s.cornerIdx m ∈ s.vertSet :=
  Finset.mem_image_of_mem s.shiftVert (Finset.mem_univ _)

theorem cornerIdx_mem_cornerSet (m : Fin 4) : s.cornerIdx m ∈ s.cornerSet :=
  Finset.mem_image_of_mem s.cornerIdx (Finset.mem_univ _)

theorem cornerIdx_not_mem_nonCornerVertSet (m : Fin 4) :
    s.cornerIdx m ∉ s.nonCornerVertSet := by
  rw [nonCornerVertSet, Finset.mem_sdiff]
  intro h
  exact h.2 (s.cornerIdx_mem_cornerSet m)

theorem shiftVert_injective : Function.Injective s.shiftVert :=
  shiftElemWallVertIdx_injective (by have := s.h2'; omega) s.hle s.hi_le s.hj_le

theorem cornerIdx_injective : Function.Injective s.cornerIdx := by
  intro m₁ m₂ heq
  have hu := s.shiftVert_injective heq
  have hc := congrArg (elemWallVertCoord s.h') hu
  unfold elemWallCornerIdx at hc
  rw [elemWallVertCoord_elemWallCoordIdx, elemWallVertCoord_elemWallCoordIdx] at hc
  have h2' := s.h2'
  fin_cases m₁ <;> fin_cases m₂ <;> simp [GM13.elementaryWallCorner] at hc <;> try rfl
  all_goals omega

/-- No elementary wall edge of `s.h'` (`2 ≤ s.h'`) has both endpoints among the 4 corners of `s`. -/
theorem not_both_corners_of_elemWallEdge (k_sub : Fin (elemWallEdges s.h').length) :
    let e := (elemWallEdges s.h')[k_sub.1]'k_sub.2
    ¬ (s.shiftVert e.1 ∈ s.cornerSet ∧ s.shiftVert e.2 ∈ s.cornerSet) := by
  intro e ⟨h1, h2⟩
  rcases Finset.mem_image.mp h1 with ⟨m₁, _, hm₁⟩
  rcases Finset.mem_image.mp h2 with ⟨m₂, _, hm₂⟩
  have he1 : e.1 = elemWallCornerIdx s.h2' m₁ := s.shiftVert_injective hm₁.symm
  have he2 : e.2 = elemWallCornerIdx s.h2' m₂ := s.shiftVert_injective hm₂.symm
  have hadj := elemWallEdge_isElemWallEdgeCoord s.h' k_sub
  change isElemWallEdgeCoord (elemWallVertCoord s.h' e.1) (elemWallVertCoord s.h' e.2) = true at hadj
  rw [he1, he2] at hadj
  unfold elemWallCornerIdx at hadj
  rw [elemWallVertCoord_elemWallCoordIdx, elemWallVertCoord_elemWallCoordIdx] at hadj
  have h2' := s.h2'
  fin_cases m₁ <;> fin_cases m₂ <;>
    simp [GM13.elementaryWallCorner, isElemWallEdgeCoord] at hadj <;> omega

/-- The subwall of `W` specified by `s : SubwallParam h`. -/
def toSubwall {n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) : WallOfHeight s.h' G :=
  W.subwallAt s.i s.j s.h' (by have := s.h2'; omega) s.hle s.hi_even s.hj_even s.hi_le s.hj_le

theorem toSubwall_isSubwallOf {n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) :
    (s.toSubwall W).IsSubwallOf W :=
  ⟨s.h2', s.he', s.hle, s.i, s.j, s.hi_even, s.hj_even, s.hi_le, s.hj_le, rfl⟩

theorem toSubwall_cornerVert {n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) (m : Fin 4) :
    (s.toSubwall W).cornerVert s.h2' m = W.branchVert (s.cornerIdx m) := rfl

theorem branchVert_mem_toSubwall_vertexFinset_iff {n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) (u : Fin (elemWallNumVerts h)) :
    W.branchVert u ∈ (s.toSubwall W).vertexFinset ↔ u ∈ s.vertSet := by
  rw [(s.toSubwall W).mem_vertexFinset_iff]
  unfold vertSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨u', heq⟩ | ⟨k_sub, hvk⟩)
    · exact ⟨u', hW.1 heq⟩
    · obtain ⟨kW, _, _, hint, _⟩ :=
        W.exists_subdivPathVerts_subwallAt s.i s.j s.h' (by have := s.h2'; omega)
          s.hle s.hi_even s.hj_even s.hi_le s.hj_le k_sub
      unfold toSubwall at hvk
      rw [hint] at hvk
      exact False.elim (hW.2.2.1 kW u hvk)
  · rintro ⟨u', rfl⟩
    exact Or.inl ⟨u', rfl⟩

theorem internalVerts_mem_toSubwall_vertexFinset_endpoints {n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid)
    {k_e : Fin (elemWallEdges h).length} {v : Fin n} (hv : v ∈ W.internalVerts k_e)
    (hv_sub : v ∈ (s.toSubwall W).vertexFinset) :
    ((elemWallEdges h)[k_e.1]'k_e.2).1 ∈ s.nonCornerVertSet ∨
    ((elemWallEdges h)[k_e.1]'k_e.2).2 ∈ s.nonCornerVertSet := by
  rw [(s.toSubwall W).mem_vertexFinset_iff] at hv_sub
  rcases hv_sub with ⟨u', heq⟩ | ⟨k_sub, hvk⟩
  · exfalso
    exact hW.2.2.1 k_e (s.shiftVert u') (heq ▸ hv)
  · obtain ⟨kW, hopt, hget, _⟩ :=
      exists_shiftElemWallEdgeIdx (by have := s.h2'; omega) s.hle s.hi_even s.hj_even
        s.hi_le s.hj_le k_sub
    have hint : (s.toSubwall W).internalVerts k_sub = W.internalVerts kW := by
      unfold toSubwall WallOfHeight.subwallAt
      dsimp only
      rw [hopt]
    rw [hint] at hvk
    have hke_eq : k_e = kW := by
      by_contra hne
      exact List.disjoint_left.mp (hW.2.2.2 k_e kW hne) hv hvk
    subst hke_eq
    have h1_mem : ((elemWallEdges h)[k_e.1]'k_e.2).1 ∈ s.vertSet := by
      rw [hget]
      exact Finset.mem_image_of_mem s.shiftVert (Finset.mem_univ _)
    have h2_mem : ((elemWallEdges h)[k_e.1]'k_e.2).2 ∈ s.vertSet := by
      rw [hget]
      exact Finset.mem_image_of_mem s.shiftVert (Finset.mem_univ _)
    have hnot_both := s.not_both_corners_of_elemWallEdge k_sub
    dsimp only at hnot_both
    have hnot_both' :
        ¬ (((elemWallEdges h)[k_e.1]'k_e.2).1 ∈ s.cornerSet ∧
           ((elemWallEdges h)[k_e.1]'k_e.2).2 ∈ s.cornerSet) := by
      rw [hget]
      exact hnot_both
    by_cases hc1 : ((elemWallEdges h)[k_e.1]'k_e.2).1 ∈ s.cornerSet
    · right
      exact Finset.mem_sdiff.mpr ⟨h2_mem, fun hc2 => hnot_both' ⟨hc1, hc2⟩⟩
    · left
      exact Finset.mem_sdiff.mpr ⟨h1_mem, hc1⟩

/-- `s : SubwallParam h` matches `W_sub : WallOfHeight h_sub G` as a subwall of `W`. -/
def MatchesSubwall {n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (s : SubwallParam h) {h_sub : ℕ} (W_sub : WallOfHeight h_sub G) : Prop :=
  ∃ h_eq : h_sub = s.h', h_eq ▸ W_sub = s.toSubwall W

theorem MatchesSubwall.vertexFinset_eq {n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    {s : SubwallParam h} {h_sub : ℕ} {W_sub : WallOfHeight h_sub G}
    (hm : s.MatchesSubwall W W_sub) :
    W_sub.vertexFinset = (s.toSubwall W).vertexFinset := by
  rcases hm with ⟨rfl, rfl⟩
  rfl

theorem MatchesSubwall.cornerVert_eq {n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    {s : SubwallParam h} {h_sub : ℕ} {W_sub : WallOfHeight h_sub G}
    (hm : s.MatchesSubwall W W_sub) (h2 : 2 ≤ h_sub) (m : Fin 4) :
    W_sub.cornerVert h2 m = W.branchVert (s.cornerIdx m) := by
  rcases hm with ⟨rfl, rfl⟩
  rfl

theorem exists_matchesSubwall_of_isSubwallOf {n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    {h_sub : ℕ} {W_sub : WallOfHeight h_sub G} (hsub : W_sub.IsSubwallOf W) :
    ∃ s : SubwallParam h, s.MatchesSubwall W W_sub := by
  rcases hsub with ⟨h2', he', hle, i, j, hi_even, hj_even, hi_le, hj_le, hW_eq⟩
  exact ⟨⟨h_sub, i, j, h2', he', hle, hi_even, hj_even, hi_le, hj_le⟩, rfl, hW_eq⟩

end SubwallParam

/-- Punctured vertex set `V_punct cfg i_drop ⊆ Fin (elemWallNumVerts h)`: all branch-vertex indices
outside the non-corner vertices of `cfg b` for all `b ≠ i_drop`. -/
def V_punct {h k : ℕ} (cfg : Fin k → SubwallParam h) (i_drop : Fin k) :
    Finset (Fin (elemWallNumVerts h)) :=
  Finset.univ.filter (fun u => ∀ b : Fin k, b ≠ i_drop → u ∉ (cfg b).nonCornerVertSet)

/-- Elementary wall edges of height `h` whose endpoints both lie in `V_punct cfg i_drop`. -/
def activeWallEdges {h k : ℕ} (cfg : Fin k → SubwallParam h) (i_drop : Fin k) :
    Finset (Fin (elemWallEdges h).length) :=
  Finset.univ.filter (fun e =>
    ((elemWallEdges h)[e.1]'e.2).1 ∈ V_punct cfg i_drop ∧
    ((elemWallEdges h)[e.1]'e.2).2 ∈ V_punct cfg i_drop)

/-- Punctured model graph `G_punct cfg i_drop` on `Fin (elemWallNumVerts h)`, consisting of all
active wall edges in `activeWallEdges cfg i_drop` and the `2 * (k - 1)` cross edges
`((cfg b).cornerIdx 0, (cfg b).cornerIdx 2)` and `((cfg b).cornerIdx 1, (cfg b).cornerIdx 3)` for
`b ≠ i_drop`. -/
def G_punct {h k : ℕ} (cfg : Fin k → SubwallParam h) (i_drop : Fin k) :
    SimpleGraph (Fin (elemWallNumVerts h)) where
  Adj u v :=
    u ≠ v ∧
    ((∃ e ∈ activeWallEdges cfg i_drop,
        (elemWallEdges h)[e.1]'e.2 = (u, v) ∨ (elemWallEdges h)[e.1]'e.2 = (v, u)) ∨
     (∃ b : Fin k, b ≠ i_drop ∧
        ((u = (cfg b).cornerIdx 0 ∧ v = (cfg b).cornerIdx 2) ∨
         (u = (cfg b).cornerIdx 2 ∧ v = (cfg b).cornerIdx 0) ∨
         (u = (cfg b).cornerIdx 1 ∧ v = (cfg b).cornerIdx 3) ∨
         (u = (cfg b).cornerIdx 3 ∧ v = (cfg b).cornerIdx 1))))
  symm := ⟨fun _ _ ⟨hne, h⟩ => by
    refine ⟨hne.symm, ?_⟩
    rcases h with ⟨e, he, h1 | h2⟩ | ⟨b, hb, h1 | h2 | h3 | h4⟩
    · exact Or.inl ⟨e, he, Or.inr h1⟩
    · exact Or.inl ⟨e, he, Or.inl h2⟩
    · exact Or.inr ⟨b, hb, Or.inr (Or.inl ⟨h1.2, h1.1⟩)⟩
    · exact Or.inr ⟨b, hb, Or.inl ⟨h2.2, h2.1⟩⟩
    · exact Or.inr ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨h3.2, h3.1⟩))⟩
    · exact Or.inr ⟨b, hb, Or.inr (Or.inr (Or.inl ⟨h4.2, h4.1⟩))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A finite recipe specifying how to assemble a `K_p`-model in `x.G` from branch vertices of `x.W`,
internal vertices of `x.W`'s subdivision paths, and internal vertices of the cross paths `x.P a` and
`x.Q a`. -/
structure Recipe (p h k : ℕ) where
  branchCoords : Fin p → Finset (Fin (elemWallNumVerts h))
  wallEdges : Fin p → Finset (Fin (elemWallEdges h).length)
  crossP : Fin p → Finset (Fin k)
  crossQ : Fin p → Finset (Fin k)
  deriving DecidableEq, Fintype

/-- Materialize `rec : Recipe p h k` on input `x : Alg91Input p h k r` to obtain `p` vertex subsets
of `Fin x.n`. -/
def evalRecipe {p h k r : ℕ} (x : Alg91Input p h k r) (rec : Recipe p h k) (idx : Fin p) :
    Finset (Fin x.n) :=
  (rec.branchCoords idx).image x.W.branchVert ∪
  (rec.wallEdges idx).biUnion (fun e => (x.W.internalVerts e).toFinset) ∪
  (rec.crossP idx).biUnion (fun a => (((x.P a).drop 1).dropLast).toFinset) ∪
  (rec.crossQ idx).biUnion (fun a => (((x.Q a).drop 1).dropLast).toFinset)

/-- Build a `Recipe p h k` from a `K_p`-model `S_punct` in `G_punct cfg i_drop`. -/
def recipeOfPunctModel {p h k : ℕ} (cfg : Fin k → SubwallParam h) (i_drop : Fin k)
    (S_punct : Fin p → Finset (Fin (elemWallNumVerts h))) : Recipe p h k where
  branchCoords := S_punct
  wallEdges idx :=
    (activeWallEdges cfg i_drop).filter (fun e => ((elemWallEdges h)[e.1]'e.2).1 ∈ S_punct idx)
  crossP idx :=
    Finset.univ.filter (fun b => b ≠ i_drop ∧ (cfg b).cornerIdx 0 ∈ S_punct idx)
  crossQ idx :=
    Finset.univ.filter (fun b => b ≠ i_drop ∧ (cfg b).cornerIdx 1 ∈ S_punct idx)

theorem list_eq_head_cons_drop_one_dropLast_append_getLast {α : Type*}
    {L : List α} (hne : L ≠ []) (hdiff : L.head hne ≠ L.getLast hne) :
    L = L.head hne :: ((L.drop 1).dropLast ++ [L.getLast hne]) := by
  rcases L with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · exact False.elim (hne rfl)
  · exact False.elim (hdiff rfl)
  · have hys : y :: ys ≠ [] := List.cons_ne_nil y ys
    have hsplit : (y :: ys).dropLast ++ [(y :: ys).getLast hys] = y :: ys :=
      List.dropLast_append_getLast hys
    change x :: y :: ys = x :: ((y :: ys).dropLast ++ [(y :: ys).getLast hys])
    rw [hsplit]

theorem not_head_or_getLast_mem_drop_one_dropLast {α : Type*}
    {L : List α} (hne : L ≠ []) (hdiff : L.head hne ≠ L.getLast hne) (hnd : L.Nodup) :
    L.head hne ∉ (L.drop 1).dropLast ∧ L.getLast hne ∉ (L.drop 1).dropLast := by
  have heq := list_eq_head_cons_drop_one_dropLast_append_getLast hne hdiff
  have hnd' : (L.head hne :: ((L.drop 1).dropLast ++ [L.getLast hne])).Nodup := heq ▸ hnd
  rw [List.nodup_cons, List.nodup_append] at hnd'
  refine ⟨fun h => hnd'.1 (List.mem_append_left _ h), ?_⟩
  intro h
  exact hnd'.2.2.2 _ h _ (List.mem_singleton_self _) rfl

theorem mem_of_mem_drop_one_dropLast {α : Type*} {L : List α} {x : α}
    (hx : x ∈ (L.drop 1).dropLast) : x ∈ L :=
  List.mem_of_mem_drop (List.dropLast_subset _ hx)

/-- **Step 2 (`G_punct → x.G.toSimpleGraph`):**
If `S_punct` is a `K_p`-model in `G_punct cfg i_drop` with `S_punct idx ⊆ V_punct cfg i_drop` and
`cfg` matches `x.W_sub`, then `evalRecipe x (recipeOfPunctModel cfg i_drop S_punct)` is a `K_p`-model
in `x.G.toSimpleGraph`. -/
theorem isCliqueModel_evalRecipe_of_punctModel {p h k r : ℕ} (hr : 1 ≤ r)
    (x : Alg91Input p h k r)
    (cfg : Fin k → SubwallParam h) (i_drop : Fin k)
    (hmatch : ∀ b : Fin k, (cfg b).MatchesSubwall x.W (x.W_sub b))
    {S_punct : Fin p → Finset (Fin (elemWallNumVerts h))}
    (hS_sub : ∀ idx : Fin p, S_punct idx ⊆ V_punct cfg i_drop)
    (hK_punct : IsCliqueModel (G_punct cfg i_drop) p S_punct) :
    IsCliqueModel x.G.toSimpleGraph p (evalRecipe x (recipeOfPunctModel cfg i_drop S_punct)) := by
  have hW : x.W.IsValid := x.hW_valid.2.2
  have hdisj_vertSet : ∀ b₁ b₂ : Fin k, b₁ ≠ b₂ →
      Disjoint (cfg b₁).vertSet (cfg b₂).vertSet := by
    intro b₁ b₂ hne
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    have hv₁ : x.W.branchVert u ∈ (x.W_sub b₁).vertexFinset := by
      rw [(hmatch b₁).vertexFinset_eq]
      exact ((cfg b₁).branchVert_mem_toSubwall_vertexFinset_iff hW u).mpr hu₁
    have hv₂ : x.W.branchVert u ∈ (x.W_sub b₂).vertexFinset := by
      rw [(hmatch b₂).vertexFinset_eq]
      exact ((cfg b₂).branchVert_mem_toSubwall_vertexFinset_iff hW u).mpr hu₂
    have hdist := x.hdist b₁ b₂ hne (x.W.branchVert u) hv₁ (x.W.branchVert u) hv₂
    have hself : x.W.brickDist (x.W.branchVert u) (x.W.branchVert u) = 0 := by
      simp [WallOfHeight.brickDist]
    omega
  have hcorner_mem_Vpunct : ∀ (b : Fin k), b ≠ i_drop → ∀ m : Fin 4,
      (cfg b).cornerIdx m ∈ V_punct cfg i_drop := by
    intro b _ m
    unfold V_punct
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun b' _ hmem => ?_⟩
    by_cases hbb' : b = b'
    · subst hbb'
      exact (cfg b).cornerIdx_not_mem_nonCornerVertSet m hmem
    · have hu_b : (cfg b).cornerIdx m ∈ (cfg b).vertSet := (cfg b).cornerIdx_mem_vertSet m
      have hu_b' : (cfg b).cornerIdx m ∈ (cfg b').vertSet := Finset.sdiff_subset hmem
      exact Finset.disjoint_left.mp (hdisj_vertSet b b' hbb') hu_b hu_b'
  let ι := { e : Fin (elemWallEdges h).length // e ∈ activeWallEdges cfg i_drop } ⊕
    ({ b : Fin k // b ≠ i_drop } × Bool)
  let u_e : ι → Fin (elemWallNumVerts h)
    | Sum.inl ⟨e, _⟩ => ((elemWallEdges h)[e.1]'e.2).1
    | Sum.inr (⟨b, _⟩, false) => (cfg b).cornerIdx 0
    | Sum.inr (⟨b, _⟩, true) => (cfg b).cornerIdx 1
  let v_e : ι → Fin (elemWallNumVerts h)
    | Sum.inl ⟨e, _⟩ => ((elemWallEdges h)[e.1]'e.2).2
    | Sum.inr (⟨b, _⟩, false) => (cfg b).cornerIdx 2
    | Sum.inr (⟨b, _⟩, true) => (cfg b).cornerIdx 3
  let L_e : ι → List (Fin x.n)
    | Sum.inl ⟨e, _⟩ => x.W.internalVerts e
    | Sum.inr (⟨b, _⟩, false) => ((x.P b).drop 1).dropLast
    | Sum.inr (⟨b, _⟩, true) => ((x.Q b).drop 1).dropLast
  have heq_model :
      evalRecipe x (recipeOfPunctModel cfg i_drop S_punct) =
        liftSubdivisionModel S_punct x.W.branchVert u_e L_e := by
    funext idx
    ext w
    rw [mem_liftSubdivisionModel]
    unfold evalRecipe recipeOfPunctModel
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, List.mem_toFinset]
    constructor
    · rintro (((⟨u, hu, rfl⟩ | ⟨e, ⟨he_act, hu_S⟩, hw⟩) | ⟨b, ⟨hb_ne, hc0⟩, hw⟩) | ⟨b, ⟨hb_ne, hc1⟩, hw⟩)
      · exact Or.inl ⟨u, hu, rfl⟩
      · exact Or.inr ⟨Sum.inl ⟨e, he_act⟩, hu_S, hw⟩
      · exact Or.inr ⟨Sum.inr (⟨b, hb_ne⟩, false), hc0, hw⟩
      · exact Or.inr ⟨Sum.inr (⟨b, hb_ne⟩, true), hc1, hw⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨⟨e, he_act⟩ | ⟨⟨b, hb_ne⟩, false | true⟩, hu_S, hw⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨u, hu, rfl⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨e, ⟨he_act, hu_S⟩, hw⟩))
      · exact Or.inl (Or.inr ⟨b, ⟨hb_ne, hu_S⟩, hw⟩)
      · exact Or.inr ⟨b, ⟨hb_ne, hu_S⟩, hw⟩
  rw [heq_model]
  have hP_split : ∀ b : Fin k,
      x.P b = x.W.branchVert ((cfg b).cornerIdx 0) ::
        (((x.P b).drop 1).dropLast ++ [x.W.branchVert ((cfg b).cornerIdx 2)]) ∧
      x.W.branchVert ((cfg b).cornerIdx 0) ∉ ((x.P b).drop 1).dropLast ∧
      x.W.branchVert ((cfg b).cornerIdx 2) ∉ ((x.P b).drop 1).dropLast := by
    intro b
    have hcr := x.hcross b
    have hhead : (x.P b).head hcr.ne_nil₁ = x.W.branchVert ((cfg b).cornerIdx 0) := by
      rw [hcr.head₁, (hmatch b).cornerVert_eq (x.hsub b).1 0]
    have hlast : (x.P b).getLast hcr.ne_nil₁ = x.W.branchVert ((cfg b).cornerIdx 2) := by
      rw [hcr.getLast₁, (hmatch b).cornerVert_eq (x.hsub b).1 2]
    have hdiff : (x.P b).head hcr.ne_nil₁ ≠ (x.P b).getLast hcr.ne_nil₁ := by
      rw [hhead, hlast]
      exact fun heq => absurd ((cfg b).cornerIdx_injective (hW.1 heq)) (by decide)
    have h1 := list_eq_head_cons_drop_one_dropLast_append_getLast hcr.ne_nil₁ hdiff
    have h2 := not_head_or_getLast_mem_drop_one_dropLast hcr.ne_nil₁ hdiff hcr.nodup₁
    rw [hhead, hlast] at h1 h2
    exact ⟨h1, h2⟩
  have hQ_split : ∀ b : Fin k,
      x.Q b = x.W.branchVert ((cfg b).cornerIdx 1) ::
        (((x.Q b).drop 1).dropLast ++ [x.W.branchVert ((cfg b).cornerIdx 3)]) ∧
      x.W.branchVert ((cfg b).cornerIdx 1) ∉ ((x.Q b).drop 1).dropLast ∧
      x.W.branchVert ((cfg b).cornerIdx 3) ∉ ((x.Q b).drop 1).dropLast := by
    intro b
    have hcr := x.hcross b
    have hhead : (x.Q b).head hcr.ne_nil₂ = x.W.branchVert ((cfg b).cornerIdx 1) := by
      rw [hcr.head₂, (hmatch b).cornerVert_eq (x.hsub b).1 1]
    have hlast : (x.Q b).getLast hcr.ne_nil₂ = x.W.branchVert ((cfg b).cornerIdx 3) := by
      rw [hcr.getLast₂, (hmatch b).cornerVert_eq (x.hsub b).1 3]
    have hdiff : (x.Q b).head hcr.ne_nil₂ ≠ (x.Q b).getLast hcr.ne_nil₂ := by
      rw [hhead, hlast]
      exact fun heq => absurd ((cfg b).cornerIdx_injective (hW.1 heq)) (by decide)
    have h1 := list_eq_head_cons_drop_one_dropLast_append_getLast hcr.ne_nil₂ hdiff
    have h2 := not_head_or_getLast_mem_drop_one_dropLast hcr.ne_nil₂ hdiff hcr.nodup₂
    rw [hhead, hlast] at h1 h2
    exact ⟨h1, h2⟩
  have hact_disj_subwall : ∀ (e : Fin (elemWallEdges h).length),
      e ∈ activeWallEdges cfg i_drop → ∀ (b : Fin k), b ≠ i_drop →
      ∀ v ∈ x.W.internalVerts e, v ∉ (x.W_sub b).vertexFinset := by
    intro e he_act b hb_ne v hv hv_sub
    rw [(hmatch b).vertexFinset_eq] at hv_sub
    unfold activeWallEdges at he_act
    rw [Finset.mem_filter] at he_act
    obtain ⟨_, h1_vp, h2_vp⟩ := he_act
    unfold V_punct at h1_vp h2_vp
    rw [Finset.mem_filter] at h1_vp h2_vp
    rcases (cfg b).internalVerts_mem_toSubwall_vertexFinset_endpoints hW hv hv_sub with h1 | h2
    · exact h1_vp.2 b hb_ne h1
    · exact h2_vp.2 b hb_ne h2
  apply IsCliqueModel.lift_subdivision hK_punct hS_sub x.W.branchVert u_e v_e L_e
  · intro u₁ _ u₂ _ heq
    exact hW.1 heq
  · rintro (⟨e, he_act⟩ | ⟨⟨b, hb_ne⟩, false | true⟩)
    · exact (Finset.mem_filter.mp he_act).2.1
    · exact hcorner_mem_Vpunct b hb_ne 0
    · exact hcorner_mem_Vpunct b hb_ne 1
  · rintro (⟨e, _⟩ | ⟨⟨b, _⟩, false | true⟩)
    · rw [isSimpleGraphWalkList_iff_isSimpleWalkList]
      exact (hW.2.1 e).2
    · rw [isSimpleGraphWalkList_iff_isSimpleWalkList]
      dsimp [u_e, v_e, L_e]
      rw [← (hP_split b).1]
      exact (x.hcross b).isWalk₁
    · rw [isSimpleGraphWalkList_iff_isSimpleWalkList]
      dsimp [u_e, v_e, L_e]
      rw [← (hQ_split b).1]
      exact (x.hcross b).isWalk₂
  · rintro (⟨e, _⟩ | ⟨⟨b, hb_ne⟩, false | true⟩) u hu_vp hmem
    · exact hW.2.2.1 e u hmem
    · dsimp [L_e] at hmem
      have hvP : x.W.branchVert u ∈ x.P b := mem_of_mem_drop_one_dropLast hmem
      have hvW : x.W.branchVert u ∈ x.W.vertexFinset :=
        (x.W.mem_vertexFinset_iff _).mpr (Or.inl ⟨u, rfl⟩)
      have hv_sub : x.W.branchVert u ∈ (x.W_sub b).vertexFinset :=
        x.hinter b _ (Or.inl hvP) hvW
      rw [(hmatch b).vertexFinset_eq,
        (cfg b).branchVert_mem_toSubwall_vertexFinset_iff hW u] at hv_sub
      have hnot_nc : u ∉ (cfg b).nonCornerVertSet := (Finset.mem_filter.mp hu_vp).2 b hb_ne
      have hu_corner : u ∈ (cfg b).cornerSet := by
        by_contra hnc
        exact hnot_nc (Finset.mem_sdiff.mpr ⟨hv_sub, hnc⟩)
      rcases Finset.mem_image.mp hu_corner with ⟨m, _, rfl⟩
      fin_cases m
      · exact (hP_split b).2.1 hmem
      · have hmemQ : x.W.branchVert ((cfg b).cornerIdx 1) ∈ x.Q b := by
          rw [(hQ_split b).1]; exact List.mem_cons_self
        exact List.disjoint_left.mp (x.hcross b).disjoint hvP hmemQ
      · exact (hP_split b).2.2 hmem
      · have hmemQ : x.W.branchVert ((cfg b).cornerIdx 3) ∈ x.Q b := by
          rw [(hQ_split b).1]; simp
        exact List.disjoint_left.mp (x.hcross b).disjoint hvP hmemQ
    · dsimp [L_e] at hmem
      have hvQ : x.W.branchVert u ∈ x.Q b := mem_of_mem_drop_one_dropLast hmem
      have hvW : x.W.branchVert u ∈ x.W.vertexFinset :=
        (x.W.mem_vertexFinset_iff _).mpr (Or.inl ⟨u, rfl⟩)
      have hv_sub : x.W.branchVert u ∈ (x.W_sub b).vertexFinset :=
        x.hinter b _ (Or.inr hvQ) hvW
      rw [(hmatch b).vertexFinset_eq,
        (cfg b).branchVert_mem_toSubwall_vertexFinset_iff hW u] at hv_sub
      have hnot_nc : u ∉ (cfg b).nonCornerVertSet := (Finset.mem_filter.mp hu_vp).2 b hb_ne
      have hu_corner : u ∈ (cfg b).cornerSet := by
        by_contra hnc
        exact hnot_nc (Finset.mem_sdiff.mpr ⟨hv_sub, hnc⟩)
      rcases Finset.mem_image.mp hu_corner with ⟨m, _, rfl⟩
      fin_cases m
      · have hmemP : x.W.branchVert ((cfg b).cornerIdx 0) ∈ x.P b := by
          rw [(hP_split b).1]; exact List.mem_cons_self
        exact List.disjoint_left.mp (x.hcross b).disjoint hmemP hvQ
      · exact (hQ_split b).2.1 hmem
      · have hmemP : x.W.branchVert ((cfg b).cornerIdx 2) ∈ x.P b := by
          rw [(hP_split b).1]; simp
        exact List.disjoint_left.mp (x.hcross b).disjoint hmemP hvQ
      · exact (hQ_split b).2.2 hmem
  · intro e₁ e₂ hne
    rw [List.disjoint_left]
    intro v hv₁ hv₂
    rcases e₁ with ⟨k₁, hk₁⟩ | ⟨⟨b₁, hb₁⟩, false | true⟩ <;>
    rcases e₂ with ⟨k₂, hk₂⟩ | ⟨⟨b₂, hb₂⟩, false | true⟩
    · have hk_ne : k₁ ≠ k₂ := fun heq => hne (by subst heq; rfl)
      exact List.disjoint_left.mp (hW.2.2.2 k₁ k₂ hk_ne) hv₁ hv₂
    · have hvW : v ∈ x.W.vertexFinset :=
        (x.W.mem_vertexFinset_iff v).mpr (Or.inr ⟨k₁, hv₁⟩)
      have hvP : v ∈ x.P b₂ := mem_of_mem_drop_one_dropLast hv₂
      exact hact_disj_subwall k₁ hk₁ b₂ hb₂ v hv₁ (x.hinter b₂ v (Or.inl hvP) hvW)
    · have hvW : v ∈ x.W.vertexFinset :=
        (x.W.mem_vertexFinset_iff v).mpr (Or.inr ⟨k₁, hv₁⟩)
      have hvQ : v ∈ x.Q b₂ := mem_of_mem_drop_one_dropLast hv₂
      exact hact_disj_subwall k₁ hk₁ b₂ hb₂ v hv₁ (x.hinter b₂ v (Or.inr hvQ) hvW)
    · have hvW : v ∈ x.W.vertexFinset :=
        (x.W.mem_vertexFinset_iff v).mpr (Or.inr ⟨k₂, hv₂⟩)
      have hvP : v ∈ x.P b₁ := mem_of_mem_drop_one_dropLast hv₁
      exact hact_disj_subwall k₂ hk₂ b₁ hb₁ v hv₂ (x.hinter b₁ v (Or.inl hvP) hvW)
    · have hb_ne : b₁ ≠ b₂ := fun heq => hne (by subst heq; rfl)
      exact x.hdisj b₁ b₂ hb_ne v
        ⟨Or.inl (mem_of_mem_drop_one_dropLast hv₁), Or.inl (mem_of_mem_drop_one_dropLast hv₂)⟩
    · by_cases hb_eq : b₁ = b₂
      · subst hb_eq
        exact List.disjoint_left.mp (x.hcross b₁).disjoint
          (mem_of_mem_drop_one_dropLast hv₁) (mem_of_mem_drop_one_dropLast hv₂)
      · exact x.hdisj b₁ b₂ hb_eq v
          ⟨Or.inl (mem_of_mem_drop_one_dropLast hv₁), Or.inr (mem_of_mem_drop_one_dropLast hv₂)⟩
    · have hvW : v ∈ x.W.vertexFinset :=
        (x.W.mem_vertexFinset_iff v).mpr (Or.inr ⟨k₂, hv₂⟩)
      have hvQ : v ∈ x.Q b₁ := mem_of_mem_drop_one_dropLast hv₁
      exact hact_disj_subwall k₂ hk₂ b₁ hb₁ v hv₂ (x.hinter b₁ v (Or.inr hvQ) hvW)
    · by_cases hb_eq : b₁ = b₂
      · subst hb_eq
        exact List.disjoint_left.mp (x.hcross b₁).disjoint
          (mem_of_mem_drop_one_dropLast hv₂) (mem_of_mem_drop_one_dropLast hv₁)
      · exact x.hdisj b₁ b₂ hb_eq v
          ⟨Or.inr (mem_of_mem_drop_one_dropLast hv₁), Or.inl (mem_of_mem_drop_one_dropLast hv₂)⟩
    · have hb_ne : b₁ ≠ b₂ := fun heq => hne (by subst heq; rfl)
      exact x.hdisj b₁ b₂ hb_ne v
        ⟨Or.inr (mem_of_mem_drop_one_dropLast hv₁), Or.inr (mem_of_mem_drop_one_dropLast hv₂)⟩
  · intro u₁ _ u₂ _ ⟨_, hadj⟩
    rcases hadj with ⟨e, he_act, h1 | h2⟩ | ⟨b, hb_ne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨Sum.inl ⟨e, he_act⟩, Or.inl ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩⟩
    · exact Or.inr ⟨Sum.inl ⟨e, he_act⟩, Or.inr ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩⟩
    · exact Or.inr ⟨Sum.inr (⟨b, hb_ne⟩, false), Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨Sum.inr (⟨b, hb_ne⟩, false), Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨Sum.inr (⟨b, hb_ne⟩, true), Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨Sum.inr (⟨b, hb_ne⟩, true), Or.inr ⟨rfl, rfl⟩⟩

/-! ### Section 3: Clean Elementary Wall `W_clean` and Finite Recipe Universe `allRecipes` -/

/-- The unsubdivided elementary wall `MultiDigraph` of height `h` on `Fin (elemWallNumVerts h)`. -/
def G_elem (h : ℕ) : MultiDigraph (elemWallNumVerts h) where
  edgeMult u v :=
    if isElemWallEdgeCoord (elemWallVertCoord h u) (elemWallVertCoord h v) then 1 else 0

/-- The unsubdivided `WallOfHeight h (G_elem h)` with `branchVert := id` and empty `internalVerts`. -/
def W_clean (h : ℕ) : WallOfHeight h (G_elem h) where
  branchVert := id
  internalVerts := fun _ => []

theorem W_clean_isValid (h : ℕ) : (W_clean h).IsValid := by
  refine ⟨Function.injective_id, fun k => ?_, fun _ _ h => List.not_mem_nil h,
    fun _ _ _ => List.disjoint_nil_left _⟩
  let e := (elemWallEdges h)[k.1]'k.2
  have hadj_coord : isElemWallEdgeCoord (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) = true :=
    elemWallEdge_isElemWallEdgeCoord h k
  have hne : e.1 ≠ e.2 := by
    intro heq
    have hadj := elemWallEdge_elementaryWallAdj h k
    change GM13.elementaryWallAdj h (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) at hadj
    rw [heq] at hadj
    exact GM13.elementaryWallAdj_irrefl _ hadj
  have hadj_G : (G_elem h).toSimpleGraph.Adj e.1 e.2 := by
    rw [MultiDigraph.toSimpleGraph_adj]
    refine ⟨hne, Or.inl ?_⟩
    simp [G_elem, hadj_coord]
  change ([e.1, e.2] : List (Fin (elemWallNumVerts h))).Nodup ∧
    WallOfHeight.IsSimpleWalkList (G_elem h) [e.1, e.2]
  exact ⟨List.nodup_cons.mpr ⟨by simp [hne], List.nodup_singleton _⟩, ⟨hadj_G, trivial⟩⟩

theorem W_clean_subwall_vertexFinset_eq {h : ℕ} (s : SubwallParam h) :
    (s.toSubwall (W_clean h)).vertexFinset = s.vertSet := by
  ext u
  have h := s.branchVert_mem_toSubwall_vertexFinset_iff (W_clean_isValid h) u
  simpa [W_clean] using h

theorem brickDist_branchVert_eq_W_clean {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) (u v : Fin (elemWallNumVerts h)) :
    W.brickDist (W.branchVert u) (W.branchVert v) = (W_clean h).brickDist u v := by
  have hcu : (W_clean h).vertCell u = elemWallVertCell h u :=
    (W_clean h).vertCell_branchVert_s9 (W_clean_isValid h) u
  have hcv : (W_clean h).vertCell v = elemWallVertCell h v :=
    (W_clean h).vertCell_branchVert_s9 (W_clean_isValid h) v
  unfold WallOfHeight.brickDist
  rw [W.vertCell_branchVert_s9 hW u, W.vertCell_branchVert_s9 hW v, hcu, hcv]
  simp only [(Function.Injective.eq_iff hW.1)]

theorem SubwallParam.ext {h : ℕ} {s₁ s₂ : SubwallParam h}
    (hh' : s₁.h' = s₂.h') (hi : s₁.i = s₂.i) (hj : s₁.j = s₂.j) : s₁ = s₂ := by
  cases s₁; cases s₂
  dsimp at hh' hi hj
  subst hh' hi hj
  rfl

theorem SubwallParam.elemWallVertCoord_cornerIdx {h : ℕ} (s : SubwallParam h) (m : Fin 4) :
    elemWallVertCoord h (s.cornerIdx m) =
      GM13.wallShift s.i s.j (GM13.elementaryWallCorner s.h' m) := by
  unfold SubwallParam.cornerIdx SubwallParam.shiftVert elemWallCornerIdx
  rw [elemWallVertCoord_shiftElemWallVertIdx, elemWallVertCoord_elemWallCoordIdx]

theorem SubwallParam.eq_of_h'_eq_of_cornerIdx_zero_eq {h : ℕ} {s₁ s₂ : SubwallParam h}
    (hh' : s₁.h' = s₂.h') (hc : s₁.cornerIdx 0 = s₂.cornerIdx 0) : s₁ = s₂ := by
  have hcoord := congrArg (elemWallVertCoord h) hc
  rw [s₁.elemWallVertCoord_cornerIdx 0, s₂.elemWallVertCoord_cornerIdx 0] at hcoord
  unfold GM13.wallShift GM13.elementaryWallCorner at hcoord
  dsimp at hcoord
  injection hcoord with hi hj
  exact SubwallParam.ext hh' (by omega) (by omega)

/-- Finite enumeration of all `SubwallParam h` values for a given `h : ℕ`. -/
def allSubwallParams (h : ℕ) : List (SubwallParam h) :=
  (List.range (h + 1)).flatMap fun h' =>
    (List.range (2 * h + 1)).flatMap fun i =>
      (List.range (h + 1)).filterMap fun j =>
        if hcond : 2 ≤ h' ∧ Even h' ∧ h' ≤ h ∧ Even i ∧ Even j ∧
            i ≤ 2 * h - 2 * h' ∧ j ≤ h - h' then
          some ⟨h', i, j, hcond.1, hcond.2.1, hcond.2.2.1,
            hcond.2.2.2.1, hcond.2.2.2.2.1, hcond.2.2.2.2.2.1, hcond.2.2.2.2.2.2⟩
        else
          none

theorem mem_allSubwallParams {h : ℕ} (s : SubwallParam h) :
    s ∈ allSubwallParams h := by
  unfold allSubwallParams
  rw [List.mem_flatMap]
  refine ⟨s.h', List.mem_range.mpr (by have := s.hle; omega), ?_⟩
  rw [List.mem_flatMap]
  refine ⟨s.i, List.mem_range.mpr (by have := s.hi_le; omega), ?_⟩
  rw [List.mem_filterMap]
  refine ⟨s.j, List.mem_range.mpr (by have := s.hj_le; omega), ?_⟩
  have hcond : 2 ≤ s.h' ∧ Even s.h' ∧ s.h' ≤ h ∧ Even s.i ∧ Even s.j ∧
      s.i ≤ 2 * h - 2 * s.h' ∧ s.j ≤ h - s.h' :=
    ⟨s.h2', s.he', s.hle, s.hi_even, s.hj_even, s.hi_le, s.hj_le⟩
  simp [hcond]

instance instFintypeSubwallParam (h : ℕ) : Fintype (SubwallParam h) where
  elems := (allSubwallParams h).toFinset
  complete s := List.mem_toFinset.mpr (mem_allSubwallParams s)

/-- Enumeration of all `Fin k → SubwallParam h` configurations. -/
noncomputable def allSubwallConfigs (h k : ℕ) : List (Fin k → SubwallParam h) :=
  (Finset.univ : Finset (Fin k → SubwallParam h)).toList

theorem mem_allSubwallConfigs (h k : ℕ) (cfg : Fin k → SubwallParam h) :
    cfg ∈ allSubwallConfigs h k :=
  Finset.mem_toList.mpr (Finset.mem_univ cfg)

/-- Enumeration of all `Recipe p h k` values via `Fintype.elems`. -/
noncomputable def allRecipes (p h k : ℕ) : List (Recipe p h k) :=
  (Finset.univ : Finset (Recipe p h k)).toList

theorem mem_allRecipes (p h k : ℕ) (rec : Recipe p h k) :
    rec ∈ allRecipes p h k := by
  unfold allRecipes
  exact Finset.mem_toList.mpr (Finset.mem_univ rec)

end GraphMinor.Compute
