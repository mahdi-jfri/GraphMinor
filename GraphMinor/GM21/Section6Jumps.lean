module

public import GraphMinor.GM21.Section7Jumps
public import GraphMinor.GM21.Section6Exhaustive
import GraphMinor.GM21.LinkagePaths

/-!
# Graph Minors XXI, Section 6: the `Σ`-jumps of an exhaustive linkage

Graph Minors XXI, Section 6 (page 24 of the preprint): "If $L$ is exhaustive, then every edge
of $\Gamma$ is in a unique $\Sigma$-jump, and any two $\Sigma$-jumps have no common vertices except
possibly one end."

We prove these two facts for a linkage `K` (in the application `K = Γ`) and a set `B` of vertices
(in the application the vertices of `Γ` in `bd(Σ)`) such that every vertex of `K` outside `B` has
two edges in `K`. The jumps are the members of `jumpSet K B`: paths of `K` with two distinct ends
in `B` and no other vertex in `B`.

* A vertex of a jump outside `B` is not an end of the jump, so the jump uses both of its edges
  (`incidentEdges_jump_eq`).
* Two jumps with a common edge are equal (`jump_eq_of_edge`): walking along the first jump from
  the common edge, we never leave the second, since we only pass through vertices outside `B`.
* Two jumps with a common vertex outside `B` share its two edges, so they are equal
  (`jump_eq_of_vertex`). Two different jumps with two common vertices would together have no
  vertex of degree 1, which a linkage forbids (`jump_eq_of_two_vertices`).
* Every edge of `K` is in a jump (`exists_jump_of_edge`): in the path of `K` through the edge, take
  the part between the nearest vertices of `B` on either side.

Finally `sigmaJumps_eq_jumpSet` identifies the `Σ`-jumps of a presentation with `jumpSet`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Hypergraph GraphMinor.GM10

universe u v w

section jumps

variable {α : Type u} {β : Type v} {G K J J' : Hypergraph α β} {B : Set α}

/-- The terminals of a jump lie in `B`. -/
theorem terminals_subset_of_mem_jumpSet (hJ : J ∈ jumpSet K B) : terminals J ⊆ B := by
  obtain ⟨-, -, a, ha, b, hb, -, hterm, -⟩ := hJ
  rw [hterm]
  rintro x (rfl | rfl) <;> assumption

/-- A vertex of a jump that lies in `B` is a terminal of the jump. -/
theorem mem_terminals_of_mem_jumpSet (hJ : J ∈ jumpSet K B) {x : α} (hx : x ∈ J.vertexSet)
    (hxB : x ∈ B) : x ∈ terminals J := by
  obtain ⟨-, -, a, -, b, -, -, hterm, hB⟩ := hJ
  rw [hterm]
  rcases hB x hx hxB with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A jump has an edge: its two ends are distinct and joined in the jump. -/
theorem edgeSet_nonempty_of_mem_jumpSet (hJ : J ∈ jumpSet K B) : J.edgeSet.Nonempty := by
  obtain ⟨-, hJp, a, -, b, -, hab, hterm, -⟩ := hJ
  have ha : a ∈ J.vertexSet := (show a ∈ terminals J from hterm ▸ Or.inl rfl).1
  have hb : b ∈ J.vertexSet := (show b ∈ terminals J from hterm ▸ Or.inr rfl).1
  obtain ⟨p⟩ := hJp.2.2.1 a ha b hb
  cases p with
  | nil => exact absurd rfl hab
  | cons hadj _ =>
    obtain ⟨-, e, he, -⟩ := hadj
    exact ⟨e, J.edge_mem_of_inc he⟩

/-- Every vertex of a jump is an end of an edge of the jump. -/
theorem exists_inc_of_mem_jumpSet (hJ : J ∈ jumpSet K B) {x : α} (hx : x ∈ J.vertexSet) :
    ∃ e ∈ J.edgeSet, J.Inc e x := by
  obtain ⟨e, he⟩ := edgeSet_nonempty_of_mem_jumpSet hJ
  have hJp : IsPathGraph J := hJ.2.1
  obtain ⟨z, hz⟩ := (hJp.1 e he).1
  by_cases hxz : x = z
  · exact ⟨e, he, hxz ▸ hz⟩
  · obtain ⟨p⟩ := hJp.2.2.1 x hx z (J.vertex_mem_of_inc hz)
    cases p with
    | nil => exact absurd rfl hxz
    | cons hadj _ =>
      obtain ⟨-, f, hf, -⟩ := hadj
      exact ⟨f, J.edge_mem_of_inc hf, hf⟩

/-- An edge of a subgraph `J ≤ K` has the same ends in `J` as in `K`. -/
private theorem inc_iff_of_mem_jumpSet (hJ : J ∈ jumpSet K B) {e : β} (he : e ∈ J.edgeSet)
    {x : α} : J.Inc e x ↔ K.Inc e x :=
  inc_iff_of_le hJ.1 he

variable (hK : IsLinkage G K) (hdeg : ∀ y ∈ K.vertexSet, y ∉ B → (incidentEdges K y).ncard = 2)
include hK hdeg

omit hK in
/-- A vertex `x` of a jump `J` outside `B` is not an end of `J`, so `J` contains both edges of `K`
at `x`. -/
theorem incidentEdges_jump_eq (hJ : J ∈ jumpSet K B) {x : α} (hx : x ∈ J.vertexSet)
    (hxB : x ∉ B) : incidentEdges J x = incidentEdges K x := by
  have hJK : J ≤ K := hJ.1
  have hJp : IsPathGraph J := hJ.2.1
  have hnt : x ∉ terminals J := fun h => hxB (terminals_subset_of_mem_jumpSet hJ h)
  have h2 : 2 ≤ (incidentEdges J x).ncard := by
    by_contra hlt
    exact hnt ⟨hx, by rw [vertexDegree_eq_ncard_incidentEdges hJp.2.2.2.1]; omega⟩
  have hfin : (incidentEdges K x).Finite := K.edgeSet_finite.subset fun e he => he.1
  exact eq_of_subset_of_ncard_le (incidentEdges_subset_of_le hJK x)
    (by rw [hdeg x (hJK.vertexSet_subset hx) hxB]; exact h2) hfin

omit hK in
/-- No vertex of a jump `J` is an end, in `J`, both of an edge of another jump `J'` and of an edge
of `J` that is not in `J'`. -/
private theorem not_inc_both (hJ : J ∈ jumpSet K B) (hJ' : J' ∈ jumpSet K B) {z : α} {f g : β}
    (hf : f ∈ J.edgeSet) (hf' : f ∈ J'.edgeSet) (hg : g ∈ J.edgeSet) (hg' : g ∉ J'.edgeSet)
    (hfz : J.Inc f z) (hgz : J.Inc g z) : False := by
  have hzJ : z ∈ J.vertexSet := J.vertex_mem_of_inc hfz
  by_cases hzB : z ∈ B
  · -- `z` is a terminal of `J`, so it has only one edge in `J`.
    have hzt := mem_terminals_of_mem_jumpSet hJ hzJ hzB
    have hJp : IsPathGraph J := hJ.2.1
    have h1 : (incidentEdges J z).ncard ≤ 1 := by
      have := hzt.2
      rwa [vertexDegree_eq_ncard_incidentEdges hJp.2.2.2.1] at this
    have hfg : f ≠ g := fun h => hg' (h ▸ hf')
    have hsub : ({f, g} : Set β) ⊆ incidentEdges J z := by
      rintro e (rfl | rfl)
      · exact ⟨hf, hfz⟩
      · exact ⟨hg, hgz⟩
    have := ncard_le_ncard hsub (J.edgeSet_finite.subset fun e he => he.1)
    rw [ncard_pair hfg] at this
    omega
  · -- `z` is outside `B`, so both jumps contain both edges of `K` at `z`.
    have hfzK : K.Inc f z := (inc_iff_of_mem_jumpSet hJ hf).1 hfz
    have hfz' : J'.Inc f z := (inc_iff_of_mem_jumpSet hJ' hf').2 hfzK
    have hzJ' : z ∈ J'.vertexSet := J'.vertex_mem_of_inc hfz'
    have hgK : g ∈ incidentEdges K z := by
      rw [← incidentEdges_jump_eq hdeg hJ hzJ hzB]
      exact ⟨hg, hgz⟩
    rw [← incidentEdges_jump_eq hdeg hJ' hzJ' hzB] at hgK
    exact hg' hgK.1

omit hK in
/-- If two jumps have a common edge, every edge of the first is an edge of the second. -/
theorem edgeSet_subset_of_jump_edge (hJ : J ∈ jumpSet K B) (hJ' : J' ∈ jumpSet K B) {f : β}
    (hf : f ∈ J.edgeSet) (hf' : f ∈ J'.edgeSet) : J.edgeSet ⊆ J'.edgeSet := by
  intro g hg
  by_contra hg'
  have hJp : IsPathGraph J := hJ.2.1
  obtain ⟨x, hx⟩ := (hJp.1 f hf).1
  obtain ⟨y, hy⟩ := (hJp.1 g hg).1
  obtain ⟨p⟩ := hJp.2.2.1 x (J.vertex_mem_of_inc hx) y (J.vertex_mem_of_inc hy)
  -- Walk from `x` to `y`; every vertex on the way is an end of an edge common to both jumps.
  have key : ∀ (a b : α) (p : J.skeleton.Walk a b), J.Inc g b →
      (∃ f₀ ∈ J.edgeSet, f₀ ∈ J'.edgeSet ∧ J.Inc f₀ a) → False := by
    intro a b p
    induction p with
    | nil =>
      rintro hgb ⟨f₀, hf₀, hf₀', hinc⟩
      exact not_inc_both hdeg hJ hJ' hf₀ hf₀' hg hg' hinc hgb
    | cons hadj _ ih =>
      rintro hgb ⟨f₀, hf₀, hf₀', hinc⟩
      obtain ⟨-, h, ha, hb⟩ := hadj
      have hh : h ∈ J.edgeSet := J.edge_mem_of_inc ha
      by_cases hh' : h ∈ J'.edgeSet
      · exact ih hgb ⟨h, hh, hh', hb⟩
      · exact not_inc_both hdeg hJ hJ' hf₀ hf₀' hh hh' hinc ha
  exact key x y p hy ⟨f, hf, hf', hx⟩

omit hK in
/-- Two jumps with a common edge are equal: "every edge of $\Gamma$ is in a unique
$\Sigma$-jump". -/
theorem jump_eq_of_edge (hJ : J ∈ jumpSet K B) (hJ' : J' ∈ jumpSet K B) {f : β}
    (hf : f ∈ J.edgeSet) (hf' : f ∈ J'.edgeSet) : J = J' := by
  have hE : J.edgeSet = J'.edgeSet :=
    (edgeSet_subset_of_jump_edge hdeg hJ hJ' hf hf').antisymm
      (edgeSet_subset_of_jump_edge hdeg hJ' hJ hf' hf)
  have hV : ∀ {J₁ J₂ : Hypergraph α β}, J₁ ∈ jumpSet K B → J₂ ∈ jumpSet K B →
      J₁.edgeSet = J₂.edgeSet → J₁.vertexSet ⊆ J₂.vertexSet := by
    intro J₁ J₂ h₁ h₂ hE₁₂ x hx
    obtain ⟨e, he, hinc⟩ := exists_inc_of_mem_jumpSet h₁ hx
    have he₂ : e ∈ J₂.edgeSet := hE₁₂ ▸ he
    exact J₂.vertex_mem_of_inc
      ((inc_iff_of_mem_jumpSet h₂ he₂).2 ((inc_iff_of_mem_jumpSet h₁ he).1 hinc))
  exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq hJ.1 hJ'.1
    ((hV hJ hJ' hE).antisymm (hV hJ' hJ hE.symm)) hE

omit hK in
/-- Two jumps with a common vertex outside `B` are equal. -/
theorem jump_eq_of_vertex (hJ : J ∈ jumpSet K B) (hJ' : J' ∈ jumpSet K B) {x : α}
    (hx : x ∈ J.vertexSet) (hx' : x ∈ J'.vertexSet) (hxB : x ∉ B) : J = J' := by
  have h1 := incidentEdges_jump_eq hdeg hJ hx hxB
  have h2 := incidentEdges_jump_eq hdeg hJ' hx' hxB
  have hne : (incidentEdges K x).Nonempty := by
    apply nonempty_of_ncard_ne_zero
    rw [hdeg x (hJ.1.vertexSet_subset hx) hxB]
    omega
  obtain ⟨f, hf⟩ := hne
  have hfJ : f ∈ incidentEdges J x := h1 ▸ hf
  have hfJ' : f ∈ incidentEdges J' x := h2 ▸ hf
  exact jump_eq_of_edge hdeg hJ hJ' hfJ.1 hfJ'.1

/-- "any two $\Sigma$-jumps have no common vertices except possibly one end": two jumps with two
distinct common vertices are equal. -/
theorem jump_eq_of_two_vertices (hJ : J ∈ jumpSet K B) (hJ' : J' ∈ jumpSet K B) {x y : α}
    (hxy : x ≠ y) (hx : x ∈ J.vertexSet) (hx' : x ∈ J'.vertexSet) (hy : y ∈ J.vertexSet)
    (hy' : y ∈ J'.vertexSet) : J = J' := by
  by_cases hxB : x ∉ B
  · exact jump_eq_of_vertex hdeg hJ hJ' hx hx' hxB
  by_cases hyB : y ∉ B
  · exact jump_eq_of_vertex hdeg hJ hJ' hy hy' hyB
  push Not at hxB hyB
  by_contra hne
  -- The ends of `J` and of `J'` are `x` and `y`.
  have hends : ∀ {J₁ : Hypergraph α β}, J₁ ∈ jumpSet K B → x ∈ J₁.vertexSet → y ∈ J₁.vertexSet →
      ∀ z ∈ J₁.vertexSet, z ∈ B → z = x ∨ z = y := by
    intro J₁ h₁ hx₁ hy₁ z hz hzB
    obtain ⟨-, -, a, -, b, -, -, -, hB⟩ := h₁
    rcases hB x hx₁ hxB with rfl | rfl <;> rcases hB y hy₁ hyB with rfl | rfl
    · exact absurd rfl hxy
    · exact hB z hz hzB
    · exact (hB z hz hzB).symm
    · exact absurd rfl hxy
  -- In `J ∪ J'` every vertex has two edges, which is impossible in a linkage.
  have hHK : J ∪ J' ≤ K := GM10.union_le hJ.1 hJ'.1
  have hHE : (J ∪ J').edgeSet.Nonempty :=
    (edgeSet_nonempty_of_mem_jumpSet hJ).mono subset_union_left
  obtain ⟨z, hz, hz1⟩ := hK.exists_deg_one_of_le hHK hHE
  have hfinH : (incidentEdges (J ∪ J') z).Finite :=
    (J ∪ J').edgeSet_finite.subset fun e he => he.1
  have hsubJ : incidentEdges J z ⊆ incidentEdges (J ∪ J') z :=
    fun e he => ⟨Or.inl he.1, Or.inl he.2⟩
  have hsubJ' : incidentEdges J' z ⊆ incidentEdges (J ∪ J') z :=
    fun e he => ⟨Or.inr he.1, Or.inr he.2⟩
  by_cases hzB : z ∈ B
  · -- `z` is a common end; its edges in `J` and in `J'` differ.
    have hzJJ' : z ∈ J.vertexSet ∧ z ∈ J'.vertexSet := by
      rcases hz with hz | hz
      · rcases hends hJ hx hy z hz hzB with rfl | rfl
        · exact ⟨hx, hx'⟩
        · exact ⟨hy, hy'⟩
      · rcases hends hJ' hx' hy' z hz hzB with rfl | rfl
        · exact ⟨hx, hx'⟩
        · exact ⟨hy, hy'⟩
    obtain ⟨g, hg, hgz⟩ := exists_inc_of_mem_jumpSet hJ hzJJ'.1
    obtain ⟨g', hg', hgz'⟩ := exists_inc_of_mem_jumpSet hJ' hzJJ'.2
    have hgg : g ≠ g' := by
      rintro rfl
      exact hne (jump_eq_of_edge hdeg hJ hJ' hg hg')
    have hsub : ({g, g'} : Set β) ⊆ incidentEdges (J ∪ J') z := by
      rintro e (rfl | rfl)
      · exact hsubJ ⟨hg, hgz⟩
      · exact hsubJ' ⟨hg', hgz'⟩
    have := ncard_le_ncard hsub hfinH
    rw [ncard_pair hgg] at this
    omega
  · -- `z` is outside `B`, so it has two edges in the jump containing it.
    have h2 : 2 ≤ (incidentEdges (J ∪ J') z).ncard := by
      rcases hz with hz | hz
      · have := ncard_le_ncard hsubJ hfinH
        rw [incidentEdges_jump_eq hdeg hJ hz hzB, hdeg z (hJ.1.vertexSet_subset hz) hzB] at this
        exact this
      · have := ncard_le_ncard hsubJ' hfinH
        rw [incidentEdges_jump_eq hdeg hJ' hz hzB,
          hdeg z (hJ'.1.vertexSet_subset hz) hzB] at this
        exact this
    omega

omit hK hdeg in
/-- The ends of a jump, as a set. -/
theorem terminals_eq_of_mem_jumpSet (hJ : J ∈ jumpSet K B) :
    ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ terminals J = {a, b} ∧ a ∈ J.vertexSet ∧ b ∈ J.vertexSet := by
  obtain ⟨-, -, a, ha, b, hb, hab, hterm, -⟩ := hJ
  exact ⟨a, ha, b, hb, hab, hterm, (show a ∈ terminals J from hterm ▸ Or.inl rfl).1,
    (show b ∈ terminals J from hterm ▸ Or.inr rfl).1⟩

/-- Two jumps with the same ends are equal. -/
theorem jump_eq_of_terminals_eq (hJ : J ∈ jumpSet K B) (hJ' : J' ∈ jumpSet K B)
    (h : terminals J = terminals J') : J = J' := by
  obtain ⟨a, -, b, -, hab, hterm, ha, hb⟩ := terminals_eq_of_mem_jumpSet hJ
  have ha' : a ∈ J'.vertexSet := (show a ∈ terminals J' from h ▸ hterm ▸ Or.inl rfl).1
  have hb' : b ∈ J'.vertexSet := (show b ∈ terminals J' from h ▸ hterm ▸ Or.inr rfl).1
  exact jump_eq_of_two_vertices hK hdeg hJ hJ' hab ha ha' hb hb'


omit hK hdeg in
/-- An edge of a path graph has two ends, which are consecutive in an indexing of the path. -/
private theorem exists_consecutive_of_edge {C : Hypergraph α β} {m : ℕ} {vv : Fin (m + 1) → α}
    (hV_eq : C.vertexSet = range vv)
    (hadj : ∀ i j : Fin (m + 1), C.skeleton.Adj (vv i) (vv j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1))
    (h2 : ∀ e ∈ C.edgeSet, (C.ends e).ncard = 2) {e : β} (he : e ∈ C.edgeSet) :
    ∃ k k' : Fin (m + 1), k.1 + 1 = k'.1 ∧ C.ends e = {vv k, vv k'} := by
  obtain ⟨p, p', hpp', hends⟩ := ncard_eq_two.1 (h2 e he)
  have hp : C.Inc e p := show p ∈ C.ends e from hends ▸ Or.inl rfl
  have hp' : C.Inc e p' := show p' ∈ C.ends e from hends ▸ Or.inr rfl
  obtain ⟨i, rfl⟩ : p ∈ range vv := hV_eq ▸ C.vertex_mem_of_inc hp
  obtain ⟨j, rfl⟩ : p' ∈ range vv := hV_eq ▸ C.vertex_mem_of_inc hp'
  have hij := (hadj i j).1 ⟨hpp', e, hp, hp'⟩
  rcases hij with h | h
  · exact ⟨i, j, h, hends⟩
  · exact ⟨j, i, h, by rw [hends, pair_comm]⟩

/-- "every edge of $\Gamma$ is in a ... $\Sigma$-jump": every edge of `K` lies in a jump. In the path
of `K` through the edge, take the part between the nearest vertices of `B` on either side; the ends
of the path are in `B`, since every other vertex has two edges. -/
theorem exists_jump_of_edge {e : β} (he : e ∈ K.edgeSet) : ∃ J ∈ jumpSet K B, e ∈ J.edgeSet := by
  classical
  have hKg : K.IsGraph := hK.2.1
  obtain ⟨y, hy⟩ := (hKg e he).1
  have hyK : y ∈ K.vertexSet := K.vertex_mem_of_inc hy
  have hCcomp : IsComponentOf K (reachableComponent K y) := isComponentOf_reachableComponent hKg hyK
  set C := reachableComponent K y with hC_def
  have hCp : IsPathGraph C := hK.2.2 C hCcomp
  have heC : e ∈ C.edgeSet := ⟨he, y, hy, SimpleGraph.Reachable.refl y⟩
  have hCK : C ≤ K := hCcomp.1
  obtain ⟨hCg, -, -, h2, hinjE, -, -⟩ := id hCp
  obtain ⟨x₁, hx₁, x₂, hx₂, -, hpath, hdegC⟩ := exists_isIndexedPath_of_isPathGraph hCp ⟨e, heC⟩
  -- The two ends of the path `C` lie in `B`.
  have hendB : ∀ x ∈ C.vertexSet, (incidentEdges C x).ncard ≤ 1 → x ∈ B := by
    intro x hx h1
    by_contra hxB
    rw [incidentEdges_component_eq hKg hCcomp hx, hdeg x (hCK.vertexSet_subset hx) hxB] at h1
    omega
  have hx₁B := hendB x₁ hx₁ ((hdegC x₁ hx₁).2 (Or.inl rfl))
  have hx₂B := hendB x₂ hx₂ ((hdegC x₂ hx₂).2 (Or.inr rfl))
  obtain ⟨m, hm, vv, hv_inj, hv0, hvm, hV_eq, hadj⟩ := hpath
  obtain ⟨k₀, k₁, hk01, hendsk⟩ := exists_consecutive_of_edge hV_eq hadj h2 heC
  set k := k₀.1 with hk_def
  have hk : k + 1 < m + 1 := hk01 ▸ k₁.2
  let P : ℕ → Prop := fun l => ∀ hl : l < m + 1, vv ⟨l, hl⟩ ∈ B
  have hP0 : P 0 := fun _ => hv0 ▸ hx₁B
  -- `lo ≤ k` is the last index up to `k` in `B`, and `hi ≥ k + 1` the first one after `k`.
  let lo := Nat.findGreatest P k
  have hlo_le : lo ≤ k := Nat.findGreatest_le k
  have hlo_P : P lo := Nat.findGreatest_spec (Nat.zero_le k) hP0
  have hlo_max : ∀ l, lo < l → l ≤ k → ¬ P l := fun l h1 h2 => Nat.findGreatest_is_greatest h1 h2
  have hex : ∃ l, k + 1 ≤ l ∧ l ≤ m ∧ P l := ⟨m, by omega, le_rfl, fun _ => hvm ▸ hx₂B⟩
  let hi := Nat.find hex
  obtain ⟨hhi1, hhim, hhiP⟩ := Nat.find_spec hex
  have hhi_min : ∀ l, k + 1 ≤ l → l < hi → ¬ P l := by
    intro l h1 h2 hl
    exact Nat.find_min hex h2 ⟨h1, by omega, hl⟩
  -- The subpath of `C` from `lo` to `hi`.
  let W : Set α := vv '' {i | lo ≤ i.1 ∧ i.1 ≤ hi}
  have hW : W ⊆ C.vertexSet := by
    rintro _ ⟨i, -, rfl⟩
    rw [hV_eq]
    exact mem_range_self i
  let Q := inducedOn C W hW
  have hQle : Q ≤ C := inducedOn_le C W hW
  have hQ_ends : ∀ f ∈ Q.edgeSet, Q.ends f = C.ends f := fun f hf => (hQle.ends_eq f hf).symm
  have hQg : Q.IsGraph := fun f hf => by
    rw [hQ_ends f hf]
    exact hCg f (hQle.edgeSet_subset hf)
  have hQ2 : ∀ f ∈ Q.edgeSet, (Q.ends f).ncard = 2 := fun f hf => by
    rw [hQ_ends f hf]
    exact h2 f (hQle.edgeSet_subset hf)
  have hQinj : ∀ e₁ ∈ Q.edgeSet, ∀ e₂ ∈ Q.edgeSet, Q.ends e₁ = Q.ends e₂ → e₁ = e₂ :=
    fun e₁ he₁ e₂ he₂ h => by
      rw [hQ_ends e₁ he₁, hQ_ends e₂ he₂] at h
      exact hinjE e₁ (hQle.edgeSet_subset he₁) e₂ (hQle.edgeSet_subset he₂) h
  have hadjQ : ∀ x ∈ W, ∀ z ∈ W, Q.skeleton.Adj x z ↔ C.skeleton.Adj x z := by
    intro x hx z hz
    constructor
    · rintro ⟨hxz, f, hfx, hfz⟩
      exact ⟨hxz, f, hfx.1, hfz.1⟩
    · rintro ⟨hxz, f, hfx, hfz⟩
      have hfC := C.edge_mem_of_inc hfx
      have hsub : C.ends f ⊆ W := by
        have hpair : ({x, z} : Set α) ⊆ C.ends f := by
          rintro t (rfl | rfl)
          · exact hfx
          · exact hfz
        have hfin : (C.ends f).Finite := Set.finite_of_ncard_pos (by rw [h2 f hfC]; omega)
        have heq : ({x, z} : Set α) = C.ends f :=
          eq_of_subset_of_ncard_le hpair (by rw [h2 f hfC, ncard_pair hxz]) hfin
        rw [← heq]
        rintro t (rfl | rfl)
        · exact hx
        · exact hz
      exact ⟨hxz, f, ⟨hfx, hfC, hsub⟩, ⟨hfz, hfC, hsub⟩⟩
  let w : Fin (hi - lo + 1) → α := fun t => vv ⟨lo + t.1, by omega⟩
  have hw_inj : Injective w := by
    intro s t h
    have := congrArg Fin.val (hv_inj h)
    exact Fin.ext (by simp only at this; omega)
  have hQ_V : Q.vertexSet = range w := by
    ext x
    constructor
    · rintro ⟨i, hi', rfl⟩
      simp only [mem_ofPred_eq] at hi'
      exact ⟨⟨i.1 - lo, by omega⟩, congrArg vv (Fin.ext (by simp only; omega))⟩
    · rintro ⟨t, rfl⟩
      exact ⟨⟨lo + t.1, by omega⟩, by simp only [mem_ofPred_eq]; omega, rfl⟩
  have hw_mem : ∀ t, w t ∈ W := fun t => by
    rw [← show Q.vertexSet = W from rfl, hQ_V]
    exact mem_range_self t
  have hQpath : IsIndexedPath Q (vv ⟨lo, by omega⟩) (vv ⟨hi, by omega⟩) := by
    refine ⟨hi - lo, by omega, w, hw_inj, rfl, congrArg vv (Fin.ext (by simp only; omega)),
      hQ_V, ?_⟩
    intro s t
    rw [hadjQ _ (hw_mem s) _ (hw_mem t), hadj]
    simp only
    omega
  obtain ⟨hQP, hQdeg⟩ := isPathGraph_of_isIndexedPath hQg hQ2 hQinj hQpath
  have hlohi : vv ⟨lo, by omega⟩ ≠ vv ⟨hi, by omega⟩ := by
    intro h
    have := congrArg Fin.val (hv_inj h)
    simp only at this
    omega
  refine ⟨Q, ⟨hQle.trans hCK, hQP, vv ⟨lo, by omega⟩, hlo_P _, vv ⟨hi, by omega⟩, hhiP _, hlohi,
    ?_, ?_⟩, ?_⟩
  · rw [terminals_eq_of_loopless hQ2]
    ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hx1⟩
      exact (hQdeg x hx).1 hx1
    · intro hx
      have hxQ : x ∈ Q.vertexSet := by
        rcases hx with rfl | rfl
        · exact ⟨⟨lo, by omega⟩, by simp only [mem_ofPred_eq]; omega, rfl⟩
        · exact ⟨⟨hi, by omega⟩, by simp only [mem_ofPred_eq]; omega, rfl⟩
      exact ⟨hxQ, (hQdeg x hxQ).2 hx⟩
  · rintro x ⟨i, hi', rfl⟩ hxB
    simp only [mem_ofPred_eq] at hi'
    by_cases h1 : i.1 ≤ k
    · left
      by_contra hne
      have hlt : lo < i.1 := by
        rcases lt_or_eq_of_le hi'.1 with h | h
        · exact h
        · exact absurd (congrArg vv (Fin.ext h.symm)) hne
      exact hlo_max i.1 hlt h1 (fun _ => hxB)
    · right
      by_contra hne
      have hlt : i.1 < hi := by
        rcases lt_or_eq_of_le hi'.2 with h | h
        · exact h
        · exact absurd (congrArg vv (Fin.ext h)) hne
      exact hhi_min i.1 (by omega) hlt (fun _ => hxB)
  · refine ⟨heC, ?_⟩
    rw [hendsk]
    rintro x (rfl | rfl)
    · exact ⟨k₀, by simp only [mem_ofPred_eq]; omega, rfl⟩
    · exact ⟨k₁, by simp only [mem_ofPred_eq]; omega, rfl⟩

omit hK in
/-- There are finitely many jumps: a jump is determined by its set of edges. -/
theorem jumpSet_finite : (jumpSet K B).Finite := by
  have hinj : InjOn (fun J : Hypergraph α β => J.edgeSet) (jumpSet K B) := by
    intro J hJ J' hJ' hE
    obtain ⟨f, hf⟩ := edgeSet_nonempty_of_mem_jumpSet hJ
    have hE' : J.edgeSet = J'.edgeSet := hE
    exact jump_eq_of_edge hdeg hJ hJ' hf (hE' ▸ hf)
  refine Finite.of_finite_image ?_ hinj
  refine (K.edgeSet_finite.finite_subsets).subset ?_
  rintro _ ⟨J, hJ, rfl⟩
  exact hJ.1.edgeSet_subset

end jumps

end GM21
end GraphMinor

namespace GraphMinor
namespace GM21

open Set Function Hypergraph GraphMinor.GM10 GraphMinor.Surface

universe u' v' w'

section presentation

variable {α : Type u'} {β : Type v'} {S : Type w'} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {L : Hypergraph α β}

/-- The `Σ`-jumps of a presentation are the jumps of `Γ` between the vertices of `Γ` in
`bd(Σ)`. -/
theorem sigmaJumps_eq_jumpSet (hiso : IsDrawingIso Γ Γ_sub ιV ιE) :
    sigmaJumps Γ Γ_sub ιV = jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)) := by
  ext J
  constructor
  · rintro ⟨hJ, hJp, u, hu, v, hv, huv, hterm, hB⟩
    refine ⟨hJ, hJp, ιV u, mem_image_of_mem ιV hu, ιV v, mem_image_of_mem ιV hv,
      fun h => huv (hiso.ιV_injOn hu.1 hv.1 h), hterm, ?_⟩
    rintro x hx ⟨x₀, hx₀, rfl⟩
    rcases hB x₀ hx₀ hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro ⟨hJ, hJp, _, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, huv, hterm, hB⟩
    refine ⟨hJ, hJp, u, hu, v, hv, fun h => huv (h ▸ rfl), hterm, ?_⟩
    intro x hx hxJ
    rcases hB (ιV x) hxJ (mem_image_of_mem ιV hx) with h | h
    · exact Or.inl (hiso.ιV_injOn hx.1 hu.1 h)
    · exact Or.inr (hiso.ιV_injOn hx.1 hv.1 h)

/-- For an exhaustive linkage, every vertex of `Γ` outside `bd(Σ)` has two edges in `Γ`. -/
theorem IsExhaustiveLinkage.ncard_incidentEdges_eq_two
    (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (hL : IsExhaustiveLinkage G Γ_sub r H L) :
    ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2 := by
  intro y hy hyB
  obtain ⟨x, hx, rfl⟩ : y ∈ ιV '' Γ.V := hP.ιV_image ▸ hy
  have hxbd : x ∉ bd S := fun h => hyB (mem_image_of_mem ιV ⟨hx, h⟩)
  have h := IsExhaustiveLinkage.vertexDegree_eq_two hP hL hx hxbd
  rwa [vertexDegree_eq_ncard_incidentEdges
    (fun e he => (IsExhaustiveLinkage.isLinkage hP hL).ends_ncard_eq_two he)] at h

end presentation

end GM21
end GraphMinor
