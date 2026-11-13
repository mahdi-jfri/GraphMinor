module

public import GraphMinor.GM01.RootedBranchModels
public import GraphMinor.GM09.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.PathLastEdgeCover

/-!
# Contracting a subdivision with an internal attachment vertex

The contraction in Graph Minors I, (4.9), page 58, retains the point
where the first path enters `D`. If this is internal to a replacing
path, assign that path's whole interior to a chosen end. Give that end
rank zero before orienting the source edges. Removing the last edge
then puts every internal vertex in its branch. The resulting rooted
model keeps the attachment point in the intended source-root branch.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- Contract a finite subdivision while rooting its chosen source
vertex at its centre or an internal point of an incident replacing
path. All path interiors incident with that source vertex are assigned
to its branch, as needed in GM01 (4.9), page 58. -/
theorem exists_rooted_model_of_finite_subdivision_at_vertex {α β ν : Type*} [Finite ν]
    {S : SimpleGraph ν} {G : Graph α β} (c : ν → α) (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(G)) (P : S.edgeSet → Graph α β)
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : ν) (x : V(G))
    (hx : x.val = c root ∨ ∃ e : S.edgeSet,
      root ∈ e.val ∧ x.val ∈ V(P e) ∧ x.val ∉ range c) :
    ∃ M : RootedMinorModel
      (⟨Graph.ofSimpleGraph S, ⟨root, mem_univ _⟩⟩ : RootedGraph ν (Sym2 ν))
      (⟨G, x⟩ : RootedGraph α β), ∀ w : ν, c w ∈ M.branch ⟨w, mem_univ _⟩ := by
  classical
  let : Fintype ν := Fintype.ofFinite ν
  let base : ν → ℕ := fun v ↦ (Fintype.equivFin ν v).val
  have hbase : Injective base := fun _ _ h ↦ (Fintype.equivFin ν).injective (Fin.ext h)
  let rk : ν → ℕ := fun v ↦ if v = root then 0 else base v + 1
  have hrk : Injective rk := by
    intro a b hab
    by_cases ha : a = root
    · by_cases hb : b = root
      · exact ha.trans hb.symm
      · simp only [rk, ha, hb, ↓reduceIte] at hab
        omega
    · by_cases hb : b = root
      · simp only [rk, ha, hb, ↓reduceIte] at hab
        omega
      · simp only [rk, ha, hb, ↓reduceIte] at hab
        exact hbase (Nat.add_right_cancel hab)
  have hrkRoot : rk root = 0 := by simp only [rk, ↓reduceIte]
  have hor : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧ S.Adj a b ∧ rk a < rk b := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : S.Adj a b := he
      rcases lt_or_gt_of_ne (fun h ↦ hab.ne (hrk h)) with hlt | hgt
      · exact ⟨a, b, rfl, hab, hlt⟩
      · exact ⟨b, a, Sym2.eq_swap, hab.symm, hgt⟩
  let lo (e : S.edgeSet) := (hor e).choose
  let hi (e : S.edgeSet) := (hor e).choose_spec.choose
  have heq (e : S.edgeSet) : e.val = s(lo e,hi e) := (hor e).choose_spec.choose_spec.1
  have hadj (e : S.edgeSet) : S.Adj (lo e) (hi e) := (hor e).choose_spec.choose_spec.2.1
  have hrank (e : S.edgeSet) : rk (lo e) < rk (hi e) := (hor e).choose_spec.choose_spec.2.2
  have hRootLo : ∀ e : S.edgeSet, root ∈ e.val → lo e = root := by
    intro e he
    rw [heq e, Sym2.mem_iff] at he
    rcases he with he | he
    · exact he.symm
    · have hbad := hrank e
      rw [← he, hrkRoot] at hbad
      exact False.elim (Nat.not_lt_zero _ hbad)
  have hPe : ∀ e : S.edgeSet, IsGraphPathWithEnds G (P e) (c (lo e)) (c (hi e)) ∧
      V(P e) ∩ range c = {c (lo e),c (hi e)} := by
    intro e
    obtain ⟨a, b, he, hP, hRange⟩ := hPaths e
    have hp := (heq e).symm.trans he
    rcases Sym2.eq_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hP, hRange⟩
    · exact ⟨hP.symm, hRange.trans (pair_comm _ _)⟩
  have hlast : ∀ e : S.edgeSet, ∃ (edge : β) (q : α) (Q : Graph α β),
      (P e).IsLink edge q (c (hi e)) ∧ Q ≤ P e ∧
      IsGraphPathWithEnds G Q (c (lo e)) q ∧ c (hi e) ∉ V(Q) ∧
      V(P e) = insert (c (hi e)) V(Q) := by
    intro e
    exact exists_last_edge_with_vertex_cover (hPe e).1 (fun h ↦ (hadj e).ne (hc h))
  let edge (e : S.edgeSet) := (hlast e).choose
  let q (e : S.edgeSet) := (hlast e).choose_spec.choose
  let Q (e : S.edgeSet) := (hlast e).choose_spec.choose_spec.choose
  have hLink (e : S.edgeSet) : (P e).IsLink (edge e) (q e) (c (hi e)) :=
    (hlast e).choose_spec.choose_spec.choose_spec.1
  have hQP (e : S.edgeSet) : Q e ≤ P e := (hlast e).choose_spec.choose_spec.choose_spec.2.1
  have hQ (e : S.edgeSet) : IsGraphPathWithEnds G (Q e) (c (lo e)) (q e) :=
    (hlast e).choose_spec.choose_spec.choose_spec.2.2.1
  have hNot (e : S.edgeSet) : c (hi e) ∉ V(Q e) :=
    (hlast e).choose_spec.choose_spec.choose_spec.2.2.2.1
  have hCover (e : S.edgeSet) : V(P e) = insert (c (hi e)) V(Q e) :=
    (hlast e).choose_spec.choose_spec.choose_spec.2.2.2.2
  let B (v : ν) : Set α := {c v} ∪ ⋃ e : S.edgeSet, ⋃ (_ : lo e = v), V(Q e)
  have hQB : ∀ e, V(Q e) ⊆ B (lo e) := by
    intro e x hx
    exact Or.inr (mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨rfl, hx⟩⟩)
  have hCentreQ : ∀ e v, c v ∈ V(Q e) → v = lo e := by
    intro e v hv
    have hm : c v ∈ ({c (lo e),c (hi e)} : Set α) :=
      (hPe e).2 ▸ ⟨(hQP e).vertexSet_mono hv, mem_range_self v⟩
    rcases hm with h | h
    · exact hc h
    · exact False.elim (hNot e (h ▸ hv))
  have hBdisj : Pairwise fun v w ↦ Disjoint (B v) (B w) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx
    · have hxc : x = c v := hx
      subst x
      rcases hy with hy | hy
      · exact hvw (hc hy)
      · obtain ⟨e, hy⟩ := mem_iUnion.mp hy
        obtain ⟨hew, hy⟩ := mem_iUnion.mp hy
        exact hvw ((hCentreQ e v hy).trans hew)
    · obtain ⟨e, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hev, hx⟩ := mem_iUnion.mp hx
      rcases hy with hy | hy
      · have hxc : x = c w := hy
        subst x
        exact hvw ((hCentreQ e w hx).trans hev).symm
      · obtain ⟨f, hy⟩ := mem_iUnion.mp hy
        obtain ⟨hfw, hy⟩ := mem_iUnion.mp hy
        by_cases hef : e = f
        · exact hvw (hev.symm.trans (hef ▸ hfw))
        · obtain ⟨z, hz⟩ := hInter e f hef
            ⟨(hQP e).vertexSet_mono hx, (hQP f).vertexSet_mono hy⟩
          have hzQe : c z ∈ V(Q e) := hz.symm ▸ hx
          have hzQf : c z ∈ V(Q f) := hz.symm ▸ hy
          exact hvw (hev.symm.trans ((hCentreQ e z hzQe).symm.trans
            ((hCentreQ f z hzQf).trans hfw)))
  have hBsub : ∀ v, B v ⊆ V(G) := by
    intro v x hx
    rcases hx with hx | hx
    · exact hx ▸ hcentres v
    · obtain ⟨e, hx⟩ := mem_iUnion.mp hx
      obtain ⟨_, hx⟩ := mem_iUnion.mp hx
      exact (hQ e).le.vertexSet_mono hx
  have hBconn : ∀ v, GraphConnected (G.induce (B v)) := by
    intro v
    have htoCentre : ∀ x ∈ B v, Relation.ReflTransGen (G.induce (B v)).Adj x (c v) := by
      intro x hx
      rcases hx with hx | hx
      · have heq : x = c v := hx
        subst x
        exact .refl
      · obtain ⟨e, hx⟩ := mem_iUnion.mp hx
        obtain ⟨hev, hx⟩ := mem_iUnion.mp hx
        have hCv : c v ∈ V(Q e) := hev ▸ (hQ e).left_mem
        have hreach := (graphConnected_of_isGraphPath (hQ e)).2 x hx (c v) hCv
        apply Relation.ReflTransGen.mono ?_ x (c v) hreach
        intro a b hab
        obtain ⟨edge', hlink⟩ := hab
        exact ⟨edge', hlink.mono (hQ e).le, hev ▸ hQB e hlink.left_mem,
          hev ▸ hQB e hlink.right_mem⟩
    exact ⟨⟨c v, Or.inl rfl⟩, fun x hx y hy ↦
      (htoCentre x hx).trans (Std.Symm.symm _ _ (htoCentre y hy))⟩
  have hxB : x.val ∈ B root := by
    rcases hx with hx | ⟨e, heRoot, hxe, hxNot⟩
    · exact Or.inl hx
    · have hlo := hRootLo e heRoot
      have hxeQ : x.val ∈ V(Q e) := by
        have hxCover := hCover e ▸ hxe
        rcases hxCover with hxHi | hxQ
        · exact False.elim (hxNot ⟨hi e, hxHi.symm⟩)
        · exact hxQ
      exact hlo ▸ hQB e hxeQ
  have hAdj : ∀ {a b : ν}, S.Adj a b →
      ∃ e u, u ∈ B a ∧ ∃ v, v ∈ B b ∧ G.IsLink e u v := by
    intro a b hab
    let e : S.edgeSet := ⟨s(a,b), hab⟩
    have hjoin : G.IsLink (edge e) (q e) (c (hi e)) := (hLink e).mono (hPe e).1.le
    have hp : s(a,b) = s(lo e,hi e) := heq e
    rcases Sym2.eq_iff.mp hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hqa : q e ∈ B a := ha.symm ▸ hQB e (hQ e).right_mem
      have hcb : c (hi e) ∈ B b := hb.symm ▸ (Or.inl rfl : c (hi e) ∈ B (hi e))
      exact ⟨edge e, q e, hqa, c (hi e), hcb, hjoin⟩
    · have hca : c (hi e) ∈ B a := ha.symm ▸ (Or.inl rfl : c (hi e) ∈ B (hi e))
      have hqb : q e ∈ B b := hb.symm ▸ hQB e (hQ e).right_mem
      exact ⟨edge e, c (hi e), hca, q e, hqb, hjoin.symm⟩
  let M := rootedModelOfBranchSets S ⟨G, x⟩ B hBsub hBdisj hBconn hAdj root hxB
  refine ⟨M, ?_⟩
  intro w
  change c w ∈ (rootedModelOfBranchSets S ⟨G, x⟩ B hBsub hBdisj hBconn hAdj root hxB).branch ⟨w, mem_univ _⟩
  rw [rootedModelOfBranchSets_branch S ⟨G, x⟩ B hBsub hBdisj hBconn hAdj root hxB]
  exact Or.inl rfl

/-- Choose the controlled rooted model supplied by the finite
subdivision contraction and its proved centre-preservation property. -/
noncomputable def rootedModelOfFiniteSubdivisionAtVertex {α β ν : Type*} [Finite ν]
    {S : SimpleGraph ν} {G : Graph α β} (c : ν → α) (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(G)) (P : S.edgeSet → Graph α β)
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : ν) (x : V(G))
    (hx : x.val = c root ∨ ∃ e : S.edgeSet,
      root ∈ e.val ∧ x.val ∈ V(P e) ∧ x.val ∉ range c) :
    RootedMinorModel
      (⟨Graph.ofSimpleGraph S, ⟨root, mem_univ _⟩⟩ : RootedGraph ν (Sym2 ν))
      (⟨G, x⟩ : RootedGraph α β) :=
  (exists_rooted_model_of_finite_subdivision_at_vertex c hc hcentres P hPaths hInter root x hx).choose

/-- Every source centre stays in its own branch of the controlled
subdivision contraction, retaining both endpoints for GM01 (4.10). -/
theorem rootedModelOfFiniteSubdivisionAtVertex_centre_mem {α β ν : Type*} [Finite ν]
    {S : SimpleGraph ν} {G : Graph α β} (c : ν → α) (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(G)) (P : S.edgeSet → Graph α β)
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : ν) (x : V(G))
    (hx : x.val = c root ∨ ∃ e : S.edgeSet,
      root ∈ e.val ∧ x.val ∈ V(P e) ∧ x.val ∉ range c) (w : ν) :
    c w ∈ (rootedModelOfFiniteSubdivisionAtVertex c hc hcentres P hPaths hInter root x hx).branch
      ⟨w, mem_univ _⟩ := by
  exact (exists_rooted_model_of_finite_subdivision_at_vertex c hc hcentres P hPaths hInter root x hx).choose_spec w

end GraphMinor.GM01
