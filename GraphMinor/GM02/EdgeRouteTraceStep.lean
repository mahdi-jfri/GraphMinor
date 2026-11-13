module

public import GraphMinor.GM02.EdgeRouteData
public import GraphMinor.GM02.EdgeRouteGlue
import GraphMinor.GM11.Walks

/-!
# Following host routes through one suppression

Orient the routes of the two removed edges toward their common vertex,
then glue them. Retained edges keep their routes. The old interiors
avoid every vertex of the current graph, and the old edge lists are
disjoint. Thus the new interior and edge list meet no retained route.
-/

set_option backward.isDefEq.respectTransparency.types false

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- Suppressing the current pattern glues its two edge traces and retains all other traces. -/
theorem exists_edgeRoute_trace_step {α : Type u} {β : Type v} {K M : Graph α β}
    (R : E(M) → EdgeRoute K) (hKM : V(M) ⊆ V(K))
    (hR : ∀ f, M.IsLink f.val (R f).start (R f).finish ∧
      (R f).walk.support = (R f).start :: ((R f).inner ++ [(R f).finish]) ∧
      (R f).inner.Nodup ∧ (∀ y ∈ (R f).inner, y ∈ V(K) \ V(M)) ∧
      (R f).walk.edges.Nodup ∧ (R f).walk.edges ≠ [])
    (hDis : ∀ f g, f ≠ g →
      Disjoint {y | y ∈ (R f).inner} {y | y ∈ (R g).inner} ∧
      Disjoint {e | e ∈ (R f).walk.edges} {e | e ∈ (R g).walk.edges})
    (d : SuppressionData M) :
    ∃ R' : E(d.result) → EdgeRoute K,
      (∀ f, d.result.IsLink f.val (R' f).start (R' f).finish ∧
        (R' f).walk.support = (R' f).start :: ((R' f).inner ++ [(R' f).finish]) ∧
        (R' f).inner.Nodup ∧ (∀ y ∈ (R' f).inner, y ∈ V(K) \ V(d.result)) ∧
        (R' f).walk.edges.Nodup ∧ (R' f).walk.edges ≠ []) ∧
      ∀ f g, f ≠ g →
        Disjoint {y | y ∈ (R' f).inner} {y | y ∈ (R' g).inner} ∧
        Disjoint {e | e ∈ (R' f).walk.edges} {e | e ∈ (R' g).walk.edges} := by
  let f₁ : E(M) := ⟨d.first, d.first_link.edge_mem⟩
  let f₂ : E(M) := ⟨d.second, d.second_link.edge_mem⟩
  have hf₁₂ : f₁ ≠ f₂ := fun h => d.first_ne_second (congrArg Subtype.val h)
  obtain ⟨l₁, W₁, hs₁, hn₁, ho₁, heN₁, heNon₁, hmV₁, hmE₁⟩ :=
    exists_oriented_edgeRoute_properties (hR f₁).1 d.first_link.symm
      (R f₁).inner (R f₁).walk (V(K) \ V(M))
      (hR f₁).2.1 (hR f₁).2.2.1 (hR f₁).2.2.2.1 (hR f₁).2.2.2.2.1 (hR f₁).2.2.2.2.2
  obtain ⟨l₂, W₂, hs₂, hn₂, ho₂, heN₂, heNon₂, hmV₂, hmE₂⟩ :=
    exists_oriented_edgeRoute_properties (hR f₂).1 d.second_link
      (R f₂).inner (R f₂).walk (V(K) \ V(M))
      (hR f₂).2.1 (hR f₂).2.2.1 (hR f₂).2.2.2.1 (hR f₂).2.2.2.2.1 (hR f₂).2.2.2.2.2
  have hdV : Disjoint {y | y ∈ l₁} {y | y ∈ l₂} := by
    rw [Set.disjoint_left]
    intro y hy hz
    exact Set.disjoint_left.1 (hDis f₁ f₂ hf₁₂).1 ((hmV₁ y).1 hy) ((hmV₂ y).1 hz)
  have hdE : Disjoint {e | e ∈ W₁.edges} {e | e ∈ W₂.edges} := by
    rw [Set.disjoint_left]
    intro e he hf
    exact Set.disjoint_left.1 (hDis f₁ f₂ hf₁₂).2 ((hmE₁ e).1 he) ((hmE₂ e).1 hf)
  have hglue := edgeRoute_glue_geometry d hKM l₁ l₂ W₁ W₂ hn₁ hn₂ ho₁ ho₂ hdV heN₁ heN₂ heNon₁ hdE
  let glued : EdgeRoute K := ⟨d.left, d.right, l₁ ++ d.vertex :: l₂, W₁.append W₂⟩
  have hret : ∀ f : E(d.result), f.val ≠ d.fresh →
      f.val ∈ E(M) ∧ f.val ≠ d.first ∧ f.val ≠ d.second := by
    intro f hf
    rcases f.property with ⟨hM, hne⟩ | hnew
    · exact ⟨hM, fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩
    · exact (hf (Set.mem_singleton_iff.1 hnew)).elim
  let ret : ∀ f : E(d.result), f.val ≠ d.fresh → E(M) :=
    fun f hf => ⟨f.val, (hret f hf).1⟩
  have hglueDis : ∀ g : E(M), g.val ≠ d.first → g.val ≠ d.second →
      Disjoint {y | y ∈ glued.inner} {y | y ∈ (R g).inner} ∧
      Disjoint {e | e ∈ glued.walk.edges} {e | e ∈ (R g).walk.edges} := by
    intro g hg₁ hg₂
    have hg₁' : f₁ ≠ g := fun h => hg₁ (congrArg Subtype.val h).symm
    have hg₂' : f₂ ≠ g := fun h => hg₂ (congrArg Subtype.val h).symm
    constructor
    · rw [Set.disjoint_left]
      intro y hy hyg
      change y ∈ l₁ ++ d.vertex :: l₂ at hy
      rcases List.mem_append.1 hy with hy | hy
      · exact Set.disjoint_left.1 (hDis f₁ g hg₁').1 ((hmV₁ y).1 hy) hyg
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact (hR g).2.2.2.1 _ hyg |>.2 d.first_link.left_mem
        · exact Set.disjoint_left.1 (hDis f₂ g hg₂').1 ((hmV₂ y).1 hy) hyg
    · rw [Set.disjoint_left]
      intro e he heg
      change e ∈ (W₁.append W₂).edges at he
      rw [GraphWalk.edges_append] at he
      rcases List.mem_append.1 he with he | he
      · exact Set.disjoint_left.1 (hDis f₁ g hg₁').2 ((hmE₁ e).1 he) heg
      · exact Set.disjoint_left.1 (hDis f₂ g hg₂').2 ((hmE₂ e).1 he) heg
  let R' : E(d.result) → EdgeRoute K :=
    fun f => if hf : f.val = d.fresh then glued else R (ret f hf)
  have hFresh : ∀ f (hf : f.val = d.fresh), R' f = glued := by
    intro f hf
    exact dite_eq_left hf
  have hKept : ∀ f (hf : f.val ≠ d.fresh), R' f = R (ret f hf) := by
    intro f hf
    exact dite_eq_right hf
  refine ⟨R', ?_, ?_⟩
  · intro f
    by_cases hf : f.val = d.fresh
    · rw [hFresh f hf]
      refine ⟨?_, ?_, hglue.1, hglue.2.1, hglue.2.2.1, hglue.2.2.2⟩
      · rw [hf]
        exact (d.fresh_isLink_iff _ _).2 (Or.inl ⟨rfl, rfl⟩)
      · exact edgeRoute_append_support l₁ l₂ W₁ W₂ hs₁ hs₂
    · rw [hKept f hf]
      obtain ⟨hl, hs, hn, ho, heN, heNon⟩ := hR (ret f hf)
      exact ⟨Or.inl ⟨hl, (hret f hf).2⟩, hs, hn,
        fun y hy => ⟨(ho y hy).1, fun h => (ho y hy).2 h.1⟩, heN, heNon⟩
  · intro f g hfg
    by_cases hf : f.val = d.fresh <;> by_cases hg : g.val = d.fresh
    · exact (hfg (Subtype.ext (hf.trans hg.symm))).elim
    · rw [hFresh f hf, hKept g hg]
      exact hglueDis (ret g hg) (hret g hg).2.1 (hret g hg).2.2
    · rw [hKept f hf, hFresh g hg]
      have hd := hglueDis (ret f hf) (hret f hf).2.1 (hret f hf).2.2
      exact ⟨hd.1.symm, hd.2.symm⟩
    · rw [hKept f hf, hKept g hg]
      apply hDis
      intro heq
      have hv : f.val = g.val := congrArg (fun t : E(M) => t.val) heq
      exact hfg (Subtype.ext hv)

end GraphMinor.GM02
