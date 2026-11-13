module

public import GraphMinor.GM01.RootedModelVertexArms
import GraphMinor.GM16.ModelBranchCentres
import GraphMinor.GM09.Basic

/-!
# Centres and arms for a rooted subcubic model

For the subdivision step in the proof of Graph Minors I, (1.1), page 55,
choose ordinary branch centres away from the source root. At the root,
choose the centre using the two incident edge attachments and the target
root. The additional root path then meets every arm only at the root's
centre and avoids all represented source edges.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

universe u v w

/-- Choose compatible branch centres and edge arms while keeping a path
from the root centre to the distinguished target root. This is the rooted
form of the elementary subdivision step on page 55. -/
theorem exists_rooted_model_branch_centres {α : Type u} {β : Type v} {ν : Type w} [Finite ν]
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe)
    (hDeg : ∀ v, (H.neighborSet v).ncard ≤ 3) (r : ν)
    (hRootDeg : (H.neighborSet r).ncard ≤ 2) (hNonempty : (H.neighborSet r).Nonempty)
    (root : α) (hroot : root ∈ ηv r) :
    ∃ (c : ν → α) (attach : ∀ v, H.neighborSet v → α)
      (arm : ∀ v, H.neighborSet v → Graph α β) (R : Graph α β),
      Function.Injective c ∧ (∀ v, c v ∈ ηv v) ∧
      (∀ v i, attach v i ∈ ηv v ∧ G.Inc (ηe s(v,i.val)) (attach v i)) ∧
      (∀ v i, IsGraphPathWithEnds G (arm v i) (c v) (attach v i)) ∧
      (∀ v i, V(arm v i) ⊆ ηv v ∧ Disjoint E(arm v i) (ηe '' H.edgeSet)) ∧
      (∀ v i j, i ≠ j → V(arm v i) ∩ V(arm v j) = {c v}) ∧
      IsGraphPathWithEnds G R (c r) root ∧ V(R) ⊆ ηv r ∧
      Disjoint E(R) (ηe '' H.edgeSet) ∧
      (∀ v i, V(R) ∩ V(arm v i) ⊆ {c r}) := by
  classical
  obtain ⟨c₀, attach₀, arm₀, hc₀Inj, hc₀, hAttach₀, hPath₀, hSub₀, hInter₀⟩ :=
    GM16.exists_model_branch_centres h hDeg
  obtain ⟨K, hK, hVK, m, attachR, armR, R, hm, hAttachR, hPathR, hR, hInterR, hRootInter⟩ :=
    rooted_model_vertex_arms h r hRootDeg hNonempty root hroot
  have hKG : K ≤ G := hK.trans Graph.deleteEdges_le
  let c (v : ν) := if v = r then m else c₀ v
  let attach (v : ν) : H.neighborSet v → α :=
    if hv : v = r then hv.symm ▸ attachR else attach₀ v
  let arm (v : ν) : H.neighborSet v → Graph α β :=
    if hv : v = r then hv.symm ▸ armR else arm₀ v
  have hc : ∀ v, c v ∈ ηv v := by
    intro v
    by_cases hv : v = r
    · subst v
      simpa only [c, ↓reduceIte] using hVK ▸ hm
    · simpa only [c, hv, ↓reduceIte] using hc₀ v
  have hcInj : Function.Injective c := by
    intro v w heq
    by_contra hne
    exact (Set.disjoint_left.mp (h.vertex_disjoint v (mem_univ _) w (mem_univ _) hne))
      (hc v) (heq.symm ▸ hc w)
  have hAttach : ∀ v i, attach v i ∈ ηv v ∧ G.Inc (ηe s(v,i.val)) (attach v i) := by
    intro v i
    by_cases hv : v = r
    · subst v
      simp only [attach, ↓reduceDIte]
      exact ⟨hVK ▸ (hAttachR i).1, (hAttachR i).2⟩
    · simpa only [attach, hv, ↓reduceDIte] using hAttach₀ v i
  have hPath : ∀ v i, IsGraphPathWithEnds G (arm v i) (c v) (attach v i) := by
    intro v i
    by_cases hv : v = r
    · subst v
      simpa only [arm, c, attach, ↓reduceDIte, ↓reduceIte] using (hPathR i).mono hKG
    · simpa only [arm, c, attach, hv, ↓reduceDIte, ↓reduceIte] using hPath₀ v i
  have hSub : ∀ v i, V(arm v i) ⊆ ηv v ∧ Disjoint E(arm v i) (ηe '' H.edgeSet) := by
    intro v i
    by_cases hv : v = r
    · subst v
      simp only [arm, ↓reduceDIte]
      refine ⟨fun x hx ↦ hVK ▸ (hPathR i).le.vertexSet_mono hx, Set.disjoint_left.mpr ?_⟩
      intro e he hchosen
      exact (((hPathR i).le.trans hK).edgeSet_mono he).2 hchosen
    · simpa only [arm, hv, ↓reduceDIte] using hSub₀ v i
  have hInter : ∀ v i j, i ≠ j → V(arm v i) ∩ V(arm v j) = {c v} := by
    intro v i j hij
    by_cases hv : v = r
    · subst v
      simpa only [arm, c, ↓reduceDIte, ↓reduceIte] using hInterR i j hij
    · simpa only [arm, c, hv, ↓reduceDIte, ↓reduceIte] using hInter₀ v i j hij
  have hRSub : V(R) ⊆ ηv r := fun x hx ↦ hVK ▸ hR.le.vertexSet_mono hx
  have hRAvoid : Disjoint E(R) (ηe '' H.edgeSet) := by
    apply Set.disjoint_left.mpr
    intro e he hchosen
    exact ((hR.le.trans hK).edgeSet_mono he).2 hchosen
  have hRInter : ∀ v i, V(R) ∩ V(arm v i) ⊆ {c r} := by
    intro v i
    by_cases hv : v = r
    · subst v
      simpa only [arm, c, ↓reduceDIte, ↓reduceIte] using
        ((Set.inter_comm V(R) V(armR i)).trans (hRootInter i)).subset
    · intro x hx
      exact False.elim ((Set.disjoint_left.mp
        (h.vertex_disjoint r (mem_univ _) v (mem_univ _) (Ne.symm hv)))
          (hRSub hx.1) ((hSub v i).1 hx.2))
  refine ⟨c, attach, arm, R, hcInj, hc, hAttach, hPath, hSub, hInter, ?_, hRSub, hRAvoid, hRInter⟩
  simpa only [c, ↓reduceIte] using hR.mono hKG

end GraphMinor.GM01
