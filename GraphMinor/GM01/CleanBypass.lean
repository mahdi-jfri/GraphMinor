module

public import GraphMinor.GM01.GraphSeparators

/-!
# A bypass with no internal vertex in the comb

The first step of Graph Minors I, (4.1), page 55, trims a path witnessing
failure of separation. Its ends lie on the two sides of the proposed
separator. Stop it at its first meeting with the far side and start it
after its last meeting with the near side. The trimmed path has no
internal vertex on either side, and it avoids the separator. Since these
three sets cover `H`, it has no internal vertex in `H`.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- The clean bypass extraction in the proof of Graph Minors I, (4.1),
page 55. Failure of separation gives a path whose only vertices in the
covered graph are its two ends, one on each side. -/
theorem exists_clean_bypass_of_not_graphSeparates {α β : Type*} {G H : Graph α β}
    {X A B : Set α} (hA : A ⊆ V(H)) (hB : B ⊆ V(H))
    (hcover : V(H) ⊆ A ∪ X ∪ B) (hno : ¬ GraphSeparates G X A B) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ P : Graph α β,
      IsGraphPathWithEnds G P a b ∧ Disjoint V(P) X ∧ V(P) ∩ V(H) = {a,b} := by
  obtain ⟨u, hu, v, hv, Q, hQ, havoid⟩ := not_graphSeparates_iff.mp hno
  obtain ⟨a, ha, b, hb, P, hPQ, hP, hPA, hPB⟩ :=
    hQ.exists_isFromToPathWithEnds hu hv
  have havoidP : Disjoint V(P) X := havoid.mono_left hPQ.vertexSet_mono
  refine ⟨a, ha, b, hb, P, hP, havoidP, Subset.antisymm ?_ ?_⟩
  · intro x hx
    rcases hcover hx.2 with (hxA | hxX) | hxB
    · exact Or.inl (mem_singleton_iff.mp (hPA ▸ ⟨hx.1, hxA⟩))
    · exact False.elim (disjoint_left.mp havoidP hx.1 hxX)
    · exact Or.inr (hPB ▸ ⟨hx.1, hxB⟩)
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨hP.left_mem, hA ha⟩
    · have hxb : x = b := hx
      subst x
      exact ⟨hP.right_mem, hB hb⟩

end GraphMinor.GM01
