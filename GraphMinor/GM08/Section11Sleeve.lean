module

public import GraphMinor.GM03.Section3a

/-!
# The first vertex of a walk in a set

A walk that ends in a set `B` has an initial part that meets `B` only in its last vertex
(`exists_walk_first_mem`). This is used in `GraphMinor/GM08/Section9Paths.lean`.
-/

public section

namespace GraphMinor
namespace GM08

open Set Graph Surface

universe u v

variable {α : Type u} {β : Type v}

/-- A walk that ends in `B` has an initial part that meets `B` only in its last vertex. -/
theorem exists_walk_first_mem {G : Graph α β} {B : Set α} {x y : α} (W : GraphWalk G x y)
    (hy : y ∈ B) :
    ∃ c ∈ B, ∃ W' : GraphWalk G x c, (∀ z ∈ W'.support, z ∈ W.support) ∧
      ∀ z ∈ W'.support, z ∈ B → z = c := by
  induction W with
  | @nil u hu => exact ⟨u, hy, .nil hu, fun z hz => hz, fun z hz _ => by simpa using hz⟩
  | @cons u v w' e h rest ih =>
    by_cases hu : u ∈ B
    · refine ⟨u, hu, .nil h.left_mem, fun z hz => ?_, fun z hz _ => by simpa using hz⟩
      simp only [GraphWalk.support_nil, List.mem_singleton] at hz
      subst hz
      exact GraphWalk.start_mem_support _
    · obtain ⟨c, hc, W', hsub, hfirst⟩ := ih hy
      refine ⟨c, hc, .cons h W', fun z hz => ?_, fun z hz hzB => ?_⟩
      · simp only [GraphWalk.support_cons, List.mem_cons] at hz ⊢
        rcases hz with rfl | hz
        · exact Or.inl rfl
        · exact Or.inr (hsub z hz)
      · simp only [GraphWalk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact absurd hzB hu
        · exact hfirst z hz hzB

end GM08
end GraphMinor
