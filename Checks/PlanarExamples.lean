module

public import GraphMinor.Planar.Defs
public import GraphMinor.GM13.Section7a
import GraphMinor.GM11.ArcDrawings
import GraphMinor.GM16.EmbeddedLineGraphDrawing
import Mathlib.Tactic.FinCases

/-!
# Examples of Planar Graphs

This file verifies `IsPlanar` (from `GraphMinor/Planar/Defs.lean`) on three concrete families of
graphs required by the planarity specification:

1. The triangle `completeGraph 3` (`isPlanar_completeGraph_three`).
2. The complete graph on four vertices `completeGraph 4` (`isPlanar_completeGraph_four`).
3. The elementary wall of each height `GM13.elementaryWall h` (`isPlanar_elementaryWall`).
-/

@[expose] public section

namespace GraphMinor.Planar.Examples

open Set Function Topology Graph SimpleGraph
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM13 GraphMinor.GM16

/-! ## 1. Straight-line segments in the plane -/

/-- The straight-line parametrization from `A` to `B` in `ℝ × ℝ`. -/
def segmentMap (A B : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  ((1 - t) * A.1 + t * B.1, (1 - t) * A.2 + t * B.2)

/-- The straight-line segment in `ℝ × ℝ` joining `A` and `B`. -/
def straightSegment (A B : ℝ × ℝ) : Set (ℝ × ℝ) :=
  segmentMap A B '' Icc 0 1

lemma straightSegment_symm (A B : ℝ × ℝ) :
    straightSegment A B = straightSegment B A := by
  ext p
  constructor <;> rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩ <;>
    refine ⟨1 - t, ⟨by linarith, by linarith⟩,
      Prod.ext (by dsimp [segmentMap]; ring) (by dsimp [segmentMap]; ring)⟩

lemma straightSegment_isLine {A B : ℝ × ℝ} (hne : A ≠ B) :
    IsLineWithEnds (straightSegment A B) A B := by
  have hp : Continuous (segmentMap A B) := by
    unfold segmentMap
    fun_prop
  have hi : InjOn (segmentMap A B) (Icc (0 : ℝ) 1) := by
    intro s _ t _ heq
    have h1 : (1 - s) * A.1 + s * B.1 = (1 - t) * A.1 + t * B.1 := congrArg Prod.fst heq
    have h2 : (1 - s) * A.2 + s * B.2 = (1 - t) * A.2 + t * B.2 := congrArg Prod.snd heq
    by_contra hst
    have hA1 : A.1 = B.1 := by
      have hmul : (s - t) * (B.1 - A.1) = 0 := by linarith
      rcases mul_eq_zero.mp hmul with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hst
      · linarith
    have hA2 : A.2 = B.2 := by
      have hmul : (s - t) * (B.2 - A.2) = 0 := by linarith
      rcases mul_eq_zero.mp hmul with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hst
      · linarith
    exact hne (Prod.ext hA1 hA2)
  have hL := isLine_of_injOn hp (by norm_num : (0 : ℝ) < 1) hi
  have h0 : segmentMap A B 0 = A := Prod.ext (by dsimp [segmentMap]; ring) (by dsimp [segmentMap]; ring)
  have h1 : segmentMap A B 1 = B := Prod.ext (by dsimp [segmentMap]; ring) (by dsimp [segmentMap]; ring)
  rwa [h0, h1] at hL

/-! ## 2. Planarity of `K_4` and the triangle `K_3` -/

/-- Coordinates in `ℝ × ℝ` for the four vertices of `K_4`: an outer triangle `(0, 0), (3, 0), (0, 3)`
with the fourth vertex at the interior point `(1, 1)`. -/
def k4Point : Fin 4 → ℝ × ℝ
  | 0 => (0, 0)
  | 1 => (3, 0)
  | 2 => (0, 3)
  | 3 => (1, 1)

lemma k4Point_injective : Function.Injective k4Point := by
  intro a b heq
  have h1 : (k4Point a).1 = (k4Point b).1 := congrArg Prod.fst heq
  have h2 : (k4Point a).2 = (k4Point b).2 := congrArg Prod.snd heq
  fin_cases a <;> fin_cases b <;> dsimp [k4Point] at h1 h2 <;>
    first | rfl | (exfalso; linarith)

/-- The straight-line segment assigned to an unordered pair of vertices of `K_4`. -/
def k4Line : Sym2 (Fin 4) → Set (ℝ × ℝ) :=
  Sym2.lift ⟨fun a b => straightSegment (k4Point a) (k4Point b),
    fun a b => straightSegment_symm (k4Point a) (k4Point b)⟩

@[simp]
lemma k4Line_mk (a b : Fin 4) :
    k4Line s(a, b) = straightSegment (k4Point a) (k4Point b) :=
  rfl

lemma k4Line_vertex {a b v : Fin 4} (hab : a ≠ b)
    (hv : k4Point v ∈ straightSegment (k4Point a) (k4Point b)) :
    v = a ∨ v = b := by
  rcases hv with ⟨t, ⟨ht0, ht1⟩, hpt⟩
  have h1 : (1 - t) * (k4Point a).1 + t * (k4Point b).1 = (k4Point v).1 :=
    congrArg Prod.fst hpt
  have h2 : (1 - t) * (k4Point a).2 + t * (k4Point b).2 = (k4Point v).2 :=
    congrArg Prod.snd hpt
  fin_cases a <;> fin_cases b <;> fin_cases v <;>
    first
    | exact absurd rfl hab
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (dsimp [k4Point] at h1 h2; exfalso; linarith)

lemma k4Line_inter {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) (hne : s(a, b) ≠ s(c, d))
    {x : ℝ × ℝ} (hx : x ∈ straightSegment (k4Point a) (k4Point b) ∩
      straightSegment (k4Point c) (k4Point d)) :
    x ∈ k4Point '' (univ : Set (Fin 4)) := by
  rcases hx.1 with ⟨t, ⟨ht0, ht1⟩, hpt⟩
  rcases hx.2 with ⟨u, ⟨hu0, hu1⟩, hpu⟩
  have ht1' : (1 - t) * (k4Point a).1 + t * (k4Point b).1 = x.1 := congrArg Prod.fst hpt
  have ht2' : (1 - t) * (k4Point a).2 + t * (k4Point b).2 = x.2 := congrArg Prod.snd hpt
  have hu1' : (1 - u) * (k4Point c).1 + u * (k4Point d).1 = x.1 := congrArg Prod.fst hpu
  have hu2' : (1 - u) * (k4Point c).2 + u * (k4Point d).2 = x.2 := congrArg Prod.snd hpu
  suffices h : x = k4Point 0 ∨ x = k4Point 1 ∨ x = k4Point 2 ∨ x = k4Point 3 by
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨0, mem_univ _, rfl⟩
    · exact ⟨1, mem_univ _, rfl⟩
    · exact ⟨2, mem_univ _, rfl⟩
    · exact ⟨3, mem_univ _, rfl⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    first
    | exact absurd (by decide) hab
    | exact absurd (by decide) hcd
    | exact absurd (by decide) hne
    | (dsimp [k4Point] at ht1' ht2' hu1' hu2'; exfalso; linarith)
    | (dsimp [k4Point] at ht1' ht2' hu1' hu2' ⊢;
       first
       | (left; exact Prod.ext (by linarith) (by linarith))
       | (right; left; exact Prod.ext (by linarith) (by linarith))
       | (right; right; left; exact Prod.ext (by linarith) (by linarith))
       | (right; right; right; exact Prod.ext (by linarith) (by linarith)))

/-- The complete graph on four vertices `K_4` is planar. -/
theorem isPlanar_completeGraph_four : IsPlanar (completeGraph 4) := by
  apply IsPlanar.of_plane_openEmbedding
  intro S _ _ j hj
  obtain ⟨Γ, _, _, _⟩ := exists_graphDrawing_of_embedded_lines
    (completeGraph 4) (Set.toFinite _) (Set.toFinite _)
    k4Point k4Point_injective.injOn k4Line
    (fun _ _ hLoop => hLoop.1 rfl)
    (fun e _ a b hLink => by
      rcases hLink with ⟨hab, rfl⟩
      rw [k4Line_mk]
      exact straightSegment_isLine (fun heq => hab (k4Point_injective heq)))
    (fun e he v _ hv => by
      rcases he with ⟨a, b, hab, rfl⟩
      rw [k4Line_mk] at hv
      rcases k4Line_vertex hab hv with rfl | rfl
      · exact ⟨b, hab, rfl⟩
      · exact ⟨a, hab.symm, Sym2.eq_swap⟩)
    (fun e he d hd hne _ hx => by
      rcases he with ⟨a, b, hab, rfl⟩
      rcases hd with ⟨c, dst, hcd, rfl⟩
      exact k4Line_inter hab hcd hne hx)
    j hj.isEmbedding
  exact ⟨Γ⟩

/-- Coordinates in `ℝ × ℝ` for the three vertices of the triangle `K_3`. -/
def k3Point (i : Fin 3) : ℝ × ℝ :=
  k4Point i.castSucc

lemma k3Point_injective : Function.Injective k3Point :=
  k4Point_injective.comp (Fin.castSucc_injective 3)

/-- The straight-line segment assigned to an edge of `K_3`. -/
def k3Line (e : Sym2 (Fin 3)) : Set (ℝ × ℝ) :=
  k4Line (Sym2.map Fin.castSucc e)

/-- The triangle `completeGraph 3` is planar. -/
theorem isPlanar_completeGraph_three : IsPlanar (completeGraph 3) := by
  apply IsPlanar.of_plane_openEmbedding
  intro S _ _ j hj
  obtain ⟨Γ, _, _, _⟩ := exists_graphDrawing_of_embedded_lines
    (completeGraph 3) (Set.toFinite _) (Set.toFinite _)
    k3Point k3Point_injective.injOn k3Line
    (fun _ _ hLoop => hLoop.1 rfl)
    (fun e _ a b hLink => by
      rcases hLink with ⟨hab, rfl⟩
      change IsLineWithEnds (k4Line s(a.castSucc, b.castSucc))
        (k4Point a.castSucc) (k4Point b.castSucc)
      rw [k4Line_mk]
      exact straightSegment_isLine (fun heq => hab (k3Point_injective heq)))
    (fun e he v _ hv => by
      rcases he with ⟨a, b, hab, rfl⟩
      have hab' : a.castSucc ≠ b.castSucc :=
        fun heq => hab (Fin.castSucc_injective 3 heq)
      change k4Point v.castSucc ∈ straightSegment (k4Point a.castSucc) (k4Point b.castSucc) at hv
      rcases k4Line_vertex hab' hv with h1 | h1
      · have hva : v = a := Fin.castSucc_injective 3 h1
        subst hva
        exact ⟨b, hab, rfl⟩
      · have hvb : v = b := Fin.castSucc_injective 3 h1
        subst hvb
        exact ⟨a, hab.symm, Sym2.eq_swap⟩)
    (fun e he d hd hne x hx => by
      rcases he with ⟨a, b, hab, rfl⟩
      rcases hd with ⟨c, dst, hcd, rfl⟩
      have hab' : a.castSucc ≠ b.castSucc :=
        fun heq => hab (Fin.castSucc_injective 3 heq)
      have hcd' : c.castSucc ≠ dst.castSucc :=
        fun heq => hcd (Fin.castSucc_injective 3 heq)
      have hne' : s(a.castSucc, b.castSucc) ≠ s(c.castSucc, dst.castSucc) := by
        intro heq
        exact hne ((Sym2.map.injective (Fin.castSucc_injective 3)) heq)
      have hx1 : x ∈ straightSegment (k4Point a.castSucc) (k4Point b.castSucc) := hx.1
      have hx2 : x ∈ straightSegment (k4Point c.castSucc) (k4Point dst.castSucc) := hx.2
      have hmem := k4Line_inter hab' hcd' hne' ⟨hx1, hx2⟩
      rcases hmem with ⟨w, _, rfl⟩
      have hw : w = a.castSucc ∨ w = b.castSucc := k4Line_vertex hab' hx1
      rcases hw with rfl | rfl
      · exact ⟨a, mem_univ _, rfl⟩
      · exact ⟨b, mem_univ _, rfl⟩)
    j hj.isEmbedding
  exact ⟨Γ⟩

/-! ## 3. Planarity of the elementary wall of each height -/

/-- The elementary wall `elementaryWall h` of any height `h : ℕ` is planar. -/
theorem isPlanar_elementaryWall (h : ℕ) : IsPlanar (elementaryWall h) :=
  GM13.isPlanar_elementaryWall h

end GraphMinor.Planar.Examples
