module

public import GraphMinor.GM07.Defs
public import GraphMinor.GM07.CutStages
import GraphMinor.GM07.Section46PullGraph
import GraphMinor.GM11.RadialChord
import GraphMinor.GM08.Section18CutCardinality
import Mathlib.Data.Set.Card.Arithmetic

/-!
# The drawing and root count after an arc cut

A proper arc is a one-edge drawing, so the graph pullback theorem applies
to a normal arc cut. Off the arc each vertex has one lift. On the arc it
has two. The new boundary vertices therefore number at most the old
boundary vertices plus twice the vertices on the arc. This is the index
bound for the disc graft used in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- Pull a proper drawing across a normal proper arc cut, as required
when opening the short tubes in VIII (15.4), page 282. -/
theorem exists_pullback_drawing_of_normal_arc {S Y : Type w}
    [TopologicalSpace S] [TopologicalSpace Y] (hS : IsSurface S)
    {F : Set S} {u v : S} (huv : u ≠ v) (hF : IsLineWithEnds F u v)
    (hbd : F ∩ bd S ⊆ {u, v}) {ψ : Y → S}
    (hcut : GM07.IsCutAlongSet F ψ) (G : Drawing S) (hG : G.IsProper)
    (hn : G.IsNormal F) :
    ∃ G' : Drawing Y, GM07.IsPullbackDrawing ψ G G' ∧ G'.IsProper ∧
      ∀ e' ∈ G'.E, ∃ e ∈ G.E, e' = ψ ⁻¹' e := by
  have : T2Space S := hS.2.1
  let K := lineDrawing hF huv
  have hp : K.IsProper := fun x hx => hbd ⟨hx.2, hx.1⟩
  have hno : GM07.HasNoIsolatedVertices K := by
    intro x hx
    have he : F \ {u, v} ∈ K.E := by rw [lineDrawing_E]; exact rfl
    refine ⟨F \ {u, v}, he, hx, Or.inl he, ?_⟩
    rw [closure_sdiff_pair hF]
    exact K.V_subset_U hx
  exact GM07.exists_pullback_graph hS (hcut.isCutAlongGraph hp hno) hG hn

private theorem ncard_preimage_le_of_fibre_bound {A B : Type*} {f : A → B}
    {V : Set B} (hV : V.Finite) (n : ℕ)
    (h : ∀ v ∈ V, (f ⁻¹' {v}).ncard ≤ n) :
    (f ⁻¹' V).ncard ≤ V.ncard * n := by
  induction V, hV using Set.Finite.induction_on with
  | empty => simp
  | @insert v V hv hV ih =>
    have hins : f ⁻¹' insert v V = f ⁻¹' {v} ∪ f ⁻¹' V := by ext x; simp
    rw [hins, ncard_insert_of_notMem hv hV, add_mul, one_mul, add_comm]
    exact (ncard_union_le _ _).trans
      (Nat.add_le_add (h v (mem_insert v V))
        (ih fun w hw => h w (mem_insert_of_mem v hw)))

/-- Cutting along a normal arc adds at most twice its vertex count to
the number of boundary vertices. This is the index estimate in the
short-tube step of VIII (15.4), page 282. -/
theorem boundary_vertices_ncard_le_of_arc_cut {S Y : Type w}
    [TopologicalSpace S] [TopologicalSpace Y] {F V : Set S}
    (hV : V.Finite) {ψ : Y → S} (hcut : GM07.IsCutAlongSet F ψ)
    (hc : IsCutting ψ F) :
    (ψ ⁻¹' V ∩ bd Y).ncard ≤ (V ∩ bd S).ncard + 2 * (V ∩ F).ncard := by
  have hpre : ψ ⁻¹' V ∩ bd Y = ψ ⁻¹' (V ∩ (bd S ∪ F)) := by
    rw [← hcut.preimage_bd, ← preimage_inter]
  have hinter : (V ∩ (bd S ∪ F)) ∩ F = V ∩ F := by ext x; simp only [mem_inter_iff, mem_union]; tauto
  have hoff : (V ∩ (bd S ∪ F)) \ F ⊆ V ∩ bd S := by
    rintro x ⟨⟨hxV, hxB | hxF⟩, hn⟩
    · exact ⟨hxV, hxB⟩
    · exact (hn hxF).elim
  have hcutcount : (ψ ⁻¹' (V ∩ F)).ncard ≤ (V ∩ F).ncard * 2 :=
    ncard_preimage_le_of_fibre_bound (hV.subset inter_subset_left) 2
      (fun v hv => (hc.2.2.2.1 v hv.2).le)
  rw [hpre, cutMap_ncard_preimage_eq (GM19.IsCutting.isCutMap hc)
    (hV.subset inter_subset_left), hinter]
  have hn := ncard_le_ncard hoff (hV.subset inter_subset_left)
  simpa only [Nat.mul_comm, Nat.add_comm] using Nat.add_le_add hcutcount hn

end GraphMinor.GM08
