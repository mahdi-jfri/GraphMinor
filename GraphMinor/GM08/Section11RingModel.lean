module

public import GraphMinor.GM08.Section11Model
public import GraphMinor.GM08.Section11Transport
public import GraphMinor.GM08.Section4

/-!
# The simulation inside one ring

In the proof of Graph Minors VIII, (11.2) a ring cell `Σ_i \ N` of the first portrait, labelled by
the part `(G_i, ψ_i)` of `(G_1, τ_1)` in `Σ_i`, is sent to a ring cell of the second portrait,
labelled by a part `(G'_j, ψ'_j)` of `(G_2, τ_2)`. The labels satisfy `(G_i, ψ_i) ≤ (G'_j, ψ'_j)`,
so `(G_i, ψ_i)` is simulated in `(G'_j, ψ'_j)`. Here this simulation is moved to the parts of the
drawings `Γ_1` and `Γ_2` in `Σ_i` and `Σ'_j` (`exists_ring_model`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface Graph

universe u u' v'

variable {S : Type u} [TopologicalSpace S]

/-- The part of a drawing `Γ` in the disc of an O-arc `F`: the vertices in the disc and the edges
inside `F`. -/
@[expose] def ringGraph (Γ : Drawing S) (F : Set S) : Graph S (Set S) :=
  (Γ.toGraph.induce (Γ.V ∩ (F ∪ insideSet F))).restrict (edgesInsideOArc Γ univ F)

variable {Γ : Drawing S} {F : Set S}

theorem ringGraph_le : ringGraph Γ F ≤ Γ.toGraph :=
  restrict_le.trans (induce_le inter_subset_left)

theorem ringGraph_V : V(ringGraph Γ F) = Γ.V ∩ (F ∪ insideSet F) := rfl

theorem ringGraph_E (hS : IsClosedDisc (univ : Set S)) (hF : IsOArc F) :
    E(ringGraph Γ F) = edgesInsideOArc Γ univ F := by
  ext e
  constructor
  · exact fun h => h.2
  · intro he
    refine ⟨?_, he⟩
    obtain ⟨x, y, hl⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet he.1
    have hcl := closure_subset_ring hS hF (e := e) he.2
    have hx : x ∈ closure e ∩ Γ.V := by
      rw [hl.2.2.2]
      exact mem_insert x {y}
    have hy : y ∈ closure e ∩ Γ.V := by
      rw [hl.2.2.2]
      exact mem_insert_of_mem x rfl
    exact ⟨x, y, hl, ⟨hx.2, hcl hx.1⟩, ⟨hy.2, hcl hy.1⟩⟩

variable {α : Type u'} {β : Type v'}

/-- The isomorphism of a graft drawing restricts to a bijection from the part `R` of `(G, τ)` in
the disc of `F` to the part of the drawing there. -/
theorem IsRingGraph.isGraphBij [Nonempty S] (hS : IsClosedDisc (univ : Set S)) (hF : IsOArc F)
    {X : RootedGraph α β} {gd : GraftDrawing X.G X.toGraft.T S} {R : RootedGraph α β}
    {μ : List S} (h : IsRingGraph X gd F R μ) :
    IsGraphBij R.G (ringGraph gd.drawing F) gd.iso.fv gd.iso.fe := by
  obtain ⟨hle, hV, hE, -⟩ := h
  refine (gd.iso.isGraphBij).restrict hle ringGraph_le (fun v hv => ?_) (fun e he => ?_)
  · rw [hV, ringGraph_V, Iso.fv_of_mem hv]
    exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨hv, hx⟩⟩
  · rw [hE, ringGraph_E hS hF, Iso.fe_of_mem he]
    exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨he, hx⟩⟩

/-- The roots of a part `R` are drawn at the list `μ`. -/
theorem IsRingGraph.fv_root {X : RootedGraph α β} {gd : GraftDrawing X.G X.toGraft.T S}
    {R : RootedGraph α β} {μ : List S} (h : IsRingGraph X gd F R μ) [Nonempty S] {n : ℕ}
    (hn : n < R.τ.length) (hn' : n < μ.length) : gd.iso.fv R.τ[n] = μ[n] := by
  obtain ⟨hv, hr⟩ := h.2.2.2.2.2.2 n hn hn'
  rw [Iso.fv_of_mem hv, hr]

/-- **The simulation inside a ring.** A simulation of the part of `(G_1, τ_1)` in the disc of
`F_1` in the part of `(G_2, τ_2)` in the disc of `F_2` gives a simulation of the part of `Γ_1` in
the part of `Γ_2` that sends the roots `μ_1` to the roots `μ_2`. -/
theorem exists_ring_model [Nonempty S] (hS : IsClosedDisc (univ : Set S)) {F₁ F₂ : Set S}
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) {X₁ X₂ : RootedGraph α β}
    {gd₁ : GraftDrawing X₁.G X₁.toGraft.T S} {gd₂ : GraftDrawing X₂.G X₂.toGraft.T S}
    {Y₁ Y₂ : RootedGraph α β} {μ₁ μ₂ : List S} (h₁ : IsRingGraph X₁ gd₁ F₁ Y₁ μ₁)
    (h₂ : IsRingGraph X₂ gd₂ F₂ Y₂ μ₂) (hsim : IsRootedGraphSimulatedIn Y₁ Y₂) :
    ∃ (ηR : S → Set S) (εR : Set S → Set S),
      IsMinorModel (ringGraph gd₁.drawing F₁) (ringGraph gd₂.drawing F₂) ηR εR ∧
      μ₁.length = μ₂.length ∧
      ∀ (n : ℕ) (hn₁ : n < μ₁.length) (hn₂ : n < μ₂.length), μ₂[n] ∈ ηR μ₁[n] := by
  obtain ⟨ηy, εy, hsimG, hlen, hroot, -⟩ := hsim
  have b₁ := h₁.isGraphBij hS hF₁
  have b₂ := h₂.isGraphBij hS hF₂
  have m := (isGraphSimulation_comp hsimG b₂.isMinorModel).pushGuest b₁
  have hl₁ : Y₁.τ.length = μ₁.length := h₁.2.2.2.2.2.1
  have hl₂ : Y₂.τ.length = μ₂.length := h₂.2.2.2.2.2.1
  refine ⟨_, _, m, by omega, fun n hn₁ hn₂ => ?_⟩
  have hy₁ : n < Y₁.τ.length := by omega
  have hy₂ : n < Y₂.τ.length := by omega
  have hr := hroot ⟨n, hy₂⟩
  simp only [Fin.getElem_fin, Fin.val_cast] at hr
  refine ⟨Y₁.τ[n], Y₁.τ_subset _ (List.getElem_mem _), h₁.fv_root hy₁ hn₁, ?_⟩
  exact mem_biUnion hr (by rw [h₂.fv_root hy₂ hn₂]; exact mem_singleton _)

end GM08
end GraphMinor
