module

public import GraphMinor.GM11.Rotation
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM16.TangentDisc
import GraphMinor.GM11.PlaneFacts
import GraphMinor.GM11.Section4c
import GraphMinor.GM11.Corners
import GraphMinor.Surface.DiscGrow

/-!
# Empty sectors for the cellular drawing in VIII, Section 12

The drawing used to derive a portrait may be chosen cellular. To move
its loops into empty small petals, first find a disc touching the
drawing only at their common vertex. The rotation sectors provide an
empty sector inside an old loop disc. A small tangent disc in that
sector stays inside the old disc and avoids the drawing except at the
vertex. This fills a local step in the cellular drawing construction.
-/

public section

namespace GraphMinor.GM08

open Set Surface Topology GM11

universe u

/-- An empty small disc at a vertex, inside a disc bounded by the
drawing. This is the local room needed to redraw the loops cellularly
before deriving the portraits in VIII, Section 12, page 274. -/
theorem exists_empty_tangent_disc {S : Type u} [TopologicalSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {γ : Set S → unitInterval → S}
    (hγ : EdgePar Γ γ) {v : S} (hv : v ∈ Γ.V)
    (h2 : 2 ≤ Nat.card (halfEdges Γ γ v))
    {K O : Set S} (hK : IsClosedDisc K) (hvK : v ∈ discBd K)
    (hKΓ : discBd K ⊆ Γ.U) (hO : IsOpen O) (hvO : v ∈ O) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ K ∧ E ⊆ O ∧
      v ∈ discBd E ∧ E ∩ Γ.U = {v} := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨next, P, W, Q, hW, hvW, _, _, _, hPc, hPd, _, hcover, _, hQ, _, _, _, _⟩ :=
    exists_rotation_sectors hS Γ hγ hv h2
  have hvcl : v ∈ closure (discInt K) := hK.subset_closure_discInt (Surface.discBd_subset K hvK)
  obtain ⟨q, hqW, hqK⟩ := mem_closure_iff.mp hvcl W hW hvW
  obtain ⟨q, ⟨hqW, hqK⟩, hqΓ⟩ := exists_notMem_U (Γ := Γ) hS
    (hW.inter (hK.isOpen_discInt hman)) ⟨q, hqW, hqK⟩
  obtain ⟨k, hqP⟩ := mem_iUnion.mp (hcover ⟨hqW, hqΓ⟩)
  have hPside : P k ⊆ discInt K := by
    have hd : Disjoint (discInt K) Kᶜ := disjoint_left.mpr fun x hx hn => hn hx.1
    have hc : P k ⊆ discInt K ∪ Kᶜ := by
      intro x hx
      by_cases hxK : x ∈ K
      · exact .inl ⟨hxK, fun hxBd => disjoint_left.mp (hPd k) hx (hKΓ hxBd)⟩
      · exact .inr hxK
    rcases (hPc k).subset_or_subset (hK.isOpen_discInt hman) hK.isClosed.isOpen_compl hd hc with hin | hout
    · exact hin
    · exact False.elim (hout hqP hqK.1)
  obtain ⟨E, hE, hEQ, hEO, hvE, hEQbd⟩ := GM16.exists_tangent_disc
    (hQ k).1 (hW.inter hO) (hQ k).2.1 ⟨hvW, hvO⟩
  have hinside : ∀ x ∈ E, x ≠ v → x ∈ P k := by
    intro x hx hxv
    apply (hQ k).2.2.2
    refine ⟨⟨(hEO hx).1, hEQ hx⟩, ?_⟩
    intro hxBd
    exact hxv (mem_singleton_iff.mp (hEQbd ▸ And.intro hx hxBd))
  refine ⟨E, hE, ?_, fun x hx => (hEO hx).2, hvE, ?_⟩
  · intro x hx
    by_cases hxv : x = v
    · exact hxv ▸ Surface.discBd_subset K hvK
    · exact (hPside (hinside x hx hxv)).1
  · ext x
    constructor
    · rintro ⟨hxE, hxΓ⟩
      by_contra hxv
      exact disjoint_left.mp (hPd k) (hinside x hxE (by simpa using hxv)) hxΓ
    · rintro rfl
      exact ⟨Surface.discBd_subset E hvE, Γ.V_subset_U hv⟩

/-- A loop supplies two half-edges at its end, so the empty-sector
construction applies there. The disc `K` is the inside of that loop
in the original disc drawing of VIII, Section 12. -/
theorem exists_empty_disc_at_loop {S : Type u} [TopologicalSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E)
    {v : S} (hcap : closure e ∩ Γ.V = {v})
    {K O : Set S} (hK : IsClosedDisc K) (hbd : discBd K = closure e)
    (hO : IsOpen O) (hvO : v ∈ O) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ K ∧ E ⊆ O ∧
      v ∈ discBd E ∧ E ∩ Γ.U = {v} := by
  classical
  have : T2Space S := hS.2.1
  have hvpair : v ∈ closure e ∩ Γ.V := hcap.symm ▸ mem_singleton v
  have : Nonempty S := ⟨v⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  have hend : ∀ b, γ e (endOf b) = v := fun b =>
    mem_singleton_iff.mp (hcap ▸ And.intro (end_mem_closure hγ he b) (end_mem_V hγ he b))
  have h2 : 2 ≤ Nat.card (halfEdges Γ γ v) := by
    rw [Nat.card_coe_set_eq]
    apply Nat.succ_le_of_lt
    apply (one_lt_ncard (finite_halfEdges Γ γ v)).mpr
    refine ⟨(e, false), ⟨he, hend false⟩, (e, true), ⟨he, hend true⟩, ?_⟩
    intro h
    have := congrArg Prod.snd h
    cases this
  apply exists_empty_tangent_disc hS Γ hγ hvpair.2 h2 hK
  · rw [hbd]
    exact hvpair.1
  · rw [hbd]
    exact Γ.closure_subset_U he
  · exact hO
  · exact hvO

end GraphMinor.GM08
