module

public import GraphMinor.GM06.Section5PolarRotationRow
public import GraphMinor.GM06.Section5HalfEdgeLabels

/-!
# Exact edge incidence in a polar rotation row

The geometric row used in VI (5.7), page 133, is labelled by the
consecutive endpoint-array positions. An edge point on the polar
rim is represented by exactly one of the two positions for that
edge. This follows from disjointness of drawing edges and the
bijection between incident directed ends and rim directions.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A rotation row labelled by the actual directed ends represents
each edge by its two consecutive array positions, also for loops. -/
theorem polar_rotation_row_edge_labels
    {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (d : halfEdges Γ γ v ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).1) ∈ range (spoke γ a.1))
    {m : ℕ} (edge : Fin m ≃ Γ.E) (xs : List ℕ) (z : ℕ → Circle)
    (hmem : ∀ r, r ∈ xs ↔ ∃ a : halfEdges Γ γ v, halfEdgeLabel edge a = r)
    (hz : ∀ a, z (halfEdgeLabel edge a) = (d a).1) (j : Fin m) (w : Circle) :
    polarRimMap Φ w ∈ (edge j).1 ↔ ∃ r ∈ xs, z r = w ∧
      (r = 2 * j.val ∨ r = 2 * j.val + 1) := by
  have hpoint (a : halfEdges Γ γ v) : polarRimMap Φ (d a).1 ∈ a.1.1 :=
    polar_rim_mem_edge_of_halfedge_ray hγ hp a (d a).1 (hd a)
  constructor
  · intro hw
    obtain ⟨a, ha⟩ := d.surjective ⟨w, (edge j).1, (edge j).2, hw⟩
    have haw : (d a).1 = w := congrArg Subtype.val ha
    have he : a.1.1 = (edge j).1 := Γ.edge_eq_of_mem a.2.1 (edge j).2
      (hpoint a) (haw.symm ▸ hw)
    have hquot := (halfEdgeLabel_edge_iff edge a j).mp he
    have hrem := Nat.mod_lt (halfEdgeLabel edge a) (by decide : 0 < 2)
    refine ⟨halfEdgeLabel edge a, (hmem _).mpr ⟨a, rfl⟩, (hz a).trans haw, ?_⟩
    omega
  · rintro ⟨r, hr, hrw, hrId⟩
    obtain ⟨a, har⟩ := (hmem r).mp hr
    have haw : (d a).1 = w := (hz a).symm.trans (har.symm ▸ hrw)
    have hquot : halfEdgeLabel edge a / 2 = j.val := by
      rw [har]
      rcases hrId with h | h <;> rw [h] <;> omega
    have he := (halfEdgeLabel_edge_iff edge a j).mpr hquot
    rw [← he, ← haw]
    exact hpoint a

/-- Every geometric rim labelling admits a finite rotation row with
valid endpoint-array positions and exact edge incidence. -/
theorem exists_polar_rotation_row_with_endpoint_labels
    {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (d : halfEdges Γ γ v ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).1) ∈ range (spoke γ a.1))
    {m : ℕ} (edge : Fin m ≃ Γ.E) :
    ∃ (xs : List ℕ) (z : ℕ → Circle), xs.Nodup ∧
      (∀ r ∈ xs, r < 2 * m) ∧ Set.InjOn z {r | r ∈ xs} ∧
      xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)) ∧
      (∀ w : Circle, (∃ e ∈ Γ.E, polarRimMap Φ w ∈ e) ↔ ∃ r ∈ xs, z r = w) ∧
      ∀ (j : Fin m) (w : Circle), polarRimMap Φ w ∈ (edge j).1 ↔
        ∃ r ∈ xs, z r = w ∧ (r = 2 * j.val ∨ r = 2 * j.val + 1) := by
  obtain ⟨xs, z, hnd, hmem, hz, hzi, hs, hcover⟩ :=
    exists_polar_rotation_row d (halfEdgeLabel edge) (halfEdgeLabel_injective edge)
  refine ⟨xs, z, hnd, ?_, hzi, hs, hcover, ?_⟩
  · intro r hr
    obtain ⟨a, rfl⟩ := (hmem r).mp hr
    exact halfEdgeLabel_lt edge a
  · exact polar_rotation_row_edge_labels hγ hp d hd edge xs z hmem hz

end GraphMinor.GM06
