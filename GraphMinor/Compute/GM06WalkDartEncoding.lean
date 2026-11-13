module

public import GraphMinor.Compute.GM06DartMate
public import GraphMinor.Compute.GM06RefreshContractedMasks
public import GraphMinor.GM11.Walks
import GraphMinor.Compute.GM06EndpointLookup

/-!
# Directed-word encodings of actual graph walks

The given and returned linkage paths of VI (5.7), page 133, are
lists of directed edge labels. Even and odd labels select the two
orientations of the supplied endpoint pair, including for a loop.
The encoding relation below says exactly which edge and orientation
each word records. It adds no path or feasibility conclusion to the
input data. The elementary equations connect word rows to actual
walk lengths, edges and active labels, and describe endpoint labels
after the contraction's finite substitution.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Surface
universe u v

/-- The source vertex of a directed original edge label. -/
@[expose] def gm06DartTail {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ))
    (d : Fin (2 * tagged.length)) : Fin n :=
  let p := tagged[d.val / 2]'(by omega)
  if d.val % 2 = 0 then p.1.1 else p.1.2

/-- The terminal vertex of a directed original edge label. -/
@[expose] def gm06DartHead {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ))
    (d : Fin (2 * tagged.length)) : Fin n :=
  let p := tagged[d.val / 2]'(by omega)
  if d.val % 2 = 0 then p.1.2 else p.1.1

/-- Each active directed word has the actual link orientation
specified by its two finite endpoint labels. -/
theorem gm06Dart_isLink {n : ℕ} {α : Type u} {β : Type v} (G : Graph α β)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → α)
    (edge : Fin tagged.length → β)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (d : Fin (2 * tagged.length)) (hactive : (tagged[d.val / 2]'(by omega)).2 = 1) :
    G.IsLink (edge ⟨d.val / 2, by omega⟩) (vertex (gm06DartTail tagged d)) (vertex (gm06DartHead tagged d)) := by
  have hh := hlinks ⟨d.val / 2, by omega⟩ hactive
  by_cases h : d.val % 2 = 0
  · simpa only [gm06DartTail, gm06DartHead, h, ite_true, Fin.getElem_fin] using hh
  · simpa only [gm06DartTail, gm06DartHead, h, ite_false, Fin.getElem_fin] using hh.symm

/-- The numeric endpoint-array reads used by the RAM neighbour
query equal the finite tail and head of its directed word. -/
theorem gm06Dart_endpoint_words {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ))
    (d : Fin (2 * tagged.length)) :
    let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
    xs[d.val]?.getD 0 = (gm06DartTail tagged d).val ∧
      xs[gm06DartMate d.val]?.getD 0 = (gm06DartHead tagged d).val := by
  dsimp only
  let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
  let j := d.val / 2
  have hj : j < tagged.length := by dsimp only [j]; omega
  have hlen : xs.length = 2 * tagged.length := by
    simp only [xs, gm06EndpointWords_length, List.length_map]
  have heven : xs[2 * j]?.getD 0 = tagged[j].1.1.val := by
    have hh : 2 * j < xs.length := by omega
    rw [List.getElem?_eq_getElem hh, Option.getD_some]
    rw [gm06EndpointWords_getElem_even, List.getElem_map]
    simpa only [List.length_map] using hj
  have hodd : xs[2 * j + 1]?.getD 0 = tagged[j].1.2.val := by
    have hh : 2 * j + 1 < xs.length := by omega
    rw [List.getElem?_eq_getElem hh, Option.getD_some]
    rw [gm06EndpointWords_getElem_odd, List.getElem_map]
    simpa only [List.length_map] using hj
  by_cases h : d.val % 2 = 0
  · have heq : d.val = 2 * j := by dsimp only [j]; omega
    have hmate : gm06DartMate d.val = 2 * j + 1 := by
      simp only [gm06DartMate, h, ite_true]; omega
    constructor
    · simpa only [gm06DartTail, h, ite_true] using (congrArg (fun r => xs[r]?.getD 0) heq).trans heven
    · simpa only [hmate, gm06DartHead, h, ite_true] using hodd
  · have heq : d.val = 2 * j + 1 := by dsimp only [j]; omega
    have hmate : gm06DartMate d.val = 2 * j := by
      simp only [gm06DartMate, h, ite_false]; omega
    constructor
    · simpa only [gm06DartTail, h, ite_false] using (congrArg (fun r => xs[r]?.getD 0) heq).trans hodd
    · simpa only [hmate, gm06DartHead, h, ite_false] using heven

/-- Relabelling endpoints commutes with reading the source of a
retained original directed-edge word. -/
theorem gm06DartTail_contract {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ))
    (a b : Fin n) (j : ℕ) (d : Fin (2 * tagged.length)) :
    gm06DartTail (gm06ContractTaggedEdges tagged a b j)
      (Fin.cast (congrArg (fun m => 2 * m) (gm06ContractTaggedEdges_length tagged a b j)).symm d) =
      gm06ContractVertexLabel a b (gm06DartTail tagged d) := by
  simp only [gm06DartTail, Fin.val_cast,
    gm06ContractTaggedEdges_getElem tagged a b j (show d.val / 2 < tagged.length by omega)]
  split <;> rfl

/-- Relabelling endpoints commutes with reading the terminal
vertex of a retained original directed-edge word. -/
theorem gm06DartHead_contract {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ))
    (a b : Fin n) (j : ℕ) (d : Fin (2 * tagged.length)) :
    gm06DartHead (gm06ContractTaggedEdges tagged a b j)
      (Fin.cast (congrArg (fun m => 2 * m) (gm06ContractTaggedEdges_length tagged a b j)).symm d) =
      gm06ContractVertexLabel a b (gm06DartHead tagged d) := by
  simp only [gm06DartHead, Fin.val_cast,
    gm06ContractTaggedEdges_getElem tagged a b j (show d.val / 2 < tagged.length by omega)]
  split <;> rfl

/-- A row records a walk precisely when its successive words
name the walk's active edges with their traversed orientations. -/
inductive GM06WalkDartEncoding {n : ℕ} {α : Type u} {β : Type v} (G : Graph α β)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → α)
    (edge : Fin tagged.length → β) : {x y : α} → GraphWalk G x y → List ℕ → Prop where
  | nil {x : α} (hx : x ∈ G.vertexSet) : GM06WalkDartEncoding G tagged vertex edge (.nil hx) []
  | cons {x y z : α} {e : β} {hl : G.IsLink e x y} {R : GraphWalk G y z}
      {row : List ℕ} {d : ℕ} (hd : d < 2 * tagged.length)
      (hactive : (tagged[d / 2]'(by omega)).2 = 1)
      (hedge : edge ⟨d / 2, by omega⟩ = e)
      (htail : vertex (gm06DartTail tagged ⟨d, hd⟩) = x)
      (hhead : vertex (gm06DartHead tagged ⟨d, hd⟩) = y)
      (hrest : GM06WalkDartEncoding G tagged vertex edge R row) :
      GM06WalkDartEncoding G tagged vertex edge (.cons hl R) (d :: row)

namespace GM06WalkDartEncoding

/-- An encoded walk has one row word for each traversed edge. -/
theorem length_eq {n : ℕ} {α : Type u} {β : Type v} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α} {edge : Fin tagged.length → β}
    {x y : α} {W : GraphWalk G x y} {row : List ℕ}
    (h : GM06WalkDartEncoding G tagged vertex edge W row) : row.length = W.edges.length := by
  induction h with
  | nil => rfl
  | cons hd hactive hedge htail hhead hrest ih =>
    simpa only [List.length_cons, GraphWalk.edges_cons] using congrArg (fun n => n + 1) ih

/-- Every word in an encoded walk is an in-range active edge label. -/
theorem active_words {n : ℕ} {α : Type u} {β : Type v} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α} {edge : Fin tagged.length → β}
    {x y : α} {W : GraphWalk G x y} {row : List ℕ}
    (h : GM06WalkDartEncoding G tagged vertex edge W row) :
    ∀ d ∈ row, ∃ hd : d < 2 * tagged.length, (tagged[d / 2]'(by omega)).2 = 1 := by
  induction h with
  | nil => simp
  | @cons x y z e hl R row d hd hactive hedge htail hhead hrest ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hd, hactive⟩
    · exact ih q hq

/-- An actual edge occurs in an encoded walk exactly when one of
the row words names that edge at its original label position. -/
theorem edge_mem_iff {n : ℕ} {α : Type u} {β : Type v} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α} {edge : Fin tagged.length → β}
    {x y : α} {W : GraphWalk G x y} {row : List ℕ}
    (h : GM06WalkDartEncoding G tagged vertex edge W row) (f : β) :
    f ∈ W.edges ↔ ∃ d ∈ row, ∃ hd : d < 2 * tagged.length, edge ⟨d / 2, by omega⟩ = f := by
  induction h with
  | nil => simp
  | @cons x y z e hl R row d hd hactive hedge htail hhead hrest ih =>
    simp only [GraphWalk.edges_cons, List.mem_cons]
    constructor
    · rintro (rfl | hf)
      · exact ⟨d, Or.inl rfl, hd, hedge⟩
      · obtain ⟨q, hq, hqBound, hqEdge⟩ := ih.mp hf
        exact ⟨q, Or.inr hq, hqBound, hqEdge⟩
    · rintro ⟨q, hq, hqBound, hqEdge⟩
      rcases hq with rfl | hq
      · exact Or.inl (hqEdge.symm.trans hedge)
      · exact Or.inr (ih.mpr ⟨q, hq, hqBound, hqEdge⟩)

/-- A nonempty encoded walk starts at the source endpoint of its
first directed word and continues with exactly the remaining row. -/
theorem first_step {n : ℕ} {α : Type u} {β : Type v} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α} {edge : Fin tagged.length → β}
    {x y : α} {W : GraphWalk G x y} {d : ℕ} {row : List ℕ}
    (h : GM06WalkDartEncoding G tagged vertex edge W (d :: row)) :
    ∃ (hd : d < 2 * tagged.length) (z : α) (e : β) (hl : G.IsLink e x z) (R : GraphWalk G z y),
      W = .cons hl R ∧ edge ⟨d / 2, by omega⟩ = e ∧
      vertex (gm06DartTail tagged ⟨d, hd⟩) = x ∧ vertex (gm06DartHead tagged ⟨d, hd⟩) = z ∧
      GM06WalkDartEncoding G tagged vertex edge R row := by
  cases h with
  | cons hd hactive hedge htail hhead hrest => exact ⟨hd, _, _, _, _, rfl, hedge, htail, hhead, hrest⟩

/-- The first endpoint word of an encoded nonempty walk is its
supplied source label, using only the vertex-label injection. -/
theorem first_source_word {n : ℕ} {α : Type u} {β : Type v} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α} {edge : Fin tagged.length → β}
    {x y : α} {W : GraphWalk G x y} {d : ℕ} {row : List ℕ}
    (h : GM06WalkDartEncoding G tagged vertex edge W (d :: row))
    (hinj : Function.Injective vertex) (a : Fin n) (ha : vertex a = x) :
    (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[d]?.getD 0 = a.val := by
  obtain ⟨hd, z, e, hl, R, _, hedge, htail, hhead, hrest⟩ := h.first_step
  have hta : gm06DartTail tagged ⟨d, hd⟩ = a := hinj (htail.trans ha.symm)
  exact (gm06Dart_endpoint_words tagged ⟨d, hd⟩).1.trans (congrArg Fin.val hta)

end GM06WalkDartEncoding
end GraphMinor.Compute
