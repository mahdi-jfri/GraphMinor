module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.Compute.GM06WalkDartEncoding
import Mathlib.Data.List.Chain

/-!
# Numeric chains along current linkage rows

For the path-side transitions in Lemma 10 of VI (5.7), page 133,
the head origin of each word is the tail origin of the next. The
first tail is the prescribed source slot. Injectivity is used only
at active endpoint slots, so deleted vertex slots may retain any
point value.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

private theorem encoded_tail_live {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ))
    (A : Set (Fin n))
    (hlive : ∀ j : Fin tagged.length, tagged[j].2 = 1 → tagged[j].1.1 ∈ A ∧ tagged[j].1.2 ∈ A)
    {d : ℕ} (hd : d < 2 * tagged.length) (ha : (tagged[d / 2]'(by omega)).2 = 1) :
    gm06DartTail tagged ⟨d, hd⟩ ∈ A := by
  have hh := hlive ⟨d / 2, by omega⟩ ha
  simp only [Fin.getElem_fin] at hh
  unfold gm06DartTail
  split_ifs
  · exact hh.1
  · exact hh.2

private theorem encoded_head_live {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ))
    (A : Set (Fin n))
    (hlive : ∀ j : Fin tagged.length, tagged[j].2 = 1 → tagged[j].1.1 ∈ A ∧ tagged[j].1.2 ∈ A)
    {d : ℕ} (hd : d < 2 * tagged.length) (ha : (tagged[d / 2]'(by omega)).2 = 1) :
    gm06DartHead tagged ⟨d, hd⟩ ∈ A := by
  have hh := hlive ⟨d / 2, by omega⟩ ha
  simp only [Fin.getElem_fin] at hh
  unfold gm06DartHead
  split_ifs
  · exact hh.2
  · exact hh.1

/-- Consecutive words of an encoded walk share exactly the same
numeric endpoint label when active endpoint labels are injective. -/
theorem walk_encoding_origin_chain {n : ℕ} {α β : Type*} {Gr : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α}
    {edge : Fin tagged.length → β} {s t : α} {W : GraphWalk Gr s t} {row : List ℕ}
    (henc : GM06WalkDartEncoding Gr tagged vertex edge W row) (A : Set (Fin n))
    (hinj : InjOn vertex A)
    (hlive : ∀ j : Fin tagged.length, tagged[j].2 = 1 → tagged[j].1.1 ∈ A ∧ tagged[j].1.2 ∈ A) :
    let origins := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
    List.IsChain (fun d e => origins[gm06DartMate d]?.getD 0 = origins[e]?.getD 0) row := by
  dsimp only
  induction henc with
  | nil => exact .nil
  | @cons x y z e hl R rest d hd hactive hedge htail hhead hrest ih =>
    cases hrest with
    | nil => exact .singleton _
    | @cons y w z f hlink S tail d' hd' hactive' hedge' htail' hhead' hrest' =>
      apply List.isChain_cons_cons.mpr
      refine ⟨?_, ih⟩
      have heq := hinj (encoded_head_live tagged A hlive hd hactive)
        (encoded_tail_live tagged A hlive hd' hactive') (hhead.trans htail'.symm)
      rw [(gm06Dart_endpoint_words tagged ⟨d, hd⟩).2,
        (gm06Dart_endpoint_words tagged ⟨d', hd'⟩).1]
      exact congrArg Fin.val heq

/-- The first numeric source of an encoded walk is its prescribed
live source label, without any injectivity requirement on retired slots. -/
theorem walk_encoding_first_source_live {n : ℕ} {α β : Type*} {Gr : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α}
    {edge : Fin tagged.length → β} {s t : α} {W : GraphWalk Gr s t}
    {d : ℕ} {rest : List ℕ} (henc : GM06WalkDartEncoding Gr tagged vertex edge W (d :: rest))
    (A : Set (Fin n)) (hinj : InjOn vertex A)
    (hlive : ∀ j : Fin tagged.length, tagged[j].2 = 1 → tagged[j].1.1 ∈ A ∧ tagged[j].1.2 ∈ A)
    (a : Fin n) (ha : a ∈ A) (hpoint : vertex a = s) :
    (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[d]?.getD 0 = a.val := by
  cases henc with
  | cons hd hactive hedge htail hhead hrest =>
    rw [(gm06Dart_endpoint_words tagged ⟨d, hd⟩).1]
    exact congrArg Fin.val (hinj (encoded_tail_live tagged A hlive hd hactive) ha
      (htail.trans hpoint.symm))

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- Every actual current linkage row chains its stored numeric
heads to the next stored numeric tails. -/
theorem linkage_origin_chain (i : Fin k) :
    List.IsChain (fun d e => x.endpoints[gm06DartMate d]?.getD 0 = x.endpoints[e]?.getD 0)
      (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) := by
  obtain ⟨W, _, henc, _⟩ := rep.linkage.path i
  rw [rep.endpoints]
  exact walk_encoding_origin_chain henc (↑rep.live) rep.vertex_inj rep.ends_live

/-- The first word of an actual current linkage row starts at
its prescribed permanent source slot. -/
theorem linkage_first_origin (i : Fin k) (d : ℕ) (rest : List ℕ)
    (hrow : (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)) = d :: rest) :
    x.endpoints[d]?.getD 0 = (rep.source i).val := by
  obtain ⟨W, _, henc, _⟩ := rep.linkage.path i
  rw [hrow] at henc
  rw [rep.endpoints]
  exact walk_encoding_first_source_live henc (↑rep.live) rep.vertex_inj rep.ends_live
    (rep.source i) (rep.source_live i) (rep.source_point i)

end GM06CurrentDrawingRep
end GraphMinor.GM06
