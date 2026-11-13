module

public import GraphMinor.Compute.GM06WalkDartEncoding
public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM06.Section5Red

/-!
# Recovering encoded walks through an injective graph image

The recovery phase of VI (5.7), page 133, reverses initial-edge
contractions. Away from the retired initial vertex, the collapse is
injective. Each surviving directed word still names an old edge
and its orientation. Lift the words one at a time. Injectivity
identifies the end of one lifted edge with the start of the lifted
suffix. This produces an old encoded walk with exactly the same
words, image support and image edge list. Simplicity follows from
the image support, and prescribed ends follow from injectivity.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11
universe u v u' v'

/-- Lift an encoded walk through a graph image whose vertex map
is injective on the retained vertex set. The assumptions interpret
vertices, labelled edges and their directed endpoints. -/
theorem GM06WalkDartEncoding.exists_image_pullback
    {n n' : ℕ} {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (G : Graph α β) {H : Graph α' β'}
    (tagged : List ((Fin n × Fin n) × ℕ))
    {updated : List ((Fin n' × Fin n') × ℕ)}
    (vertex : Fin n → α) {vertex' : Fin n' → α'}
    (edge : Fin tagged.length → β) {edge' : Fin updated.length → β'}
    (f : α → α') (g : β → β') (D : Set α) (hinj : InjOn f D)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ z ∈ H.vertexSet, ∃ x ∈ D, x ∈ G.vertexSet ∧ f x = z)
    (hword : ∀ (d : ℕ) (hd : d < 2 * updated.length),
      (updated[d / 2]'(by omega)).2 = 1 →
      ∃ hdold : d < 2 * tagged.length,
        (tagged[d / 2]'(by omega)).2 = 1 ∧
        g (edge ⟨d / 2, by omega⟩) = edge' ⟨d / 2, by omega⟩ ∧
        f (vertex (gm06DartTail tagged ⟨d, hdold⟩)) = vertex' (gm06DartTail updated ⟨d, hd⟩) ∧
        f (vertex (gm06DartHead tagged ⟨d, hdold⟩)) = vertex' (gm06DartHead updated ⟨d, hd⟩) ∧
        vertex (gm06DartTail tagged ⟨d, hdold⟩) ∈ D ∧
        vertex (gm06DartHead tagged ⟨d, hdold⟩) ∈ D)
    {x' y' : α'} {W : GraphWalk H x' y'} {row : List ℕ}
    (h : GM06WalkDartEncoding H updated vertex' edge' W row) :
    ∃ x ∈ D, ∃ y ∈ D, ∃ R : GraphWalk G x y,
      GM06WalkDartEncoding G tagged vertex edge R row ∧
      f x = x' ∧ f y = y' ∧ R.support.map f = W.support ∧ R.edges.map g = W.edges ∧
      ∀ z ∈ R.support, z ∈ D := by
  induction h with
  | nil hz =>
    obtain ⟨x, hxD, hx, hfx⟩ := hcover _ hz
    refine ⟨x, hxD, x, hxD, .nil hx, .nil hx, hfx, hfx, ?_, rfl, ?_⟩
    · simp only [GraphWalk.support_nil, List.map_cons, List.map_nil, hfx]
    · intro z hz
      rw [GraphWalk.support_nil, List.mem_singleton] at hz
      exact hz ▸ hxD
  | @cons x' y' z' e' hl S row d hd hactive hedge htail hhead hrest ih =>
    obtain ⟨x, hx, y, hy, R, hR, hfx, hfy, hs, he, hRD⟩ := ih
    obtain ⟨hdold, hflag, hgedge, hftail, hfhead, htailD, hheadD⟩ := hword d hd hactive
    have hxhead : vertex (gm06DartHead tagged ⟨d, hdold⟩) = x :=
      hinj hheadD hx ((hfhead.trans hhead).trans hfx.symm)
    cases hxhead
    have hlold := gm06Dart_isLink G tagged vertex edge hlinks ⟨d, hdold⟩ hflag
    refine ⟨vertex (gm06DartTail tagged ⟨d, hdold⟩), htailD, y, hy,
      .cons hlold R, .cons hdold hflag rfl rfl rfl hR,
      hftail.trans htail, hfy, ?_, ?_, ?_⟩
    · simp only [GraphWalk.support_cons, List.map_cons, hftail, htail, hs]
    · simp only [GraphWalk.edges_cons, List.map_cons, hgedge, hedge, he]
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact htailD
      · exact hRD z hz

/-- The recovered walk is simple if its image walk is simple.
No injectivity is needed for this implication: repetition below
would give repetition in the image support. -/
theorem isSimple_of_mapped_support {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {G : Graph α β} {H : Graph α' β'}
    {x y : α} {x' y' : α'} {R : GraphWalk G x y} {W : GraphWalk H x' y'}
    (f : α → α') (hs : R.support.map f = W.support) (hW : W.IsSimple) : R.IsSimple := by
  change R.support.Nodup
  apply List.Nodup.of_map f
  rw [hs]
  exact hW

/-- Injectivity on the retained vertex set identifies prescribed
old ends of a recovered encoded walk with the image walk's ends. -/
theorem encoded_walk_pullback_endpoints
    {n : ℕ} {α : Type u} {β : Type v} {α' : Type u'} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α}
    {edge : Fin tagged.length → β} {row : List ℕ}
    (f : α → α') (D : Set α) (hinj : InjOn f D)
    {x y s t : α} (hx : x ∈ D) (hy : y ∈ D) (hs : s ∈ D) (ht : t ∈ D)
    (hxs : f x = f s) (hyt : f y = f t)
    (h : ∃ R : GraphWalk G x y, R.IsSimple ∧
      GM06WalkDartEncoding G tagged vertex edge R row) :
    ∃ R : GraphWalk G s t, R.IsSimple ∧ GM06WalkDartEncoding G tagged vertex edge R row := by
  have hxs' : x = s := hinj hx hs hxs
  have hyt' : y = t := hinj hy ht hyt
  cases hxs'
  cases hyt'
  exact h

/-- A simple walk encoded in the actual contracted drawing lifts to
an old simple walk avoiding the initial vertex. Its directed words
are unchanged, including their original edge-label positions. -/
theorem exists_expanded_encoded_walk
    {n k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k}
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex vertex' : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hLive : ∀ x, vertex x ∈ G.V → x ∈ A)
    (a b : Fin n) (ha : a ∈ A) (hab : a ≠ b)
    (hpoint : vertex a = cylinderM1Point k i) (d₀ : Fin tagged.length) (hd₀ : tagged[d₀].2 = 1)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d₀) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure (edge d₀)) (hi : InjOn π (closure (edge d₀))ᶜ)
    (hV : G'.V = π '' G.V)
    (hnew : ∀ x ∈ A.erase b, vertex' x = π (vertex x))
    {s t : ClosedCylinder} (W : GraphWalk G'.toGraph s t) (row : List ℕ)
    (hW : W.IsSimple)
    (henc : GM06WalkDartEncoding G'.toGraph (gm06ContractTaggedEdges tagged a b d₀.val) vertex'
      (fun j => π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d₀.val) j)) W row) :
    ∃ x ∈ G.V \ {cylinderM1Point k i}, ∃ y ∈ G.V \ {cylinderM1Point k i},
      ∃ R : GraphWalk G.toGraph x y, R.IsSimple ∧
        GM06WalkDartEncoding G.toGraph tagged vertex edge R row ∧
        π x = s ∧ π y = t ∧ R.support.map π = W.support ∧ R.edges.map (image π) = W.edges ∧
        ∀ z ∈ R.support, z ∈ G.V \ {cylinderM1Point k i} := by
  let updated := gm06ContractTaggedEdges tagged a b d₀.val
  let D := G.V \ {cylinderM1Point k i}
  let J := induceDrawing G D
  have hJV : J.V = D := induceDrawing_V G sdiff_subset
  have hJi : InjOn π J.U := injOn_deleted_initial_vertex_drawing hval hl hvs hfiber hi
  have hDi : InjOn π D := hJi.mono (by intro x hx; exact J.V_subset_U (hJV.symm ▸ hx))
  have hπs : π (cylinderM1Point k i) = cylinderM1Point k i := by
    have hx : cylinderM1Point k i ∈ closure (edge d₀) :=
      (show cylinderM1Point k i ∈ closure (edge d₀) ∩ G.V from hl.2.2.2.symm ▸ mem_insert _ _).1
    have hx' : cylinderM1Point k i ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hx
    exact hx'
  have hπb : π (vertex b) = cylinderM1Point k i := by
    have hx : vertex b ∈ closure (edge d₀) :=
      (show vertex b ∈ closure (edge d₀) ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
    have hx' : vertex b ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hx
    exact hx'
  have hrelab : ∀ x, π (vertex (gm06ContractVertexLabel a b x)) = π (vertex x) := by
    intro x
    by_cases hx : x = b
    · simp only [gm06ContractVertexLabel, hx, ite_true, hpoint, hπs, hπb]
    · simp only [gm06ContractVertexLabel, hx, ite_false]
  have hlabel : ∀ x ∈ A, vertex' (gm06ContractVertexLabel a b x) = π (vertex x) := by
    intro x hx
    rw [hnew _ (gm06ContractVertexLabel_mem_erase A a b x ha hx hab), hrelab]
  have hcover : ∀ z ∈ G'.V, ∃ x ∈ D, x ∈ G.V ∧ π x = z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hV ▸ hz
    by_cases hxs : x = cylinderM1Point k i
    · refine ⟨vertex b, ⟨hl.right_mem, hvs⟩, hl.right_mem, ?_⟩
      rw [hxs, hπs, hπb]
    · exact ⟨x, ⟨hx, hxs⟩, hx, rfl⟩
  have hword : ∀ (d : ℕ) (hd : d < 2 * updated.length),
      (updated[d / 2]'(by omega)).2 = 1 →
      ∃ hdold : d < 2 * tagged.length,
        (tagged[d / 2]'(by omega)).2 = 1 ∧
        image π (edge ⟨d / 2, by omega⟩) =
          π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d₀.val) ⟨d / 2, by change d / 2 < updated.length; omega⟩) ∧
        π (vertex (gm06DartTail tagged ⟨d, hdold⟩)) = vertex' (gm06DartTail updated ⟨d, hd⟩) ∧
        π (vertex (gm06DartHead tagged ⟨d, hdold⟩)) = vertex' (gm06DartHead updated ⟨d, hd⟩) ∧
        vertex (gm06DartTail tagged ⟨d, hdold⟩) ∈ D ∧ vertex (gm06DartHead tagged ⟨d, hdold⟩) ∈ D := by
    intro d hd hactive
    have hdold : d < 2 * tagged.length := by simpa only [updated, gm06ContractTaggedEdges_length] using hd
    have hj : d / 2 < tagged.length := by omega
    rw [gm06ContractTaggedEdges_getElem tagged a b d₀.val hj] at hactive
    have hne : d / 2 ≠ d₀.val := by intro h; simp only [h, ite_true] at hactive; omega
    have hflag : (tagged[d / 2]'hj).2 = 1 := by simpa only [hne, ite_false] using hactive
    have hlold := gm06Dart_isLink G.toGraph tagged vertex edge hlinks ⟨d, hdold⟩ hflag
    have heNot : edge ⟨d / 2, hj⟩ ≠ edge d₀ := by
      intro heq
      have heindex := hinj hflag hd₀ heq
      exact hne (congrArg Fin.val heindex)
    have hscl := not_mem_closure_edge_of_ne_red3 hval hl hvs hlold.edge_mem heNot
    have htailD : vertex (gm06DartTail tagged ⟨d, hdold⟩) ∈ D := by
      refine ⟨hlold.left_mem, ?_⟩
      intro hs
      have hx : vertex (gm06DartTail tagged ⟨d, hdold⟩) ∈ closure (edge ⟨d / 2, hj⟩) :=
        (show _ ∈ closure _ ∩ G.V from hlold.2.2.2.symm ▸ mem_insert _ _).1
      exact hscl (hs ▸ hx)
    have hheadD : vertex (gm06DartHead tagged ⟨d, hdold⟩) ∈ D := by
      refine ⟨hlold.right_mem, ?_⟩
      intro hs
      have hx : vertex (gm06DartHead tagged ⟨d, hdold⟩) ∈ closure (edge ⟨d / 2, hj⟩) :=
        (show _ ∈ closure _ ∩ G.V from hlold.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
      exact hscl (hs ▸ hx)
    refine ⟨hdold, hflag, rfl, ?_, ?_, htailD, hheadD⟩
    · have heq : gm06DartTail updated ⟨d, hd⟩ = gm06ContractVertexLabel a b (gm06DartTail tagged ⟨d, hdold⟩) := by
        simpa only [Fin.cast_mk] using gm06DartTail_contract tagged a b d₀.val ⟨d, hdold⟩
      rw [heq, hlabel _ (hLive _ hlold.left_mem)]
    · have heq : gm06DartHead updated ⟨d, hd⟩ = gm06ContractVertexLabel a b (gm06DartHead tagged ⟨d, hdold⟩) := by
        simpa only [Fin.cast_mk] using gm06DartHead_contract tagged a b d₀.val ⟨d, hdold⟩
      rw [heq, hlabel _ (hLive _ hlold.right_mem)]
  obtain ⟨x, hx, y, hy, R, hR, hπx, hπy, hs, he, hD⟩ :=
    henc.exists_image_pullback G.toGraph tagged vertex edge π (image π) D hDi hlinks hcover hword
  exact ⟨x, hx, y, hy, R, isSimple_of_mapped_support π hs hW, hR, hπx, hπy, hs, he, hD⟩

end GraphMinor.Compute
