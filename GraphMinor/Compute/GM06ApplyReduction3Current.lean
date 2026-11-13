module

public import GraphMinor.GM06.Alg57ContractedCurrentDrawing
public import GraphMinor.Compute.GM06ApplyReduction3Drawing

/-!
# The RAM contraction preserves the whole current drawing

For the Reduction 3 branch of VI (5.7), page 133, the first word
of the selected linkage row gives the actual two directed ends.
The finite RAM update has the exact endpoint substitution, positive
rotation splice, shortened path, two mask changes and undo write.
The constructed current drawing relation interprets those same
literal fields, and its inverse record concerns that same drawing.
-/

public section
namespace GraphMinor.Compute
open Set Topology GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The selected RAM contraction constructs a complete new current
drawing interpretation and its actual undo step, with the proved
positive source splice, fixed cuff data and exact finite arrays. -/
theorem gm06ApplyReduction3Prog_current
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (b : Fin x.vertexCount) (first : ℕ) (rest : List ℕ)
    (hrow : x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt) = first :: rest)
    (hfirst : first < 2 * rep.tagged.length)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (rep.edge ⟨first / 2, by omega⟩)
      (cylinderM1Point k i) (rep.vertex b))
    (hvs : rep.vertex b ≠ cylinderM1Point k i) (hoff : rep.vertex b ∉ cylinderCuff2)
    (hist : List ℕ) (c : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w) (hm : 2 * rep.tagged.length < 2 ^ w)
    (hrotLen : 4 * (gm06EncodeRows x.rotations).length < 2 ^ w)
    (hrotWords : ∀ z ∈ gm06EncodeRows x.rotations, z < 2 ^ w)
    (hpathLen : (gm06EncodeRows x.linkage).length < 2 ^ w)
    (hpathWords : ∀ z ∈ gm06EncodeRows x.linkage, z < 2 ^ w)
    (hhist : hist.length < 2 ^ w) (hslot : 2 * c + 1 < hist.length)
    (h3 : s.arrs 3 = x.endpoints) (h4 : s.arrs 4 = gm06EncodeRows x.rotations)
    (h8 : s.arrs 8 = gm06EncodeRows x.linkage) (h9 : s.arrs 9 = hist)
    (h12 : s.arrs 12 = rep.tagged.map Prod.snd) (h14 : s.arrs 14 = gm02VertexBits rep.live)
    (h22 : s.regs 22 = (rep.source i).val) (h301 : s.regs 301 = b.val)
    (h328 : s.regs 328 = i.val) (h23 : s.regs 23 = first)
    (h24 : s.regs 24 = gm06DartMate first) (h309 : s.regs 309 = c) :
    let x' := gm06ContractSuccessorInput x (rep.source i).val b.val i.val first rest
    ∃ (s' : State) (t : ℕ) (G' : Drawing ClosedCylinder) (M : CylinderLinkage k G')
      (cur : GM06CurrentDrawingRep x' G' M),
      Exec w gm06ApplyReduction3Prog s s' t ∧
      t ≤ 682 + 28 * rep.tagged.length + 1000 * (gm06EncodeRows x.rotations).length +
        17 * i.val + 22 * (rest.length + 1) + 32 * (gm06EncodeRows x.linkage).length ∧
      Keeps [295, 309, 31, 7, 8, 9, 11, 320, 317, 319, 313, 323, 324, 98,
        311, 310, 312, 308, 307] [9, 25, 26, 27, 4, 28, 24, 8, 3, 12, 14] s s' ∧
      s'.arrs 3 = x'.endpoints ∧ s'.arrs 4 = gm06EncodeRows x'.rotations ∧
      s'.arrs 8 = gm06EncodeRows x'.linkage ∧
      s'.arrs 12 = cur.tagged.map Prod.snd ∧ s'.arrs 14 = gm02VertexBits cur.live ∧
      s'.regs 309 = c + 1 ∧ s'.arrs 9 = (hist.set (2 * c) i.val).set (2 * c + 1) first ∧
      (s'.arrs 12).count 1 + 1 = (s.arrs 12).count 1 ∧
      (s'.arrs 14).count 1 + 1 = (s.arrs 14).count 1 ∧
      IsCylinderSection5Drawing k G' ∧ Section5Reduction3Step k G L G' M ∧
      Function.Injective cur.vertex ∧ cur.live = rep.live.erase b ∧
      cur.tagged = gm06ContractTaggedEdges rep.tagged (rep.source i) b (first / 2) ∧
      GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
        ⟨G', cur.tagged, cur.vertex, cur.edge⟩ (some (i.val, first)) := by
  classical
  dsimp only
  obtain ⟨G', M, cur, hG', hred, hvinj', hlive', htag', hundo⟩ :=
    rep.exists_contracted_currentDrawingRep hvinj hG i b first rest hrow hfirst hval hl hvs hoff
  let vertex : Fin x.vertexCount ↪ ClosedCylinder := ⟨rep.vertex, hvinj⟩
  let d : Fin rep.tagged.length := ⟨first / 2, by omega⟩
  obtain ⟨W, _, henc, _⟩ := rep.linkage.path i
  rw [hrow] at henc
  obtain ⟨_, hactive⟩ := henc.active_words first (by simp)
  have hb : b ∈ rep.live := by
    obtain ⟨j, hj, hjeq⟩ := rep.vertex_cover _ hl.right_mem
    exact hvinj hjeq ▸ hj
  obtain ⟨a₀, a₁, _, _, hcode₀, hcode₁⟩ := rep.initial_word_halfedges i first rest hrow hfirst hl hvs
  have hx := rep.rows (rep.source i) (rep.source_live i)
  rw [rep.source_point] at hx
  have hy := rep.rows b hb
  have hsa : (rep.source i).val < x.rotations.length := by rw [rep.rows_length]; exact (rep.source i).isLt
  have hsb : b.val < x.rotations.length := by rw [rep.rows_length]; exact b.isLt
  have hrotD : first ∈ x.rotations[(rep.source i).val]'hsa := by
    rw [← List.getD_eq_getElem _ [] hsa]
    exact (hx.2.1 first).mpr ⟨a₀, hcode₀⟩
  have hrotMate : gm06DartMate first ∈ x.rotations[b.val]'hsb := by
    rw [← List.getD_eq_getElem _ [] hsb]
    exact (hy.2.1 _).mpr ⟨a₁, hcode₁⟩
  have hnd0 : (x.rotations[(rep.source i).val]'hsa).Nodup := by
    simpa only [List.getD_eq_getElem _ [] hsa] using hx.1
  have hnd1 : (x.rotations[b.val]'hsb).Nodup := by
    simpa only [List.getD_eq_getElem _ [] hsb] using hy.1
  obtain ⟨s', t, he, ht, hk, hcount, hhist', hrots', hpaths', hdropE, hdropV,
      πother, Gother, Mother, vother, hother⟩ :=
    gm06ApplyReduction3Prog_graph L hG i rep.tagged vertex rep.edge rep.live rep.edge_inj
      rep.links rep.edge_cover rep.vertex_mem rep.vertex_cover (rep.source i) b (rep.source_point i)
      d hactive hval hl hvs hoff x.linkage rep.linkage first rest hrow rfl
      x.rotations rep.rows_length hnd0 hnd1 hrotD hrotMate hist c s hw hn hm hrotLen hrotWords
      hpathLen hpathWords hhist hslot (h3.trans rep.endpoints) h4 h8 h9 h12 h14 h22 h301 h328 h23 h24 h309
  dsimp only at hother
  obtain ⟨_, _, h3', h12', h14', _⟩ := hother
  refine ⟨s', t, G', M, cur, he, ht, hk, ?_, ?_, hpaths', ?_, ?_, hcount, hhist',
    hdropE, hdropV, hG', hred, hvinj', hlive', htag', hundo⟩
  · change s'.arrs 3 = x.endpoints.map _
    rw [gm06ContractTaggedEdges_endpointWords, ← rep.endpoints] at h3'
    exact h3'
  · change s'.arrs 4 = gm06EncodeRows (gm06ContractRotationRows _ _ _ _ _)
    unfold gm06ContractRotationRows
    rw [List.getElem?_eq_getElem hsa, List.getElem?_eq_getElem hsb,
      Option.getD_some, Option.getD_some]
    exact hrots'
  · rw [htag']
    exact h12'
  · rw [hlive']
    exact h14'

end GraphMinor.Compute
