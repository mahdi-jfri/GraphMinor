module

public import GraphMinor.Compute.GM06ApplyReduction3Current
public import GraphMinor.Compute.GM06Reduction3ScanDrawing
import GraphMinor.GM06.Section5AnnulusInterior
import GraphMinor.GM06.Section5Red

/-!
# Scanning and applying the current contraction branch

For VI (5.7), page 133, the selected first linkage word determines
the actual edge and neighbour. The fixed outer-cuff labels decide
whether that neighbour is eligible. The existing contraction scan
and rectangular-collapse update therefore compose on the complete
current drawing relation. All geometry of the new rotations is
proved by that update, rather than supplied to this branch.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.Compute

/-- Among actual current vertices, the fixed outer-cuff words
identify exactly those on the outer cuff. -/
theorem GM06CurrentDrawingRep.outer_mem_iff
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex) (hG : IsCylinderSection5Drawing k G)
    (a : Fin x.vertexCount) (haV : rep.vertex a ∈ G.V) :
    a.val ∈ x.outerCuff ↔ rep.vertex a ∈ cylinderCuff2 := by
  rw [rep.outer, List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    have he : rep.target i = a := Fin.ext hi
    rw [← he, rep.target_point]
    exact cylinderM2Point_mem_cylinderCuff2 k i
  · intro ha
    have habd : rep.vertex a ∈ bd ClosedCylinder := by
      rw [bd_closedCylinder]
      exact Or.inr ha
    have haM : rep.vertex a ∈ cylinderM1 k ∪ cylinderM2 k := hG.2.2 ▸ ⟨haV, habd⟩
    rcases haM with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact False.elim (disjoint_cylinderCuffs.ne_of_mem (cylinderM1Point_mem_cylinderCuff1 k i) ha hi)
    · have he : rep.target i = a := hvinj ((rep.target_point i).trans hi)
      exact ⟨i, congrArg Fin.val he⟩

end GraphMinor.GM06
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- Find the first eligible source edge and perform its contraction.
Register 327 reports success, and array 9 receives its inverse record. -/
@[expose] def gm06Reduction3CurrentProg : Cmd :=
  .seq gm06Reduction3ScanProg (.ite (.reg 327) gm06ApplyReduction3Prog .skip)

/-- The scan and rectangular-collapse command preserve the complete
current relation and record the actual inverse. Each successful
branch removes one live vertex and one active edge. -/
theorem gm06Reduction3CurrentProg_exec
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex) (hG : IsCylinderSection5Drawing k G)
    (hist : List ℕ) (c : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w) (hm : 2 * rep.tagged.length < 2 ^ w)
    (hk : k < 2 ^ w) (hbits : ∀ p ∈ rep.tagged, p.2 ≤ 1)
    (hrotLen : 4 * (gm06EncodeRows x.rotations).length < 2 ^ w)
    (hrotWords : ∀ z ∈ gm06EncodeRows x.rotations, z < 2 ^ w)
    (hpathLen : (gm06EncodeRows x.linkage).length < 2 ^ w)
    (hpathWords : ∀ z ∈ gm06EncodeRows x.linkage, z < 2 ^ w)
    (hhist : hist.length < 2 ^ w) (hslot : 2 * c + 1 < hist.length)
    (h3 : s.arrs 3 = x.endpoints) (h4 : s.arrs 4 = gm06EncodeRows x.rotations)
    (h6 : s.arrs 6 = x.innerCuff) (h7 : s.arrs 7 = x.outerCuff)
    (h8 : s.arrs 8 = gm06EncodeRows x.linkage) (h9 : s.arrs 9 = hist)
    (h12 : s.arrs 12 = rep.tagged.map Prod.snd) (h14 : s.arrs 14 = gm02VertexBits rep.live)
    (h309 : s.regs 309 = c) :
    ∃ s' t, Exec w gm06Reduction3CurrentProg s s' t ∧
      t ≤ 7 + k * (73 + 42 * rep.tagged.length + 17 * k +
          22 * (gm06EncodeRows x.linkage).length + 13 * x.outerCuff.length) +
        683 + 28 * rep.tagged.length + 1000 * (gm06EncodeRows x.rotations).length +
        17 * k + 54 * (gm06EncodeRows x.linkage).length ∧
      (∀ a ∈ [2, 6, 7, 17, 19], s'.arrs a = s.arrs a) ∧
      (∀ r ∈ [329, 900], s'.regs r = s.regs r) ∧
      ((s'.regs 327 = 0 ∧ s'.regs 309 = c ∧
          (∀ a ∈ [3, 4, 8, 9, 12, 14], s'.arrs a = s.arrs a) ∧
          ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
            ¬ Section5Reduction3Step k G L H M) ∨
       ∃ (i : Fin k) (b : Fin x.vertexCount) (first : ℕ) (rest : List ℕ)
         (H : Drawing ClosedCylinder) (M : CylinderLinkage k H)
         (cur : GM06CurrentDrawingRep
           (gm06ContractSuccessorInput x (rep.source i).val b.val i.val first rest) H M),
         s'.regs 327 = 1 ∧
         s'.arrs 3 = (gm06ContractSuccessorInput x (rep.source i).val b.val i.val first rest).endpoints ∧
         s'.arrs 4 = gm06EncodeRows (gm06ContractSuccessorInput x (rep.source i).val b.val i.val first rest).rotations ∧
         s'.arrs 8 = gm06EncodeRows (gm06ContractSuccessorInput x (rep.source i).val b.val i.val first rest).linkage ∧
         s'.arrs 12 = cur.tagged.map Prod.snd ∧ s'.arrs 14 = gm02VertexBits cur.live ∧
         s'.regs 309 = c + 1 ∧ s'.arrs 9 = (hist.set (2 * c) i.val).set (2 * c + 1) first ∧
         (s'.arrs 12).count 1 + 1 = (s.arrs 12).count 1 ∧
         (s'.arrs 14).count 1 + 1 = (s.arrs 14).count 1 ∧
         IsCylinderSection5Drawing k H ∧ Section5Reduction3Step k G L H M ∧
         Function.Injective cur.vertex ∧ cur.live = rep.live.erase b ∧
         cur.tagged = gm06ContractTaggedEdges rep.tagged (rep.source i) b (first / 2) ∧
         GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
           ⟨H, cur.tagged, cur.vertex, cur.edge⟩ (some (i.val, first))) := by
  classical
  let vertex : Fin x.vertexCount ↪ ClosedCylinder := ⟨rep.vertex, hvinj⟩
  have houterLen : x.outerCuff.length = k := by rw [rep.outer, List.length_ofFn]
  have houterWords : ∀ v ∈ x.outerCuff, v < 2 ^ w := by
    intro v hv
    rw [rep.outer, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact (rep.target i).isLt.trans hn
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout⟩ := gm06Reduction3ScanProg_selected L rep.tagged vertex rep.edge
    rep.edge_inj rep.links rep.edge_cover rep.source rep.source_point x.outerCuff
    (fun b hb => (rep.outer_mem_iff hvinj hG b hb).symm) x.linkage rep.linkage s hw hn hm hbits hk
    (houterLen ▸ hk) houterWords hpathLen hpathWords (h3.trans rep.endpoints) h12 (h6.trans rep.inner) h7 h8
  have hf₁ (a : ℕ) (ha : a ∈ [2, 6, 7, 17, 19]) : s₁.arrs a = s.arrs a := by
    apply hk₁.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  have hr₁ (r : ℕ) (hr : r ∈ [329, 900]) : s₁.regs r = s.regs r := by
    apply hk₁.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  rcases hout with ⟨hflag, hno⟩ |
      ⟨i, first, rest, b, hfirst, hrow, hflag, h328, h22, h23, h24, h301, _, _, hval, hl, hvs, hoff⟩
  · refine ⟨s₁, t₁ + 2, .seq he₁ (.ite_false (Crossing.eval_reg hflag (Nat.two_pow_pos w)) (.skip _)),
      by omega, hf₁, hr₁, Or.inl ⟨hflag, (hk₁.1 309 (by decide)).trans h309, ?_, hno⟩⟩
    intro a ha
    apply hk₁.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · obtain ⟨s₂, t₂, H, M, cur, he₂, ht₂, hk₂, h3₂, h4₂, h8₂, h12₂, h14₂, hc₂, hh₂,
      hdropE, hdropV, hH, hred, hvinj', hA, htag, hundo⟩ := gm06ApplyReduction3Prog_current rep
      hvinj hG i b first rest hrow hfirst hval hl hvs hoff hist c s₁ hw hn hm hrotLen hrotWords
      hpathLen hpathWords hhist hslot ((hk₁.2 3 (by decide)).trans h3)
      ((hk₁.2 4 (by decide)).trans h4) ((hk₁.2 8 (by decide)).trans h8)
      ((hk₁.2 9 (by decide)).trans h9) ((hk₁.2 12 (by decide)).trans h12)
      ((hk₁.2 14 (by decide)).trans h14) h22 h301 h328 h23 h24 ((hk₁.1 309 (by decide)).trans h309)
    have hrowLen : rest.length + 1 ≤ (gm06EncodeRows x.linkage).length := by
      have hsub := (List.sublist_flatten_of_mem
        (List.getElem_mem (show i.val < x.linkage.length by rw [rep.linkage.1]; exact i.isLt))).length_le
      rw [hrow] at hsub
      rw [gm06EncodeRows_length]
      simp only [List.length_cons] at hsub
      omega
    refine ⟨s₂, t₁ + (1 + t₂), .seq he₁ (.ite_true
      (Crossing.eval_reg hflag (by omega)) (by decide) he₂), ?_, ?_, ?_, Or.inr ?_⟩
    · have hi := i.isLt
      omega
    · intro a ha
      apply (hk₂.2 a ?_).trans (hf₁ a ha)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
    · intro r hr
      apply (hk₂.1 r ?_).trans (hr₁ r hr)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · refine ⟨i, b, first, rest, H, M, cur, (hk₂.1 327 (by decide)).trans hflag,
        h3₂, h4₂, h8₂, h12₂, h14₂, hc₂, hh₂, ?_, ?_, hH, hred, hvinj', hA, htag, hundo⟩
      · simpa only [(hk₁.2 12 (by decide))] using hdropE
      · simpa only [(hk₁.2 14 (by decide))] using hdropV

end GraphMinor.Compute
