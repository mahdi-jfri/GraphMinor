module

public import GraphMinor.Compute.GM02RecursiveChosenChild
public import GraphMinor.Compute.GM02RecursivePushChild
public import GraphMinor.Compute.GM02TerminatedWords

/-!
# Executing an exact recursive side call

Build the chosen canonical child from the parent and a valid catalogue
code. The builder preserves parent arrays and high control words, so
the frame push then saves the exact parent continuation and starts the
child. Both stages read only plain input and computed catalogue data.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

private theorem bitSetList_words {w n : ℕ} (S : Finset (Fin n)) (hw : 1 < 2 ^ w) :
    ∀ v ∈ bitSetList S, v < 2 ^ w := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  exact (getElem_bitSetList_le_one S i hi).trans_lt hw

/-- A valid scheme code executes its chosen child call with an exact saved parent frame. -/
theorem gm02RecursiveCallProg_exec {w cap : ℕ} (right : Bool) (q : ℕ)
    (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n))
    (C : (gm02CompressedBoundaryInput x L R).schemes) (pref : List ℕ)
    (phase aggregate leftAnswer : ℕ) (s : State)
    (hparent : s.arrs (gm02RecursiveParentArr q) = x.enc) (hlen : x.enc.length < 2 ^ w)
    (hL : s.arrs 1 = bitSetList L) (hR : s.arrs 2 = bitSetList R)
    (hB : (gm02CompressedBoundaryInput x L R).n ≤ gm02RecursiveBoundaryBound q)
    (hn : x.n < 2 ^ w) (hNW : gm02RecursiveBoundaryBound q + 1 < 2 ^ w)
    (hCW : gm02RecursiveCodeBound q + 1 < 2 ^ w)
    (horig : s.arrs (gm02RecursiveParentArr q + 4) = List.ofFn
      (fun i : Fin (gm02CompressedBoundaryInput x L R).n =>
        (compactEmb (gm02BoundaryDeletedSet x L R) i).val))
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q)
      (gm02CompressedBoundaryInput x L R))
    (hcodes : 2 ^ gm02RecursiveCodeBound q ≤ 2 ^ w)
    (hchild : 8 + 2 * (edgeListOf x.G).length +
      2 * (if right then C.right.index else C.left.index) < 2 ^ w)
    (hclen : (gm02RecursiveChosenInput right x L R C).enc.length < 2 ^ w)
    (hcn : (gm02RecursiveChosenInput right x L R C).n < 2 ^ w)
    (hphase : s.regs (gm02RecursiveControlBase q + 3) = phase) (hph : phase ≤ 1)
    (hcode : s.regs (gm02RecursiveControlBase q + 4) =
      gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C)
    (hagg : s.regs (gm02RecursiveControlBase q + 5) = aggregate)
    (hleft : s.regs (gm02RecursiveControlBase q + 6) = leftAnswer)
    (ha : aggregate ≤ 1) (hl : leftAnswer ≤ 1) (hw : 3 < 2 ^ w)
    (hframe : pref.length + 9 + x.enc.length + 2 * x.n < 2 ^ w)
    (hstack : IsPrefixBuffer (gm02RecursiveStackArr q) pref
      (9 + x.enc.length + 2 * x.n + cap) s)
    (hpos : s.regs (gm02RecursiveControlBase q + 10) = pref.length) :
    let child := gm02RecursiveChosenInput right x L R C
    let code := gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C
    let catalogue := gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R)
    let tag := phase + if right then 2 else 0
    let b := gm02RecursiveControlBase q
    ∃ s' t, Exec w (gm02RecursiveCallProg right q code) s s' t ∧
      t ≤ 376 + 28 * x.A.index + 73 * gm02RecursiveBoundaryBound q +
        x.n * (143 + 28 * gm02RecursiveBoundaryBound q) + 166 * (edgeListOf x.G).length +
        4 * (gm02RecursiveCodeBound q + 1) + 4 * (gm02RecursiveBoundaryBound q + 1) +
        17 * (x.enc.length + 2 * x.n) + 16 * child.enc.length ∧
      IsPrefixBuffer (gm02RecursiveStackArr q)
        (pref ++ gm02SavedFrameWords x.enc (bitSetList L) (bitSetList R)
          tag code aggregate leftAnswer catalogue pref.length) cap s' ∧
      s'.arrs (gm02RecursiveParentArr q) = child.enc ∧ s'.arrs 1 = bitSetList L ∧ s'.arrs 2 = bitSetList R ∧
      s'.regs (b + 10) = pref.length + 9 + x.enc.length + 2 * x.n ∧
      s'.regs (b + 3) = 1 - phase ∧ s'.regs (b + 18) = 1 ∧
      (∀ offset : ℕ, 18 < offset → s'.regs (b + offset) = s.regs (b + offset)) := by
  let p := gm02RecursiveParentArr q
  let a := gm02RecursiveTemplateArr q
  let b := gm02RecursiveControlBase q
  have hpg := gm02RecursiveParentArr_ge q
  have hbg := gm02RecursiveControlBase_ge q
  obtain ⟨s₁, t₁, he₁, ht₁, hchild₁, hL₁, hR₁, _, hcat₁, ha₁, hr₁⟩ :=
    gm02RecursiveSelectedChild_exec right q x L R C s hparent hlen hL hR hB hn hNW hCW
      horig hcat hcodes hchild
  have hparent₁ : s₁.arrs p = x.enc := (ha₁ p
    (by dsimp only [p, Arr] at *; omega)
    (Or.inl (by dsimp only [a, p, gm02RecursiveTemplateArr, Arr]; omega))).trans hparent
  have hhigh₁ (offset : ℕ) : s₁.regs (b + offset) = s.regs (b + offset) :=
    hr₁ _ (by dsimp only [b, Reg] at *; omega)
  have hstack₁ : IsPrefixBuffer (gm02RecursiveStackArr q) pref
      (9 + x.enc.length + 2 * x.n + cap) s₁ :=
    hstack.of_arr_eq (ha₁ _
      (by dsimp only [gm02RecursiveStackArr, Arr] at *; omega)
      (Or.inr (by dsimp only [a, gm02RecursiveTemplateArr, gm02RecursiveStackArr, Arr]; omega)))
  have hcodew : gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C < 2 ^ w :=
    (gm02BoundarySchemeCode_lt_bound _ hB C).trans
      (by change gm02RecursiveCodeBound q < 2 ^ w; omega)
  have hcatw : gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q)
      (gm02CompressedBoundaryInput x L R) < 2 ^ w :=
    (gm02BoundarySchemeSetCode_lt _ _).trans_le hcodes
  obtain ⟨s₂, t₂, he₂, ht₂, hstack₂, hchild₂, hL₂, hR₂, hpos₂, hphase₂, hstate₂, hhigh₂⟩ :=
    gm02RecursivePushChildProg_exec right q x.enc (bitSetList L) (bitSetList R)
      (gm02RecursiveChosenInput right x L R C).enc pref phase
      (gm02BoundarySchemeCode (gm02CompressedBoundaryInput x L R) C) aggregate leftAnswer
      (gm02BoundarySchemeSetCode (gm02RecursiveBoundaryBound q) (gm02CompressedBoundaryInput x L R)) s₁
      hparent₁ hL₁ hR₁ hchild₁ ((hhigh₁ 3).trans hphase) ((hhigh₁ 4).trans hcode)
      ((hhigh₁ 5).trans hagg) ((hhigh₁ 6).trans hleft) hcat₁ hph hw
      (by simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hframe) hclen
      (x.enc_all_lt hn hlen) (bitSetList_words L (by omega)) (bitSetList_words R (by omega))
      ((gm02RecursiveChosenInput right x L R C).enc_all_lt hcn hclen)
      hcodew (ha.trans_lt (by omega)) (hl.trans_lt (by omega)) hcatw
      (by simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hstack₁)
      ((hhigh₁ 10).trans hpos)
  refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, ?_, hstack₂, hchild₂, hL₂, hR₂, ?_, hphase₂, hstate₂, ?_⟩
  · simp only [length_bitSetList] at ht₂
    omega
  · simpa only [length_bitSetList, two_mul, Nat.add_assoc] using hpos₂
  · intro offset hoff
    exact (hhigh₂ offset hoff).trans (hhigh₁ offset)

end GraphMinor.Compute
