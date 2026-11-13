module

public import GraphMinor.Compute.GM02BoundaryComplement
public import GraphMinor.Compute.Algorithm99Relabel

/-!
# Numbering the crossing-scheme boundary on the Word RAM

Construct the boundary deletion bits, compute surviving-vertex ranks,
and write the inverse list of original names. Both arrays are needed:
compact ranks form the finite boundary input, while inverse names expand
the selected scheme patterns into original graph vertices. All three
passes use linear time in the parent vertex count.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Number the support union separator, retaining both directions of the
numbering. Registers 310 and 312 return parent and boundary sizes. -/
def gm02NumberBoundaryProg (support left right deleted rank orig : Arr) : Cmd :=
  .seq (gm02BoundaryComplementProg support left right deleted)
    (.seq (compactRankProg deleted rank 310 311 312) (compactOrigProg deleted rank orig 310 312 311))

/-- Boundary numbering writes exactly the compact ranks and original-name
list, with a linear time bound and explicit array/register preservation. -/
theorem gm02NumberBoundaryProg_exec {n w : ℕ} (Q L R : Finset (Fin n))
    (support left right deleted rank orig : Arr)
    (hqd : support ≠ deleted) (hld : left ≠ deleted) (hrd : right ≠ deleted)
    (hdr : deleted ≠ rank) (hdo : deleted ≠ orig) (hro : rank ≠ orig)
    (s : State) (hq : s.arrs support = bitSetList Q) (hl : s.arrs left = bitSetList L)
    (hr : s.arrs right = bitSetList R) (hn : s.regs 40 = n) (hnw : n < 2 ^ w) (hw : 2 < 2 ^ w) :
    let Z := (Q ∪ (L ∩ R))ᶜ
    ∃ s' t, Exec w (gm02NumberBoundaryProg support left right deleted rank orig) s s' t ∧
      t ≤ 62 * n + 30 ∧
      s'.arrs deleted = bitSetList Z ∧
      s'.arrs rank = List.ofFn (fun v : Fin n => compactRank Z v.val) ∧
      s'.arrs orig = List.ofFn (fun i : Fin Zᶜ.card => (compactEmb Z i).val) ∧
      s'.regs 310 = n ∧ s'.regs 312 = (Q ∪ (L ∩ R)).card ∧
      (∀ a, a ≠ deleted → a ≠ rank → a ≠ orig → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 300 → r ≠ 310 → r ≠ 311 → r ≠ 312 → s'.regs r = s.regs r) := by
  let Z := (Q ∪ (L ∩ R))ᶜ
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hZ₁⟩ := gm02BoundaryComplementProg_exec Q L R support left right deleted
    hqd hld hrd s hq hl hr hn hnw (by omega)
  obtain ⟨s₂, t₂, he₂, ht₂, hRank₂, hCount₂, hN₂, ha₂, hr₂⟩ := compactRankProg_exec Z
    deleted rank 310 311 312 hdr (by decide) (by decide) (by decide) hw hnw hZ₁
  have hZ₂ : s₂.arrs deleted = bitSetList Z := (ha₂ deleted hdr).trans hZ₁
  obtain ⟨s₃, t₃, he₃, ht₃, hOrig₃, ha₃, hr₃⟩ := compactOrigProg_exec Z deleted rank orig 310 312 311
    hdo hro (by decide) hw hnw hZ₂ hRank₂ hN₂ hCount₂
  refine ⟨s₃, _, Exec.seq he₁ (Exec.seq he₂ he₃), by omega, ?_, ?_, hOrig₃, ?_, ?_, ?_, ?_⟩
  · exact (ha₃ deleted hdo).trans hZ₂
  · exact (ha₃ rank hro).trans hRank₂
  · exact (hr₃ 310 (by decide)).trans hN₂
  · simpa only [Z, compl_compl] using (hr₃ 312 (by decide)).trans hCount₂
  · intro a had har hao
    rw [ha₃ a hao, ha₂ a har]
    exact hk₁.2 a (by simpa only [List.mem_singleton] using had)
  · intro r hr300 hr310 hr311 hr312
    rw [hr₃ r hr311, hr₂ r hr310 hr311 hr312]
    exact hk₁.1 r (by simpa only [List.mem_singleton] using hr300)

end GraphMinor.Compute
