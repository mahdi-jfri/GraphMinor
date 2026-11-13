module

public import GraphMinor.Compute.GM06CutNeighbourMarks
public import GraphMinor.Compute.GM06Alg34FilterMapArray
import GraphMinor.Compute.GM06CutActiveBits

/-!
# Appending one cut vertex's adjacency row

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) finds
components of the graph given by copied rotations. For one row, the program
marks the origins of its reverse ends, then scans the vertex range
to append each neighbour once. The bitmap removes repeated neighbours
from parallel edges. The source rotations and edge labels survive.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths
open GraphMinor.Compute.Crossing

/-- Increasing distinct neighbours computed from one copied row. -/
def gm06CutRowNeighbours (n : ℕ) (origins active live : List ℕ) (u : ℕ) (row : List ℕ) : List ℕ :=
  (List.range n).filter (fun v => decide (v ∈ gm06CutNeighbourCandidates origins active live u row))

/-- A row contains at most one entry for each permanent vertex slot. -/
theorem gm06CutRowNeighbours_length_le (n : ℕ) (origins active live : List ℕ) (u : ℕ) (row : List ℕ) :
    (gm06CutRowNeighbours n origins active live u row).length ≤ n := by
  exact (List.length_filter_le _ _).trans (by simp)

/-- The constructed adjacency row has no repetitions. -/
theorem gm06CutRowNeighbours_nodup (n : ℕ) (origins active live : List ℕ) (u : ℕ) (row : List ℕ) :
    (gm06CutRowNeighbours n origins active live u row).Nodup := (List.nodup_range (n := n)).filter _

/-- Every constructed neighbour has a valid permanent vertex label. -/
theorem gm06CutRowNeighbours_bound {n : ℕ} (origins active live : List ℕ) (u : ℕ) (row : List ℕ)
    {v : ℕ} (hv : v ∈ gm06CutRowNeighbours n origins active live u row) : v < n :=
  List.mem_range.mp (List.mem_filter.mp hv).1

private theorem filter_flatMap (xs : List ℕ) (keep : ℕ → Bool) :
    xs.flatMap (fun d => if keep d then [d] else []) = xs.filter keep := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : keep x <;> simp [h, ih]

/-- Clear neighbour bits, mark reverse-end origins, and append the
selected vertex labels into CSR entries 622 at cursor 655. -/
def gm06CutNeighbourRowProg : Cmd :=
  .seq (.alloc 614 (.reg 620))
    (.seq gm06CutNeighbourMarkProg
      (gm06FilterMapArrayProg 618 622 650 651 652 655 (.read 614 (.reg 652)) (.reg 652)))

/-- Exact adjacency-row append with a polynomial bound. The row,
origins, active ends and live vertices are the only graph inputs. -/
theorem gm06CutNeighbourRowProg_exec {w n m u cap : ℕ}
    (origins active live row pre : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hm : 2 * m < 2 ^ w) (hu : u < n)
    (hl : row.length < 2 ^ w) (horgLen : origins.length = 2 * m)
    (hkeys : ∀ d ∈ row, d < 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hcap : n ≤ cap) (hfit : pre.length + cap + 2 < 2 ^ w)
    (h611 : s.arrs 611 = row) (h626 : s.arrs 626 = origins)
    (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h619 : s.arrs 619 = gm06IncidenceBits n live) (h618 : s.arrs 618 = List.range n)
    (h620 : s.regs 620 = n) (h666 : s.regs 666 = u)
    (hbuf : IsBuf 622 655 pre cap s) :
    ∃ sf t, Exec w gm06CutNeighbourRowProg s sf t ∧ t ≤ 13 + 20 * n + 107 * row.length ∧
      Keeps [650, 651, 652, 653, 655] [614, 622] s sf ∧
      IsBuf 622 655 (pre ++ gm06CutRowNeighbours n origins active live u row)
        (cap - (gm06CutRowNeighbours n origins active live u row).length) sf := by
  have hw1 : 1 < 2 ^ w := by omega
  have hn : n < 2 ^ w := by omega
  let s₀ := s.setArr 614 (List.replicate n 0)
  have he₀ : Exec w (.alloc 614 (.reg 620)) s s₀ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg h620 hn)
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hb₁⟩ := gm06CutNeighbourMarkProg_exec
    origins active live row (List.replicate n 0) s₀ hw hn hm hu hl horgLen (by simp)
    hkeys hvalues (by simpa [s₀] using h611) (by simpa [s₀] using h626)
    (by simp [s₀]) (by simpa [s₀] using h627) (by simpa [s₀] using h619)
    (by simpa [s₀] using h666)
  have hk₀₁ : Keeps [650, 651, 652, 653] [614] s s₁ :=
    ((Keeps.refl _ _ s).setArr (by simp) _).trans hk₁ (fun _ h => h) (fun _ h => h)
  let labels := gm06CutNeighbourCandidates origins active live u row
  let keep := fun v => decide (v ∈ labels)
  have hbits : s₁.arrs 614 = gm06IncidenceBits n labels :=
    hb₁.trans (gm06CutActiveScatter_eq n labels)
  have hsource : s₁.arrs 618 = List.range n := (hk₀₁.2 618 (by decide)).trans h618
  have hbuf₁ : IsBuf 622 655 pre cap s₁ := by
    constructor
    · exact (hk₀₁.2 622 (by decide)).trans hbuf.1
    · exact (hk₀₁.1 655 (by decide)).trans hbuf.2
  obtain ⟨sf, tf, hef, htf, hbf, haf, hrf⟩ := gm06FilterMapArrayProg_exec
    (l := List.range n) (pre := pre) (cap := cap) (s := s₁)
    618 622 650 651 652 655 (.read 614 (.reg 652)) (.reg 652) keep id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hw1 hsource (by simpa using hn) (fun v hv => (List.mem_range.mp hv).trans hn) hbuf₁
    (by simpa only [id_eq, filter_flatMap, gm06CutRowNeighbours, keep, labels] using
      (gm06CutRowNeighbours_length_le n origins active live u row).trans hcap) hfit
    (fun z v hv ha _ hr => by
      have hz : z.arrs 614 = gm06IncidenceBits n labels := (ha 614 (by decide)).trans hbits
      simpa only [keep, decide_eq_true_eq] using gm06ReadBits_eval labels z (.reg 652) hw1 (List.mem_range.mp hv)
        (GraphMinor.Compute.Crossing.eval_reg hr ((List.mem_range.mp hv).trans hn)) hz)
    (fun _ v hv _ _ _ hr => GraphMinor.Compute.Crossing.eval_reg hr ((List.mem_range.mp hv).trans hn))
  have hkf : Keeps [650, 651, 652, 653, 655] [622] s₁ sf := by
    constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact hrf r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.2
    · intro a ha
      exact haf a (by simpa using ha)
  refine ⟨sf, (1 + n) + (t₁ + tf), .seq he₀ (.seq he₁ hef), ?_,
    (hk₀₁.mono (by simp) (by simp)).trans hkf (fun _ h => h) (by simp), ?_⟩
  · simp only [Expr.cost, List.length_range] at htf
    omega
  · simpa only [id_eq, filter_flatMap, gm06CutRowNeighbours, keep, labels] using hbf

end GraphMinor.Compute
