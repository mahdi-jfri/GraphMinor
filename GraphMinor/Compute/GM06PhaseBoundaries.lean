module

public import GraphMinor.Compute.GM06PhaseRows
public import GraphMinor.Compute.GM06Reduction4Phase
import GraphMinor.Compute.CrossingOpsCycleTest

/-!
# Computing copied boundary vertices from current path rows

Sections 12 and 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) use
the left and right vertex lists of the two path boundaries. These
programs read original directed darts and endpoints and compute
the copied labels. The edge list for the left boundary retains the
original edge identity, including parallel edges.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The copied start followed by all copied arrival vertices. -/
def gm06PhaseBoundaryRow (origins row : List ℕ) (start tag : ℕ) : List ℕ :=
  (2 * start + tag) :: row.map (fun d => 2 * origins[gm06DartMate d]?.getD 0 + tag)

/-- The boundary rows used by the pure phase are precisely these
computed copies of the current original path rows. -/
theorem gm06PhaseBoundaryRow_eq (x : GM06SuccessorInput) (i tag : ℕ) :
    gm06PhaseBoundaryRow x.endpoints (x.linkage[i]?.getD []) (x.innerCuff[i]?.getD 0) tag =
      gm06PhaseBoundaryVertices x i tag := by rfl

/-- All copied boundary vertices lie in the doubled vertex space. -/
theorem gm06PhaseBoundaryRow_bounds {n m start tag : ℕ} (origins row : List ℕ)
    (horig : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hrow : ∀ d ∈ row, d < 2 * m) (hstart : start < n) (htag : tag ≤ 1) :
    ∀ v ∈ gm06PhaseBoundaryRow origins row start tag, v < 2 * n := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · omega
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    have hb : gm06DartMate d < origins.length := horig ▸ gm06DartMate_lt (hrow d hd)
    have hx := hvalues _ (List.getElem_mem hb)
    simp only [List.getElem?_eq_getElem hb, Option.getD_some]
    omega

/-- Compute copied arrivals from endpoint array 3 and a saved path row. -/
def gm06PhaseBoundaryArrivalExpr (src tag : ℕ) : Expr :=
  .op .add (.op .mul (.const 2) (.read 3 (gm06DartMateExpr (.read src (.reg 650))))) (.const tag)

/-- Build a boundary row in a destination distinct from the two
append scratch arrays. Register 695 contains its original start. -/
def gm06PhaseBoundaryRowProg (src dst tag : ℕ) : Cmd :=
  .seq (.alloc 617 (.const 1))
    (.seq (.write 617 (.const 0) (.op .add (.op .mul (.const 2) (.reg 695)) (.const tag)))
      (.seq (gm13TabulateProg 650 (.len src) (gm06PhaseBoundaryArrivalExpr src tag) 618)
        (gm06ConcatWordsProg 617 618 dst)))

/-- Exact boundary-row construction from original endpoint and dart
arrays, with linear time and a frame wholly within reserved scratch. -/
theorem gm06PhaseBoundaryRowProg_exec {w n m start tag : ℕ} (src dst : ℕ)
    (hsrc617 : src ≠ 617) (hsrc618 : src ≠ 618) (hdst617 : dst ≠ 617) (hdst618 : dst ≠ 618)
    (origins row : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : 2 * n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (horig : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hrow : ∀ d ∈ row, d < 2 * m) (hstart : start < n) (htag : tag ≤ 1)
    (hfit : row.length + 3 < 2 ^ w) (h3 : s.arrs 3 = origins) (ha : s.arrs src = row)
    (h695 : s.regs 695 = start) :
    ∃ sf t, Exec w (gm06PhaseBoundaryRowProg src dst tag) s sf t ∧
      t ≤ 60 + 100 * row.length ∧ Keeps [650, 651, 652, 655] [617, 618, dst] s sf ∧
      sf.arrs dst = gm06PhaseBoundaryRow origins row start tag := by
  let first := 2 * start + tag
  let arrivals := row.map (fun d => 2 * origins[gm06DartMate d]?.getD 0 + tag)
  have hfirst : first < 2 ^ w := by dsimp only [first]; omega
  have harrivals : ∀ v ∈ arrivals, v < 2 ^ w := by
    intro v hv
    exact (gm06PhaseBoundaryRow_bounds origins row horig hvalues hrow hstart htag v
      (List.mem_cons_of_mem first hv)).trans hn
  have harrLen : arrivals.length = row.length := List.length_map _
  let s₀ := s.setArr 617 [0]
  let s₁ := s₀.writeArr 617 0 first
  have he₀ : Exec w (.alloc 617 (.const 1)) s s₀ 2 := .alloc (GraphMinor.Compute.Crossing.eval_const (by omega))
  have he₁ : Exec w (.write 617 (.const 0) (.op .add (.op .mul (.const 2) (.reg 695)) (.const tag))) s₀ s₁ 7 :=
    .write (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
          (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₀] using h695) (by omega)) (by dsimp only [first] at hfirst; omega))
        (GraphMinor.Compute.Crossing.eval_const (by omega)) hfirst) (by simp [s₀])
  have hk₁ : Keeps [650] [617, 618] s s₁ :=
    ((Keeps.refl _ _ s).setArr (by simp) _).writeArr (by simp) _ _
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm13TabulateProg_exec (w := w) 650 (.len src)
    (gm06PhaseBoundaryArrivalExpr src tag) 618 arrivals s₁ (by omega) (by rw [harrLen]; omega)
    (fun st hk => by
      rw [harrLen]
      exact GraphMinor.Compute.Crossing.eval_len
        ((hk.2 src (by simpa using hsrc618)).trans ((hk₁.2 src (by simp [hsrc617, hsrc618])).trans ha)) (by omega))
    (fun st i hi hk hr => by
      have hi' : i < row.length := harrLen ▸ hi
      have hsr := (hk.2 src (by simpa using hsrc618)).trans ((hk₁.2 src (by simp [hsrc617, hsrc618])).trans ha)
      have horg := (hk.2 3 (by decide)).trans ((hk₁.2 3 (by decide)).trans h3)
      have hd := hrow _ (List.getElem_mem hi')
      have hread := GraphMinor.Compute.Crossing.eval_read (a := src)
        (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega))
        (by simpa only [hsr] using hi') (by simpa only [hsr] using hd.trans hm)
      have hread' : (Expr.read src (.reg 650)).eval w st = some row[i] := by simpa only [hsr] using hread
      have hmate := gm06DartMateExpr_eval hw hm hd hread'
      have hidx : gm06DartMate row[i] < origins.length := horig ▸ gm06DartMate_lt hd
      have hv := hvalues _ (List.getElem_mem hidx)
      have hhead := GraphMinor.Compute.Crossing.eval_read (a := 3) hmate
        (by simpa only [horg] using hidx) (by simpa only [horg] using hv.trans (by omega : n < 2 ^ w))
      have hlabel : 2 * origins[gm06DartMate row[i]] + tag < 2 ^ w := by omega
      have he := GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw) hhead
          (by simpa only [horg] using (show 2 * origins[gm06DartMate row[i]] < 2 ^ w by omega)))
        (GraphMinor.Compute.Crossing.eval_const (by omega : tag < 2 ^ w))
        (by simpa only [horg] using hlabel)
      simpa only [gm06PhaseBoundaryArrivalExpr, arrivals, List.getElem_map,
        List.getElem?_eq_getElem hidx, Option.getD_some, horg] using he)
  have hk₁₂ : Keeps [650] [617, 618] s s₂ := hk₁.trans hk₂ (fun _ h => h) (by simp)
  have h617 : s₂.arrs 617 = [first] := by
    rw [hk₂.2 617 (by decide)]
    simp [s₁, s₀, State.writeArr]
  obtain ⟨sf, tf, hef, htf, hkf, hdf, _⟩ := gm06ConcatWordsProg_exec (Ne.symm hdst617) (Ne.symm hdst618) [first] arrivals s₂
    (by omega) (by simp only [List.length_singleton, harrLen]; omega)
    (by simpa using hfirst) harrivals h617 hd₂
  refine ⟨sf, 2 + (7 + (t₂ + tf)), .seq he₀ (.seq he₁ (.seq he₂ hef)), ?_, ?_, hdf⟩
  · simp only [Expr.cost, gm06PhaseBoundaryArrivalExpr, gm06DartMateExpr, harrLen] at ht₂
    simp only [List.length_singleton, harrLen] at htf
    omega
  · exact (hk₁₂.mono (by simp) (by simp)).trans hkf (fun _ h => h) (by simp)

/-- Compute copied left-edge labels from a saved original path. -/
def gm06PhaseLeftEdgesProg (src : ℕ) : Cmd :=
  gm13TabulateProg 650 (.len src) (.op .mul (.const 2) (.op .div (.read src (.reg 650)) (.const 2))) 610

/-- The edge row agrees with the edge coordinates of the pure
left-boundary steps and preserves parallel-edge labels. -/
theorem gm06PhaseLeftEdgesProg_exec {w m : ℕ} (src : ℕ) (hne : src ≠ 610)
    (row : List ℕ) (s : State) (hw : 2 < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hrow : ∀ d ∈ row, d < 2 * m) (hlen : row.length < 2 ^ w) (ha : s.arrs src = row) :
    ∃ sf t, Exec w (gm06PhaseLeftEdgesProg src) s sf t ∧ t ≤ 6 + 18 * row.length ∧
      Keeps [650] [610] s sf ∧ sf.arrs 610 = row.map (fun d => 2 * (d / 2)) := by
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec (w := w) 650 (.len src)
    (.op .mul (.const 2) (.op .div (.read src (.reg 650)) (.const 2))) 610 (row.map (fun d => 2 * (d / 2))) s
    (by omega) (by simpa using hlen)
    (fun st hk => by
      have he := GraphMinor.Compute.Crossing.eval_len (w := w) ((hk.2 src (by simpa using hne)).trans ha) hlen
      simpa only [List.length_map] using he)
    (fun st i hi hk hr => by
      have hi' : i < row.length := by simpa using hi
      have hsrc := (hk.2 src (by simpa using hne)).trans ha
      have h := hrow _ (List.getElem_mem hi')
      have hread := GraphMinor.Compute.Crossing.eval_read (a := src)
        (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega))
        (by simpa only [hsrc] using hi') (by simpa only [hsrc] using h.trans hm)
      have hdiv := GraphMinor.Compute.Crossing.eval_div hread (GraphMinor.Compute.Crossing.eval_const hw) (by decide)
        (by simp only [hsrc]; omega)
      have he := GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw) hdiv
        (by simp only [hsrc]; omega)
      simpa only [List.getElem_map, hsrc] using he)
  exact ⟨sf, t, he, by simpa only [Expr.cost, List.length_map, Nat.mul_comm] using ht, hk, hd⟩

end GraphMinor.Compute
