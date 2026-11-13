module

public import GraphMinor.Compute.GM06Alg34EmitSelected
public import GraphMinor.Compute.CrossingOpsEmit

/-!
# Filtering and relabelling an array into a reserved output buffer

Scan a finite source array. For each word, a read-only test selects
whether to append its computed label. The exact finite reference list
and the preserved outer registers support incidence and gap-class
serialization in the disc-duality step.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Select and relabel source words using three loop registers. -/
def gm06FilterMapArrayProg (src buf ri rn ry cursor : ℕ) (test value : Expr) : Cmd :=
  forArrProg src ri rn ry (gm06EmitSelectedProg buf cursor test value)

/-- A filter-and-label scan emits exactly its finite selected word list.
The tests may read unchanged outer registers and arrays. -/
theorem gm06FilterMapArrayProg_exec {w : ℕ} (src buf ri rn ry cursor : ℕ)
    (test value : Expr) (keep : ℕ → Bool) (label : ℕ → ℕ)
    (hsb : src ≠ buf) (hin : ri ≠ rn) (hic : ri ≠ cursor) (hnc : rn ≠ cursor)
    (hyc : ry ≠ cursor) (hyi : ry ≠ ri) (hyn : ry ≠ rn)
    (hw : 1 < 2 ^ w) {l pre : List ℕ} {cap : ℕ} {s : State}
    (hsource : s.arrs src = l) (hlen : l.length < 2 ^ w)
    (hwords : ∀ y ∈ l, y < 2 ^ w)
    (hbuf : IsBuf buf cursor pre cap s)
    (hcap : (l.flatMap (fun y => if keep y then [label y] else [])).length ≤ cap)
    (hfit : pre.length + cap + 2 < 2 ^ w)
    (htest : ∀ z y, y ∈ l → (∀ A, A ≠ buf → z.arrs A = s.arrs A) →
      (∀ r, r ≠ ri → r ≠ rn → r ≠ ry → r ≠ cursor → z.regs r = s.regs r) →
      z.regs ry = y → test.eval w z = some (if keep y then 1 else 0))
    (hvalue : ∀ z y, y ∈ l → keep y = true →
      (∀ A, A ≠ buf → z.arrs A = s.arrs A) →
      (∀ r, r ≠ ri → r ≠ rn → r ≠ ry → r ≠ cursor → z.regs r = s.regs r) →
      z.regs ry = y → value.eval w z = some (label y)) :
    let out := l.flatMap (fun y => if keep y then [label y] else [])
    ∃ s' t, Exec w (gm06FilterMapArrayProg src buf ri rn ry cursor test value) s s' t ∧
      t ≤ 7 + l.length * (10 + (test.cost + value.cost + 6)) ∧
      IsBuf buf cursor (pre ++ out) (cap - out.length) s' ∧
      (∀ A, A ≠ buf → s'.arrs A = s.arrs A) ∧
      (∀ r, r ≠ ri → r ≠ rn → r ≠ ry → r ≠ cursor → s'.regs r = s.regs r) := by
  let g : ℕ → List ℕ := fun y => if keep y then [label y] else []
  let Q : ℕ → State → Prop := fun _ z =>
    (∀ A, A ≠ buf → z.arrs A = s.arrs A) ∧
    (∀ r, r ≠ ri → r ≠ rn → r ≠ ry → r ≠ cursor → z.regs r = s.regs r)
  obtain ⟨s', t, he, ht, hQ, hb⟩ := forArrEmit_exec src ri rn ry buf cursor
    (gm06EmitSelectedProg buf cursor test value) g Q (test.cost + value.cost + 6)
    hin hic hnc hyc hyi hyn hw (by simpa only [hsource] using hlen)
    (by simpa only [hsource] using hwords) ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩ hbuf
    (by simpa only [hsource] using hcap)
    (fun _ z z' h ha hr => ⟨fun A hA => (congrFun ha A).trans (h.1 A hA),
      fun r hri hrn hry hrc => (hr r hri hrn hry).trans (h.2 r hri hrn hry hrc)⟩)
    (fun _ z h => h.1 src hsb)
    (fun j hj z front rem h hri hrn hry hb' hk' htotal => by
      have hy : (s.arrs src)[j] ∈ l := by
        exact Eq.mp (congrArg (fun A : List ℕ => (s.arrs src)[j] ∈ A) hsource)
          (List.getElem_mem hj)
      have hkc : (if keep (s.arrs src)[j] then 1 else 0) ≤ rem := by
        cases hh : keep (s.arrs src)[j] <;> simpa only [g, hh, Bool.false_eq_true, ↓reduceIte,
          List.length_nil, List.length_cons] using hk'
      obtain ⟨z', t', he', ht', hb'', ha', hr'⟩ := gm06EmitSelectedProg_exec test value
        (keep (s.arrs src)[j]) (label (s.arrs src)[j])
        (htest z _ hy h.1 h.2 hry) (fun hk => hvalue z _ hy hk h.1 h.2 hry)
        hb' hkc (by omega)
      refine ⟨z', t', he', ht', ⟨fun A hA => (ha' A hA).trans (h.1 A hA),
        fun r h1 h2 h3 h4 => (hr' r h4).trans (h.2 r h1 h2 h3 h4)⟩,
        (hr' ri hic).trans hri, (hr' rn hnc).trans hrn, ?_⟩
      cases hh : keep (s.arrs src)[j] <;>
        simpa only [g, hh, Bool.false_eq_true, ↓reduceIte, List.length_nil, List.length_cons] using hb'')
  exact ⟨s', t, he, by simpa only [hsource] using ht, by simpa only [hsource] using hb, hQ.1, hQ.2⟩

end GraphMinor.Compute
