module

public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Expanding template endpoint words by old-name lookup

Read each boundary index from a template array and look up its original
parent vertex name. The output has exactly the same word order. This
loop supplies the parent endpoint words of a fixed crossing-scheme pair
template before the child vertices are compacted.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Replace boundary indices by the corresponding parent vertex names. -/
def gm02LookupTemplateWordsProg (src orig dst : Arr) : Cmd :=
  gm13TabulateProg 342 (.len src) (.read orig (.read src (.reg 342))) dst

/-- Lookup preserves the template word order and changes no source array. -/
theorem gm02LookupTemplateWordsProg_exec {n b w : ℕ} (f : Fin b → Fin n)
    (indices : List (Fin b)) (src orig dst : Arr) (hsd : src ≠ dst) (hod : orig ≠ dst)
    (s : State) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hb : b < 2 ^ w)
    (hlen : indices.length < 2 ^ w)
    (hsrc : s.arrs src = indices.map Fin.val)
    (horig : s.arrs orig = List.ofFn (fun i => (f i).val)) :
    ∃ s' t, Exec w (gm02LookupTemplateWordsProg src orig dst) s s' t ∧
      t ≤ 6 + 15 * indices.length ∧ Keeps [342] [dst] s s' ∧
      s'.arrs dst = indices.map (fun i => (f i).val) := by
  obtain ⟨s', t, he, ht, hk, hout⟩ := gm13TabulateProg_exec (w := w) 342 (.len src)
    (.read orig (.read src (.reg 342))) dst (indices.map (fun i => (f i).val)) s hw
    (by simpa only [List.length_map] using hlen)
    (fun st hk => by
      simpa only [List.length_map] using eval_len
        ((hk.2 _ (by simpa only [List.mem_singleton] using hsd)).trans hsrc)
        (by simpa only [List.length_map] using hlen))
    (fun st i hi hk hri => by
      have hil : i < indices.length := by simpa only [List.length_map] using hi
      have hsa := (hk.2 src (by simpa only [List.mem_singleton] using hsd)).trans hsrc
      have hoa := (hk.2 orig (by simpa only [List.mem_singleton] using hod)).trans horig
      have his : i < (st.arrs src).length := by simpa only [hsa, List.length_map] using hil
      have hget : (st.arrs src)[i] = (indices[i]).val := by
        simp only [hsa, List.getElem_map]
      have hread := eval_read (a := src) (eval_reg hri (hil.trans hlen)) his
        (by rw [hget]; exact (indices[i]).isLt.trans hb)
      rw [hget] at hread
      have hio : (indices[i]).val < (st.arrs orig).length := by
        simpa only [hoa, List.length_ofFn] using (indices[i]).isLt
      have hgeto : (st.arrs orig)[(indices[i]).val] = (f indices[i]).val := by
        simp only [hoa, List.getElem_ofFn]
      have hout := eval_read (a := orig) hread hio
        (by rw [hgeto]; exact (f indices[i]).isLt.trans hn)
      simpa only [hgeto, List.getElem_map] using hout)
  refine ⟨s', t, he, ?_, hk, hout⟩
  simp only [Expr.cost_len, Expr.cost_read, Expr.cost_reg, List.length_map] at ht
  simpa only [Nat.mul_comm] using ht

end GraphMinor.Compute
