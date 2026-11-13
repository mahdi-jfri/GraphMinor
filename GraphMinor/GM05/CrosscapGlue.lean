module

public import GraphMinor.GM05.ModelBaseHalfTurn
import GraphMinor.GM19.CapModel

/-!
# The supported half turn respects the model identifications

For the crosscap obstruction needed in GM V, (8.10), a half turn around
one crosscap hole exchanges its antipodal boundary points. It fixes
all other boundary circles because their centres are at least three
apart. Thus it respects every handle and crosscap identification.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

private theorem base_half_turn_fixed {i n j : ℕ}
    (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre i)=dist x (modelCentre i))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre i) → Θ x=x)
    (hji : j ≠ i) {u : EuclideanPlane} (hu : ‖u‖=1)
    {p : modelBase n} (hp : p.1=(↑(modelCentre j+u) : OnePoint EuclideanPlane)) :
    modelBaseHalfTurn i n Θ hnorm hfix p=p := by
  apply Subtype.ext
  rw [modelBaseHalfTurn_apply_val,hp]
  change (↑(Θ (modelCentre j+u)) : OnePoint EuclideanPlane)=↑(modelCentre j+u)
  rw [supported_half_turn_fixes_other_boundary i j Θ hfix hji hu]

/-- The base half turn about crosscap `k` preserves the generating
identifications of the model surface. The other boundary circles are
fixed, and on the selected circle it exchanges antipodal points. -/
theorem crosscap_half_turn_preserves_glue {a b c k : ℕ} (hk : k<b)
    (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre (2*a+k))=dist x (modelCentre (2*a+k)))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre (2*a+k)) → Θ x=x)
    (hcircle : ∀ u : EuclideanPlane,‖u‖=1 →
      Θ (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u)
    {p q : modelBase (2*a+b+c)} (h : ModelGlue a b (2*a+b+c) p q) :
    ModelGlue a b (2*a+b+c)
      (modelBaseHalfTurn (2*a+k) (2*a+b+c) Θ hnorm hfix p)
      (modelBaseHalfTurn (2*a+k) (2*a+b+c) Θ hnorm hfix q) := by
  cases h with
  | handle j hj u hu p q hp hq =>
    have hpfix := base_half_turn_fixed Θ hnorm hfix (show 2*j ≠ 2*a+k by omega) hu hp
    have hqfix := base_half_turn_fixed Θ hnorm hfix (show 2*j+1 ≠ 2*a+k by omega)
      (show ‖modelMirror u‖=1 by rw [GM19.norm_modelMirror,hu]) hq
    rw [hpfix,hqfix]
    exact ModelGlue.handle j hj u hu p q hp hq
  | crosscap j hj u hu p q hp hq =>
    by_cases hjk : j=k
    · subst j
      apply ModelGlue.crosscap k hk (-u) (by rw [norm_neg,hu])
      · rw [modelBaseHalfTurn_apply_val,hp]
        change (↑(Θ (modelCentre (2*a+k)+u)) : OnePoint EuclideanPlane)=↑(modelCentre (2*a+k)+ -u)
        rw [hcircle u hu]
        rfl
      · rw [modelBaseHalfTurn_apply_val,hq]
        change (↑(Θ (modelCentre (2*a+k)-u)) : OnePoint EuclideanPlane)=↑(modelCentre (2*a+k)- -u)
        rw [sub_eq_add_neg,hcircle (-u) (by rw [norm_neg,hu])]
    · have hpfix := base_half_turn_fixed Θ hnorm hfix (show 2*a+j ≠ 2*a+k by omega) hu hp
      have hq' : q.1=(↑(modelCentre (2*a+j)+ -u) : OnePoint EuclideanPlane) := by simpa only [sub_eq_add_neg] using hq
      have hqfix := base_half_turn_fixed Θ hnorm hfix (show 2*a+j ≠ 2*a+k by omega)
        (show ‖-u‖=1 by rw [norm_neg,hu]) hq'
      rw [hpfix,hqfix]
      exact ModelGlue.crosscap j hj u hu p q hp hq

end GraphMinor.GM05
