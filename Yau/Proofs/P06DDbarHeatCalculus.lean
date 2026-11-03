import Yau.Proofs.G04ClosedHodge
import Yau.Proofs.P06WeakDDbarCurrentGreen
import Yau.Proofs.P06FiberContraction
import Yau.Proofs.P06ExteriorHeatResolvent

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.DDbarHeat
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem scalarForm_scalarValue (A : RealForm M 0) :
    scalarForm (WeakCurrent.scalarValue A) = A := by
  funext x
  ext V
  change A x Fin.elim0 = A x V
  congr 1
  exact Subsingleton.elim _ _

theorem scalarForm_compact (f : M.Carrier → ℝ) (hf : HasCompactSupport f) :
    CompactlySupportedRealForm (scalarForm f) := by
  apply hf.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx hz
  apply hx
  ext V
  change f x = 0
  exact hz

theorem scalarForm_support (f : M.Carrier → ℝ) :
    closure {x | scalarForm f x ≠ 0} ⊆ tsupport f := by
  apply closure_mono
  intro x hx hz
  apply hx
  ext V
  exact hz

theorem jPullback_add (A B : RealForm M 1) :
    jPullbackForm (A+B) = jPullbackForm A + jPullbackForm B := by
  funext x
  ext V
  rfl

theorem jPullback_smul (c : ℝ) (A : RealForm M 1) :
    jPullbackForm (c • A) = c • jPullbackForm A := by
  funext x
  ext V
  rfl

theorem dd_add (f q : M.Carrier → ℝ) (hf : SmoothFn f) (hq : SmoothFn q) :
    ddRealForm (f+q) = ddRealForm f + ddRealForm q := by
  have hj : jDifferential (f+q) = jDifferential f + jDifferential q := by
    unfold jDifferential
    rw [scalarForm_add, exteriorRealForm_add _ _ (scalarForm_smooth f hf)
      (scalarForm_smooth q hq), jPullback_add]
  unfold ddRealForm
  rw [hj, exteriorRealForm_add _ _ (jDifferential_smooth f hf) (jDifferential_smooth q hq), smul_add]

theorem dd_smul (c : ℝ) (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    ddRealForm (c • f) = c • ddRealForm f := by
  have hj : jDifferential (c • f) = c • jDifferential f := by
    unfold jDifferential
    rw [scalarForm_smul, exteriorRealForm_smul c _ (scalarForm_smooth f hf), jPullback_smul]
  unfold ddRealForm
  rw [hj, exteriorRealForm_smul c _ (jDifferential_smooth f hf), smul_smul, smul_smul]
  congr 1
  ring

theorem dd_sub (f q : M.Carrier → ℝ) (hf : SmoothFn f) (hq : SmoothFn q) :
    ddRealForm (f-q) = ddRealForm f - ddRealForm q := by
  simpa only [neg_one_smul ℝ q, neg_one_smul ℝ (ddRealForm q), ← sub_eq_add_neg] using
    (dd_add f ((-1 : ℝ) • q) hf (show SmoothFn ((-1 : ℝ) • q) from
      fun x => contDiffOn_const.mul (hq x))).trans
        (congrArg (fun A => ddRealForm f + A) (dd_smul (-1) q hq))

theorem dd_support (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    closure {x | ddRealForm f x ≠ 0} ⊆ tsupport f := by
  have hsm : closure {x | ddRealForm f x ≠ 0} ⊆
      closure {x | exteriorRealForm (jDifferential f) x ≠ 0} := by
    apply closure_mono
    intro x hx hz
    apply hx
    simp only [ddRealForm, Pi.smul_apply, hz, smul_zero]
  exact hsm.trans ((representsExterior_support_subset
    (exteriorRealForm_represents _ (jDifferential_smooth f hf))).trans
    ((WeakCurrent.jPullbackOne_support _).trans
    ((representsExterior_support_subset
      (exteriorRealForm_represents _ (scalarForm_smooth f hf))).trans (scalarForm_support f))))

theorem dd_compact (f : M.Carrier → ℝ) (hf : SmoothFn f) (hc : HasCompactSupport f) :
    CompactlySupportedRealForm (ddRealForm f) :=
  hc.of_isClosed_subset isClosed_closure (dd_support f hf)

theorem dd_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (hc : HasCompactSupport f) : L2RealForm g.form μ (ddRealForm f) :=
  smooth_compactlySupported_l2RealForm g μ hμ _ (dd_smooth f hf) (dd_compact f hf hc)

theorem trace_dd (g : HermitianField M) (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    formTrace g (ddRealForm f) = laplacian g f := by
  funext x
  unfold formTrace laplacian
  rw [formHermitianMatrix_of_representsIota _ _ (dd_properties f hf).2.2.2]

/-- The tailored normalization used by the second-order graph proof. -/
theorem hodge_scalar_eq_neg_two_trace_dd (g : SmoothMetric M) (hk : IsKahler g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    hodgeRealForm g.form 0 (scalarForm f) =
      (-2 : ℝ) • scalarForm (formTrace g.form (ddRealForm f)) := by
  rw [trace_dd g.form f hf]
  apply realForm_eq_of_center_components
  intro x I
  have hI : I = Fin.elim0 := Subsingleton.elim _ _
  rw [hI]
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hs := L12Aux.metricSmooth_of_smoothMetric g
  have he := hodge_represents g.form hs (scalarForm f) (scalarForm_smooth f hf)
    x (chartPt x x) hx Fin.elim0
  have hn := scalarHodgeNormalization g.form hs hk f hf x (chartPt x x) hx
  have hxinv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  simp only [formComponents_smul, Pi.smul_apply, smul_eq_mul]
  rw [scalarForm_components, he]
  change hodgeComponents g.form x 0 (formComponents (scalarForm f) x)
    (chartPt x x) Fin.elim0 = -2 * laplacian g.form f (chartInv x (chartPt x x))
  change -(hodgeComponents g.form x 0 (formComponents (scalarForm f) x)
    (chartPt x x) Fin.elim0) / 2 = laplacian g.form f (chartInv x (chartPt x x)) at hn
  linarith

theorem hodge_dd (g : SmoothMetric M) (hk : IsKahler g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    hodgeRealForm g.form 2 (ddRealForm f) =
      ddRealForm (WeakCurrent.scalarValue (hodgeRealForm g.form 0 (scalarForm f))) := by
  have hτ := trace_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g)
    _ (dd_smooth f hf) (dd_properties f hf).2.1
  rw [closed_oneOne_hodge g.form (L12Aux.metricSmooth_of_smoothMetric g) hk
    _ _ (dd_smooth f hf) (dd_properties f hf).2.1 (dd_properties f hf).2.2.1
      (hodge_represents g.form (L12Aux.metricSmooth_of_smoothMetric g) _ (dd_smooth f hf)),
    hodge_scalar_eq_neg_two_trace_dd g hk f hf]
  change (-2 : ℝ) • ddRealForm (formTrace g.form (ddRealForm f)) =
    ddRealForm ((-2 : ℝ) • formTrace g.form (ddRealForm f))
  exact (dd_smul (-2) _ hτ).symm

end Yau.NodeProofs.P06Aux.DDbarHeat
