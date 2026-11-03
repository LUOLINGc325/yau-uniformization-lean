import Yau.Proofs.P08CanonicalLogRicci
import Yau.Proofs.P08LogRegularizer
import Yau.Proofs.P06ScalarUniquenessRicciPositive

/-! The actual smooth canonical logarithms have the required weighted Ricci
lower bound at every point, including every zero of the section. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.Blueprint Yau.LeafProofs Yau.Proofs.P04Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- Positive regularization is globally smooth, with no condition on the
zero set of the given section. -/
theorem canonical_regularized_log_smooth (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) {ε : ℝ} (hε : 0 < ε) :
    SmoothFn (fun y => Real.log (canonicalNormSq g.form S y + ε)) := by
  intro a
  exact ((canonicalNormSq_smooth g S hS a).add contDiffOn_const).log
    (fun z _ => (add_pos_of_nonneg_of_pos (canonicalNormSq_nonneg g.form S _) hε).ne')

/-- Away from zeros use the convex scalar profile of the nonsingular
logarithm. At a zero, the regularized logarithm has an actual local minimum. -/
theorem canonical_regularized_levi_lower (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) {ε : ℝ} (hε : 0 < ε) (x : M.Carrier) :
    HermLE (((canonicalNormSq g.form S x / (canonicalNormSq g.form S x + ε) : ℝ) : ℂ) •
      ricci g.form x) (levi (fun y => Real.log (canonicalNormSq g.form S y + ε)) x) := by
  let q := canonicalNormSq g.form S
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hx : chartInv x z = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hq : SmoothFn q := canonicalNormSq_smooth g S hS
  have hw := canonical_regularized_log_smooth g S hS hε
  have hqz : inChart x q z = q x := congrArg q hx
  have hqnon : 0 ≤ q x := canonicalNormSq_nonneg g.form S x
  by_cases hzero : q x = 0
  · have hmin : IsLocalMin (inChart x (fun y => Real.log (q y + ε))) z := by
      apply Filter.Eventually.of_forall
      intro w
      change Real.log (q (chartInv x z) + ε) ≤ Real.log (q (chartInv x w) + ε)
      rw [hx, hzero, zero_add]
      exact Real.log_le_log hε (by linarith [canonicalNormSq_nonneg g.form S (chartInv x w)])
    have hp := leviC_posSemidef_at_local_min
      ((L18Aux.contDiffAt_inChart hw x hz).of_le (by simp)) hmin
    change (leviC (inChart x (fun y => Real.log (q y + ε))) z -
      (((q x / (q x + ε) : ℝ) : ℂ) • ricci g.form x)).PosSemidef
    change (leviC (inChart x (fun y => Real.log (q y + ε))) z).PosSemidef at hp
    simpa only [hzero, zero_div, Complex.ofReal_zero, zero_smul, sub_zero] using hp
  · have hpos : 0 < q x := lt_of_le_of_ne hqnon (Ne.symm hzero)
    have hlog : ContDiffAt ℝ 2 (fun w => Real.log (inChart x q w)) z :=
      ((L18Aux.contDiffAt_inChart hq x hz).of_le (by simp)).log
        (by rw [hqz]; exact hpos.ne')
    have hF : ContDiffAt ℝ 2 (logRegularizer ε) (Real.log (inChart x q z)) :=
      (logRegularizer_contDiff hε).contDiffAt.of_le (by simp)
    have hh := leviC_scalar_comp hlog hF
    have heq : (fun w => logRegularizer ε (Real.log (inChart x q w))) =ᶠ[𝓝 z]
        inChart x (fun y => Real.log (q y + ε)) := by
      filter_upwards [((L18Aux.contDiffAt_inChart hq x hz).continuousAt).eventually
        (Ioi_mem_nhds (by rw [hqz]; exact hpos))] with w hw
      dsimp only [logRegularizer]
      rw [Real.exp_log hw]
      rfl
    have hRic : leviC (fun w => Real.log (inChart x q w)) z = ricci g.form x :=
      levi_log_canonicalNormSq_at_pos g S hS x hpos
    rw [L22Aux.leviC_congr_of_eventuallyEq heq, hRic, logRegularizer_deriv hε,
      hqz, Real.exp_log hpos] at hh
    change (leviC (inChart x (fun y => Real.log (q y + ε))) z -
      (((q x / (q x + ε) : ℝ) : ℂ) • ricci g.form x)).PosSemidef
    rw [hh, add_sub_cancel_left]
    exact (gradientGram_posSemidef _ _).smul
      (Complex.zero_le_real.mpr (logRegularizer_deriv_deriv_nonneg hε _))

/-- Tracing the genuine matrix order preserves its normalization. -/
theorem traceWith_mono (g : HermitianField M) (x : M.Carrier)
    {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : HermLE A B) :
    traceWith (gMat g x) A ≤ traceWith (gMat g x) B := by
  have hH := L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)
  have h := P06Aux.matrix_trace_mul_nonneg (gMat g x)⁻¹ (B - A) hH.inv.posSemidef hAB
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg, traceWith] using h

/-- Both signs needed by the submean argument are consequences of the
original positive bisectional-curvature data. -/
theorem canonical_regularized_laplacian_lower (X : KahlerManifold n)
    (S : CanonicalSection X.manifold) (hS : IsHolomorphicCanonical S)
    {ε : ℝ} (hε : 0 < ε) (x : Pt X) :
    0 ≤ canonicalNormSq X.metric.form S x / (canonicalNormSq X.metric.form S x + ε) *
      scalarCurvature X.metric.form x ∧
    canonicalNormSq X.metric.form S x / (canonicalNormSq X.metric.form S x + ε) *
      scalarCurvature X.metric.form x ≤
        laplacian X.metric.form (fun y => Real.log (canonicalNormSq X.metric.form S y + ε)) x := by
  have hR : 0 ≤ scalarCurvature X.metric.form x :=
    P06Aux.matrix_trace_mul_nonneg _ _
      (L12Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).inv.posSemidef
      (P06Aux.kahlerManifold_ricci_posSemidef X x)
  refine ⟨mul_nonneg (div_nonneg (canonicalNormSq_nonneg _ _ _)
    (add_pos_of_nonneg_of_pos (canonicalNormSq_nonneg _ _ _) hε).le) hR, ?_⟩
  have h := traceWith_mono X.metric.form x (canonical_regularized_levi_lower X.metric S hS hε x)
  simpa only [traceWith, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    scalarCurvature, laplacian] using h

end Yau.NodeProofs.P08Aux
