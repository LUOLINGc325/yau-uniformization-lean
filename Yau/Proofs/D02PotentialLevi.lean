import Yau.Proofs.D02LogJacobian
import Yau.Proofs.P06ScalarUniquenessRicciPositive

/-! The original immersion potential has the source's genuine nonnegative
Levi form: log Gram contributes a nonnegative term and minus log det g
contributes the actual computed Ricci matrix of the same metric. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

theorem leviC_congr_of_eventuallyEq {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hfg : f =ᶠ[𝓝 z] g) : leviC f z = leviC g z := by
  ext i j
  exact mixedWirt_congr (hfg.mono fun y hy => congrArg (fun r : ℝ => (r : ℂ)) hy) _ _

/-- Real Hessian linearity for the actual nested Wirtinger matrix. -/
theorem leviC_add_actual {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    leviC (fun x => f x + g x) z = leviC f z + leviC g z := by
  apply Yau.LeafProofs.L17Aux.matrix_eq_of_quadratic_eq
  intro v
  rw [Matrix.add_mulVec, dotProduct_add]
  rw [Yau.LeafProofs.L22Aux.leviC_quadratic (hf.add hg) (WithLp.toLp 2 v),
    Yau.LeafProofs.L22Aux.leviC_quadratic hf (WithLp.toLp 2 v),
    Yau.LeafProofs.L22Aux.leviC_quadratic hg (WithLp.toLp 2 v),
    Yau.LeafProofs.L22Aux.complexLeviQuadratic_add hf hg]
  simp

theorem leviC_const_mul_actual {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) :
    leviC (fun x => c * f x) z = (c : ℂ) • leviC f z := by
  apply Yau.LeafProofs.L17Aux.matrix_eq_of_quadratic_eq
  intro v
  rw [Matrix.smul_mulVec, dotProduct_smul]
  rw [Yau.LeafProofs.L22Aux.leviC_quadratic ((contDiffAt_const (c := c)).mul hf)
    (WithLp.toLp 2 v), Yau.LeafProofs.L22Aux.leviC_quadratic hf (WithLp.toLp 2 v),
    Yau.LeafProofs.L22Aux.complexLeviQuadratic_const_mul hf c]
  simp [smul_eq_mul]

theorem leviC_sub_actual {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    leviC (fun x => f x - g x) z = leviC f z - leviC g z := by
  have heq : (fun x => f x - g x) = (fun x => f x + (-1) * g x) := by
    funext x
    ring
  rw [heq, leviC_add_actual hf (contDiffAt_const.mul hg), leviC_const_mul_actual hg (-1)]
  simp [sub_eq_add_neg]

/-- Exact curvature binding, with the original same-metric Ricci calculator. -/
theorem immersionPotential_levi_eq (g : HermitianField M) (hg : MetricSmooth g)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    (y : M.Carrier) :
    levi (immersionPotential g F) y =
      leviC (fun z => Real.log (immersionGram F y z).det.re) (chartPt y y) + ricci g y := by
  have hz : chartPt y y ∈ chartTarget y :=
    (extChartAt (ComplexModel n) y).map_source (mem_extChartAt_source y)
  have heq : inChart y (immersionPotential g F) =ᶠ[𝓝 (chartPt y y)]
      (fun z => Real.log (immersionGram F y z).det.re - Real.log (hMat g y z).det.re) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds hz] with z hz'
    exact immersionPotential_in_fixed_chart g hF hImm y hz'
  have hG : ContDiffAt ℝ 2 (fun z => Real.log (immersionGram F y z).det.re) (chartPt y y) :=
    ((log_immersionGram_contDiffOn hF hImm y).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds hz)).of_le (by simp)
  have hH : ContDiffAt ℝ 2 (logDet g y) (chartPt y y) :=
    ((Yau.LeafProofs.L17Aux.logDet_contDiffOn_of_metricSmooth g hg y).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y).mem_nhds hz)).of_le (by simp)
  change leviC (inChart y (immersionPotential g F)) (chartPt y y) = _
  have hH' : ContDiffAt ℝ 2 (fun z => Real.log (hMat g y z).det.re) (chartPt y y) := hH
  rw [leviC_congr_of_eventuallyEq heq, leviC_sub_actual hG hH']
  change _ - leviC (logDet g y) (chartPt y y) = _
  exact sub_eq_add_neg _ _

/-- Original complete Kähler data imply the Levi sign, without a curvature oracle. -/
theorem immersionPotential_levi_posSemidef (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) :
    ∀ y : Pt X, (levi (immersionPotential X.metric.form F) y).PosSemidef := by
  intro y
  rw [immersionPotential_levi_eq X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) hF hImm y]
  exact (log_immersionGram_levi_posSemidef hF hImm y
    ((extChartAt (ComplexModel n) y).map_source (mem_extChartAt_source y))).add
    (P06Aux.kahlerManifold_ricci_posSemidef X y)

end Yau.NodeProofs.D02Aux
