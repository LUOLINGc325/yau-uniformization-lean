import Yau.Proofs.D02DirectionalCurvature
import Yau.Proofs.D02PullbackCurvatureCenter

/-! The actual squared differential norm has nonnegative intrinsic Levi
form, using the original same-metric bisectional curvature condition. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

def immersionComponentNormInChart (g : HermitianField M) (F : M.Carrier → ComplexVector N)
    (x : M.Carrier) (a : Fin N) (z : ComplexVector n) : ℝ :=
  dualNormMat (hMat g x z) (WithLp.toLp 2 (fun b => immersionDerivativeMatrix F x z a b))

theorem immersionComponentNormInChart_contDiffOn (g : HermitianField M) (hg : MetricSmooth g)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (x : M.Carrier) (a : Fin N) :
    ContDiffOn ℝ ∞ (immersionComponentNormInChart g F x a) (chartTarget x) := by
  have hJ (b : Fin n) : ContDiffOn ℝ ∞
      (fun z => immersionDerivativeMatrix F x z a b) (chartTarget x) :=
    (complex_holomorphic_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x)
      (immersionDerivativeMatrix_differentiableOn hF x a b)).restrict_scalars ℝ
  have hI (b c : Fin n) : ContDiffOn ℝ ∞ (fun z => (hMat g x z)⁻¹ c b) (chartTarget x) :=
    entrywise_matrix_inv_contDiffOn
      (Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg x)
      (fun z hz => ne_of_gt (hMat_posDef g x z hz).det_pos) c b
  change ContDiffOn ℝ ∞ (fun z =>
    (∑ b, star (immersionDerivativeMatrix F x z a b) *
      ∑ c, (hMat g x z)⁻¹ c b * immersionDerivativeMatrix F x z a c).re) (chartTarget x)
  exact Complex.reCLM.contDiff.comp_contDiffOn (ContDiffOn.sum fun b _ =>
    (Complex.conjCLE.contDiff.comp_contDiffOn (hJ b)).mul
      (ContDiffOn.sum fun c _ => (hI b c).mul (hJ c)))

theorem immersionComponentNorm_levi_posSemidef (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (x : Pt X) (a : Fin N) :
    (leviC (immersionComponentNormInChart X.metric.form F x a) (chartPt x x)).PosSemidef := by
  have hg := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hq : ContDiffAt ℝ 2 (immersionComponentNormInChart X.metric.form F x a) (chartPt x x) :=
    ((immersionComponentNormInChart_contDiffOn X.metric.form hg hF x a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  apply (Yau.LeafProofs.L22Aux.leviC_posSemidef_iff hq).mpr
  intro v
  rw [← mixedWirt_real_eq_LeviQuadratic hq v]
  have hqc : ContDiffAt ℝ 2
      (fun w => (immersionComponentNormInChart X.metric.form F x a w : ℂ)) (chartPt x x) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (chartPt x x) hq
  rw [Yau.LeafProofs.L14Aux.wirt_wirtBar_comm _ _ hqc v v]
  dsimp only [immersionComponentNormInChart]
  rw [immersionComponent_dualBochner X.metric.form hg hF x a hz v, Complex.add_re]
  apply add_nonneg
  · have hp := (hMat_posDef X.metric.form x (chartPt x x) hz).transpose.posSemidef.dotProduct_mulVec_nonneg
      (vectorWirt (raisedImmersionComponent X.metric.form F x a) (chartPt x x) v)
    exact (Complex.nonneg_iff.mp hp).1
  · rw [immersionDualCurvatureMatrix_center_pairing X.metric.form hg x v]
    exact kahlerManifold_nonnegBisectional X x _ v

theorem leviC_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ComplexVector n → ℝ) (z : ComplexVector n)
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) z) :
    leviC (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, leviC (f i) z := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    ext a b
    simp [leviC, leviMatrix, wirt, wirtBar]
  | @insert i s hi ih =>
    have hsum : ContDiffAt ℝ 2 (fun w => ∑ j ∈ s, f j w) z :=
      ContDiffAt.sum fun j _ => hf j
    simp only [Finset.sum_insert hi]
    rw [leviC_add_actual (hf i) hsum, ih]

/-- The actual u=|dF|² has the source's nonnegative Levi form. -/
theorem immersionDifferentialNormSq_levi_posSemidef (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) :
    ∀ x : Pt X, (levi (immersionDifferentialNormSq X.metric.form F) x).PosSemidef := by
  intro x
  have hg := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have he : inChart x (immersionDifferentialNormSq X.metric.form F) =ᶠ[𝓝 (chartPt x x)]
      (fun z => ∑ a, immersionComponentNormInChart X.metric.form F x a z) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with z hz'
    exact immersionDifferentialNormSq_in_fixed_chart X.metric.form hF x hz'
  have hq (a : Fin N) : ContDiffAt ℝ 2
      (immersionComponentNormInChart X.metric.form F x a) (chartPt x x) :=
    ((immersionComponentNormInChart_contDiffOn X.metric.form hg hF x a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  change (leviC (inChart x (immersionDifferentialNormSq X.metric.form F)) (chartPt x x)).PosSemidef
  rw [leviC_congr_of_eventuallyEq he, leviC_finset_sum Finset.univ _ _ hq]
  have hsum (s : Finset (Fin N)) :
      (∑ a ∈ s, leviC (immersionComponentNormInChart X.metric.form F x a) (chartPt x x)).PosSemidef := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (show (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef from Matrix.PosSemidef.zero)
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (immersionComponentNorm_levi_posSemidef X hF x a).add ih
  exact hsum Finset.univ

end Yau.NodeProofs.D02Aux
