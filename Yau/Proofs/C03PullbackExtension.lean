import Yau.Proofs.C03PullbackSmooth

/-! The cutoff extension is globally smooth and still has the exact original
pullback coefficients on the inner ball. -/

noncomputable section
open Set
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem hMat_euclidean_field (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (x z : (ComplexEuclideanManifold n hn).Carrier) (a b : Fin n) :
    hMat k x z a b = (k z).toFun (stdVec a) (stdVec b) := by
  have hInv : chartInv x z = z := by
    change (extChartAt (ComplexModel n) (x : ComplexVector n)).symm z = z
    rw [extChartAt_model_space_eq_id]
    rfl
  unfold hMat
  rw [hInv, chartVec_euclidean, chartVec_euclidean]

theorem flat_pair_stdVec (hn : 1 ≤ n)
    (z : (ComplexEuclideanManifold n hn).Carrier) (a b : Fin n) :
    (flatHermitianField hn z).toFun (stdVec a) (stdVec b) =
      (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  change inner ℂ (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single b (1 : ℂ)) =
    if a = b then (1 : ℂ) else 0
  rw [EuclideanSpace.inner_single_left]
  simp [EuclideanSpace.single, PiLp.single_apply, eq_comm]

theorem cutoffPullbackField_hMat (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (χ : ComplexVector n → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hs : tsupport χ ⊆ Metric.ball (0 : ComplexVector n) r)
    (x z : (ComplexEuclideanManifold n hn).Carrier) (a b : Fin n) :
    hMat (cutoffPullbackField hn X Φ r hΦ χ hχ) x z a b =
      (χ z : ℂ) * pullbackMat X.metric.form Φ z a b +
        ((1 - χ z : ℝ) : ℂ) * (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [hMat_euclidean_field]
  by_cases hz : z ∈ Metric.ball (0 : ComplexVector n) r
  · rw [cutoffPullbackField_of_mem hn X Φ r hΦ χ hχ z hz,
      flat_pair_stdVec]
    rfl
  · have hzero : χ z = 0 := by
      by_contra hne
      exact hz (hs (subset_closure hne))
    rw [cutoffPullbackField_eq_flat_of_zero hn X Φ r hΦ χ hχ z hzero,
      flat_pair_stdVec]
    simp only [hzero, Complex.ofReal_zero, zero_mul, sub_zero, Complex.ofReal_one,
      one_mul, zero_add]

theorem cutoffPullbackField_hMat_contDiff (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (χ : ComplexVector n → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hχs : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Metric.ball (0 : ComplexVector n) r)
    (x : (ComplexEuclideanManifold n hn).Carrier) (a b : Fin n) :
    ContDiff ℝ ∞ (fun z => hMat (cutoffPullbackField hn X Φ r hΦ χ hχ) x z a b) := by
  have hp := contDiff_cutoff_product χ (fun z => pullbackMat X.metric.form Φ z a b)
    (Metric.ball 0 r) Metric.isOpen_ball hχs hs
    (pullbackMat_contDiffOn X.metric.form (metricSmooth_of_smoothMetric X.metric) hΦ.1 a b)
  have hq : ContDiff ℝ ∞ (fun z : ComplexVector n =>
      ((1 - χ z : ℝ) : ℂ) * (1 : Matrix (Fin n) (Fin n) ℂ) a b) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hχs)).mul contDiff_const
  convert hp.add hq using 1
  funext z
  exact cutoffPullbackField_hMat hn X Φ r hΦ χ hχ hs x z a b

theorem cutoffPullbackField_metricSmooth (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hΦ : IsLocalBiholomorphism Φ r)
    (χ : ComplexVector n → ℝ) (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hχs : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Metric.ball (0 : ComplexVector n) r) :
    MetricSmooth (cutoffPullbackField hn X Φ r hΦ χ hχ) := by
  intro x a b
  simp_rw [realMetricFn_entries]
  split_ifs
  · exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn
      (cutoffPullbackField_hMat_contDiff hn X Φ r hΦ χ hχ hχs hs x a.1 b.1).contDiffOn)
  · exact contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn
      (cutoffPullbackField_hMat_contDiff hn X Φ r hΦ χ hχ hχs hs x a.1 b.1).contDiffOn).neg
  · exact contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn
      (cutoffPullbackField_hMat_contDiff hn X Φ r hΦ χ hχ hχs hs x a.1 b.1).contDiffOn)

def chartCutoff (n : ℕ) (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ComplexVector n) :=
  ⟨3 * r / 4, 7 * r / 8, by positivity, by linarith⟩

theorem chartCutoff_tsupport_subset (r : ℝ) (hr : 0 < r) :
    tsupport (chartCutoff n r hr : ComplexVector n → ℝ) ⊆ Metric.ball 0 r := by
  rw [ContDiffBump.tsupport_eq]
  intro z hz
  have hz' : dist z 0 ≤ 7 * r / 8 := hz
  exact (show dist z 0 < r by linarith)

end Yau.Proofs.C03Aux
