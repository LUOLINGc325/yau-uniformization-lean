import Yau.Proofs.P06LocalMollification
import Yau.Proofs.P06MetricComparison

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03 Yau.LeafProofs.L18Aux

/-- Actual smooth local approximants retain an arbitrarily small relative
error in the original metric upper Levi bound. Both the sign of the upper
constant and the uniform metric comparison are proved from the datum. -/
theorem weakLeviUpper_local_approximation {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (hf : Continuous f) (C : ℝ)
    (hc : ConstantOutsideCompact f) (hw : WeakLeviUpper g.form f C)
    (x : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ chartTarget x) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ U : ComplexVector n → ℝ, ContDiff ℝ ∞ U ∧
      (∀ z ∈ K, |U z - inChart x f z| ≤ ε) ∧
      ∀ z ∈ K, HermLE (leviC U z) (((C * (1 + η) : ℝ) : ℂ) • hMat g.form x z) := by
  have hC : 0 ≤ C := weakLeviUpper_constantOutside_nonnegative g f C hc hw
  obtain ⟨r, hr, hlocal⟩ := weakLeviUpper_local_mollification g f hf C hw x K hK hKO ε hε
  obtain ⟨s, hs, hmetric⟩ := hMat_uniform_relative_upper g x hK hKO hη
  let d := min r s
  have hd : 0 < d := lt_min hr hs
  let φ : ContDiffBump (0 : ComplexVector n) :=
    ⟨d / 4, d / 2, by positivity, by linarith⟩
  have hφr : φ.rOut < r := (half_lt_self hd).trans_le (min_le_left r s)
  have hφs : φ.rOut < s := (half_lt_self hd).trans_le (min_le_right r s)
  obtain ⟨U, hU, happrox, hbound⟩ := hlocal φ hφr
  refine ⟨U, hU, happrox, ?_⟩
  intro z hz
  have hO : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  let ψ : ComplexVector n → ℝ := fun a => φ.normed volume (z - a)
  have hψ : ContDiff ℝ ∞ ψ := φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft z)
  have hnear (a : ComplexVector n) (ha : a ∈ tsupport ψ) : dist a z < s := by
    have hmem : z - a ∈ tsupport (φ.normed volume) := by
      change a ∈ tsupport (φ.normed volume ∘ Homeomorph.subLeft z) at ha
      rwa [tsupport_comp_eq_preimage] at ha
    rw [φ.tsupport_normed_eq] at hmem
    have hn : ‖z - a‖ ≤ φ.rOut := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hmem
    rw [dist_eq_norm, norm_sub_rev]
    exact hn.trans_lt hφs
  have hψO : tsupport ψ ⊆ chartTarget x :=
    fun a ha => (hmetric z hz a (hnear a ha)).1
  have hmass : (∫ a, ψ a) = 1 := by
    change (∫ a, φ.normed volume (z - a)) = 1
    rw [integral_sub_left_eq_self]
    exact φ.integral_normed
  have hG := Yau.LeafProofs.L12Aux.hMat_isHermitian g.form x z
  have hH : ((((C * (1 + η) : ℝ) : ℂ) • hMat g.form x z) - leviC U z).IsHermitian :=
    (hG.smul (by simp [IsSelfAdjoint])).sub
      (Yau.LeafProofs.L22Aux.leviC_isHermitian (hU.contDiffAt.of_le (by simp)))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self v).symm⟩
  let w := WithLp.toLp 2 v
  have hiG : Integrable (fun a => ψ a * leviDirection (hMat g.form x a) w) volume :=
    integrable_compactTest_mul volume hO hψ.continuous hcψ hψO
      (metricLeviDirection_contDiffOn g x w).continuousOn
  have hib : Integrable (fun a => ψ a * ((1 + η) * leviDirection (hMat g.form x z) w)) volume :=
    (hψ.continuous.integrable_of_hasCompactSupport hcψ).mul_const _
  have hq : (∫ a, ψ a * leviDirection (hMat g.form x a) w) ≤
      (1 + η) * leviDirection (hMat g.form x z) w := by
    calc
      _ ≤ ∫ a, ψ a * ((1 + η) * leviDirection (hMat g.form x z) w) := by
        apply integral_mono hiG hib
        intro a
        dsimp only
        by_cases ha : a ∈ tsupport ψ
        · exact mul_le_mul_of_nonneg_left ((hmetric z hz a (hnear a ha)).2 w)
            (φ.nonneg_normed _)
        · rw [image_eq_zero_of_notMem_tsupport ha, zero_mul, zero_mul]
      _ = _ := by rw [integral_mul_const, hmass, one_mul]
  have hfinal := (hbound z hz w).trans (mul_le_mul_of_nonneg_left hq hC)
  have hnonneg : 0 ≤ C * (1 + η) * leviDirection (hMat g.form x z) w -
      leviDirection (leviC U z) w := by nlinarith
  simpa only [w, leviDirection, WithLp.ofLp_toLp, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul] using hnonneg

end Yau.NodeProofs.P06Aux
