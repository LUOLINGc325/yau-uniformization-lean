import Yau.Proofs.U02CorrectedCauchy
import Yau.Proofs.U02InverseDifferential
import Yau.Proofs.U02RawCharts
import Yau.Proofs.U02ChartNeighborhood

/-! The actual metric lower bound excludes a kernel of the corrected
coordinate differential in every genuine local chart. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint
open Yau.LeafProofs.L12Aux

theorem corrected_limit_chart_derivative_injective {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho) (hw : RicciWindows X o h rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {psi : Pt X → ComplexVector n}
    (hpsi : ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ psi)
    (hshadow : ∀ K : Set (Pt X), IsCompact K → ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖(forwardComp G k).eval (psi x) - (H k).eval (f (tk k) x)‖ ≤
        Real.exp (-6 * rho o (tk k))) (x : Pt X) :
    Function.Injective (fderiv ℂ (fun z => psi (chartInv x z)) (chartPt x x)) := by
  obtain ⟨r, hr, hclosed, hK, hkappa, _V, _hV, _hxV, _hVL, _hsheet⟩ :=
    exists_compact_chart_neighborhood X.manifold x
  let b := chartPt x x
  let O := ball b (2 * r)
  let K := chartInv x '' closedBall b (2 * r)
  let q := fun k z => f (tk k) (chartInv x z)
  let pc := fun z => psi (chartInv x z)
  have hcenter : chartInv x b = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hxK : x ∈ K := ⟨b, mem_closedBall_self (by positivity), hcenter⟩
  have hbO : b ∈ O := mem_ball_self (by positivity)
  have hmapK : Set.MapsTo (chartInv x) O K := fun z hz => ⟨z, ball_subset_closedBall hz, rfl⟩
  have hraw := raw_compact_data hf hc hp ht hK
  have hq : ∀ᶠ k in atTop, DifferentiableOn ℂ (q k) O := by
    filter_upwards [hraw] with k hk
    obtain ⟨V, _hV, hKV, hdf, _hinv, _hsmall⟩ := hk
    exact (hdf.comp hkappa (fun z hz => hKV (hmapK hz))).differentiableOn
  have hpc : DifferentiableOn ℂ pc O :=
    ((hpsi.mdifferentiable (by simp)).comp_mdifferentiableOn hkappa).differentiableOn
  have hpoint : ∀ᶠ k in atTop, ‖q k b‖ ≤ Real.exp (-sigma * rho o (tk k)) := by
    filter_upwards [hraw] with k hk
    simpa only [q, hcenter] using hk.choose_spec.2.2.2.2 x hxK
  have hsh : ∀ᶠ k in atTop, ∀ z ∈ closedBall b (2 * (r / 2)),
      ‖(forwardComp G k).eval (pc z) - (H k).eval (q k z)‖ ≤ Real.exp (-6 * rho o (tk k)) := by
    filter_upwards [hshadow K hK] with k hk
    intro z hz
    apply hk (chartInv x z)
    exact ⟨z, closedBall_subset_closedBall (by linarith) hz, rfl⟩
  have hball : closedBall b (2 * (r / 2)) ⊆ O := closedBall_subset_ball (by linarith)
  have hkernel : ∀ v : ComplexVector n, fderiv ℂ pc b v = 0 → v = 0 := by
    intro v hker
    by_contra hv
    let w := chartVec x x v
    have hwne : w ≠ 0 := by
      intro hzero
      apply hv
      apply chartVec_injective x x (mem_extChartAt_source x)
      have hz0 : chartVec x x (0 : ComplexVector n) = 0 := by
        change (mfderiv (ComplexModel n) (ComplexModel n)
          (extChartAt (ComplexModel n) x).symm (chartPt x x))
            (0 : TangentSpace (ComplexModel n) (chartPt x x)) = 0
        exact map_zero _
      rw [hz0]
      exact hzero
    have hnorm : 0 < hermitianNormSq (X.metric.form x) w :=
      hermitianNormSq_pos _ hwne
    have hsmall := raw_derivative_small_of_limit_kernel hp isOpen_ball hq hpc hc.2.2.1
      (by positivity : 0 < r / 2) hball (mem_closedBall_self (by positivity)) hpoint hsh hker
    obtain ⟨cK, _hcK, T, hmetric⟩ := hw.2.2.2.2.2.2.1 K hK
    have hdecay : Tendsto (fun k => (C * ‖v‖ ^ 2) * Real.exp (-8 * rho o (tk k))) atTop (𝓝 0) := by
      have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (hp.2.1.const_mul_atTop (by norm_num : (0 : ℝ) < 8))
      simpa only [Function.comp_def, neg_mul, mul_zero] using
        (tendsto_const_nhds.mul hh :
          Tendsto (fun k => (C * ‖v‖ ^ 2) * _) atTop (𝓝 ((C * ‖v‖ ^ 2) * 0)))
    have hbad : ∀ᶠ k : ℕ in atTop, False := by
      filter_upwards [hraw, hsmall, eventually_models_time_ge hf hp ht (max t0 T),
        hdecay.eventually (gt_mem_nhds hnorm)] with k hk hsmallk htime hbudget
      obtain ⟨V, hV, hKV, hdf, hinv, _hdecay⟩ := hk
      have hxV := hKV hxK
      have hdfx := (hdf x hxV).mdifferentiableAt (hV.mem_nhds hxV)
      have hkc := (hkappa b hbO).mdifferentiableAt (isOpen_ball.mem_nhds hbO)
      have hchain : fderiv ℂ (q k) b v =
          mfderiv (ComplexModel n) 𝓘(ℂ, ComplexVector n) (f (tk k)) x w := by
        have hh := mfderiv_comp_apply_of_eq (x := b) hdfx hkc hcenter v
        rw [mfderiv_eq_fderiv] at hh
        exact hh
      have hcx := hc.2.2.2.2.1 (tk k) ((le_max_left _ _).trans htime)
      have hleft : ∀ᶠ y in 𝓝 x, Phi (tk k) (f (tk k) y) = y := by
        filter_upwards [hV.mem_nhds hxV] with y hy
        exact (hinv y hy).2.1
      have hmetricx := (hmetric (tk k) ((le_max_right _ _).trans htime) x hxK).1
      have hm := raw_inverse_differential_metric X.metric.form (h (tk k)) o x
        (Phi (tk k)) (f (tk k)) hcx (hinv x hxV).1 hdfx hleft hmetricx w
      rw [← hchain] at hm
      have hnormsq := sq_le_sq₀ (norm_nonneg (fderiv ℂ (q k) b v))
        (by positivity : 0 ≤ Real.exp (-5 * rho o (tk k)) * ‖v‖) |>.mpr hsmallk
      have hbound := hm.trans (mul_le_mul_of_nonneg_left hnormsq hc.2.2.2.1.le)
      have hpaid : hermitianNormSq (X.metric.form x) w ≤
          (C * ‖v‖ ^ 2) * Real.exp (-8 * rho o (tk k)) := by
        calc
          _ = Real.exp (2 * rho o (tk k)) *
              (Real.exp (-2 * rho o (tk k)) * hermitianNormSq (X.metric.form x) w) := by
            rw [← mul_assoc, ← Real.exp_add]
            simp
          _ ≤ Real.exp (2 * rho o (tk k)) *
              (C * (Real.exp (-5 * rho o (tk k)) * ‖v‖) ^ 2) :=
            mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
          _ = _ := by
            have he : Real.exp (-5 * rho o (tk k)) ^ 2 = Real.exp (-10 * rho o (tk k)) := by
              rw [pow_two, ← Real.exp_add]
              congr 1
              ring
            rw [mul_pow, he]
            rw [show Real.exp (2 * rho o (tk k)) *
                (C * (Real.exp (-10 * rho o (tk k)) * ‖v‖ ^ 2)) =
                (C * ‖v‖ ^ 2) * (Real.exp (2 * rho o (tk k)) *
                  Real.exp (-10 * rho o (tk k))) by ring, ← Real.exp_add]
            congr 2
            ring
      exact (not_lt_of_ge hpaid) hbudget
    obtain ⟨k, hk⟩ := hbad.exists
    exact hk
  intro v w hvw
  apply sub_eq_zero.mp
  apply hkernel (v - w)
  rw [map_sub, hvw, sub_self]

end Yau.NodeProofs.U02Proof
