import Yau.Proofs.F01ACompactActualBounds
import Yau.Proofs.F01AAmbientApproximationSequence
import Yau.Proofs.F01AAmbientPotentialJets
import Yau.Proofs.F01AOriginalChartEllipticity

/-! Every fixed original holomorphic chart receives genuine uniform
local scalar solution data from the continued approximants. All constants
precede the level and the actual solution, including the ellipticity and
the closed-time logarithmic determinant bound. -/
noncomputable section
open Set Metric
open scoped Topology Manifold ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem actual_original_chart_uniform_solution_data
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {c : ℝ} (hc : 0 ≤ c)
    (hgrowth : ∀ x, Ξ x ≤ c * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)))
    (e : OpenPartialHomeomorph (ComplexVector n) X.manifold.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {r T : ℝ} (hball : closedBall 0 r ⊆ e.source) (hT : 0 < T) :
    ∃ L0 Mclock ell upper : ℝ, 0 < L0 ∧ 0 ≤ Mclock ∧ 0 < ell ∧ ell ≤ upper ∧
      ∀ (L : ℝ), L0 ≤ L → ∀ ho : u o < L,
        let N := sublevelManifold X.manifold u hu.1 o L ho
        let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
        ∀ (Tsol : ℝ) (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ),
          T < Tsol → NativePotentialSlab α Tsol h U →
          let F : Point n → ℝ := fun p =>
            ambientApproximationPotential X o u hu L ho U (e p.1) p.2
          ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T) ∧
          (∀ z ∈ ball 0 r, F (z,0) = 0) ∧
          (∀ z ∈ ball 0 r, ∀ t ∈ Icc 0 T,
            HasDerivWithinAt (fun s => F (z,s))
              (localNativePotentialClock (pullbackMatrix X.metric.form e) F (z,t)) (Icc 0 T) t) ∧
          (∀ p ∈ ball 0 r ×ˢ Icc 0 T,
            |localNativePotentialClock (pullbackMatrix X.metric.form e) F p| ≤ Mclock) ∧
          ∀ p ∈ ball 0 r ×ˢ Icc 0 T,
            (localNativePotentialMatrix (pullbackMatrix X.metric.form e) F p -
              (ell : ℂ) • 1).PosSemidef ∧
            ((upper : ℂ) • 1 - localNativePotentialMatrix (pullbackMatrix X.metric.form e) F p).PosSemidef := by
  let K : Set (Pt X) := e '' closedBall 0 r
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn.mono hball)
  have hg : MetricSmooth X.metric.form := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  obtain ⟨a0, Lb, A, c0, R, ha0, hLb, hA, hc0, hR, hBounds⟩ :=
    actual_compact_uniform_bounds X o u hu Ξ hΞ hRic hc hgrowth hK hT
  obtain ⟨Li, hLi, hIdentity⟩ := compact_ambient_approximate_flow_identity X o u hu hK
  obtain ⟨Le, hLe, hExact⟩ := compact_approximation_identity X o u hu hK
  obtain ⟨D, hD, hBackground⟩ := original_chart_compact_matrix_sandwich
    X.metric.form hg e he hei (isCompact_closedBall _ _) hball
  let L0 : ℝ := max Lb (max Li Le)
  let ell : ℝ := c0 * D⁻¹
  let upper : ℝ := max ell (Real.exp (2 * R) * D)
  have hDp : 0 < D := zero_lt_one.trans_le hD
  refine ⟨L0, A, ell, upper, hLb.trans_le (le_max_left _ _), hA,
    mul_pos hc0 (inv_pos.mpr hDp), le_max_left _ _, ?_⟩
  intro L hLL0 ho
  dsimp only
  intro Tsol h U hTsol hslab
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  let f := ambientApproximationPotential X o u hu L ho U
  let F : Point n → ℝ := fun p => f (e p.1) p.2
  have hLb' : Lb ≤ L := (le_max_left _ _).trans hLL0
  have hLi' : Li ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLL0)
  have hLe' : Le ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLL0)
  have hLp : 0 < L := hLb.trans_le hLb'
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 Tsol := fun t ht => ⟨ht.1, ht.2.trans hTsol.le⟩
  obtain ⟨hh0, hh, hU, hU0, Cpre, hCpre, hdata⟩ := hslab
  have hslab' : NativePotentialSlab α Tsol h U := ⟨hh0, hh, hU, hU0, Cpre, hCpre, hdata⟩
  have hB := hBounds L hLb' ho Tsol h U hTsol hslab'
  obtain ⟨hInside, hAmbient⟩ := hIdentity L hLi' ho
  have hAmbient' := hAmbient h U (Icc 0 T)
    (fun x t ht => (hdata x t (hsub ht)).2.2.1)
    (fun x t ht => ((hdata x t (hsub ht)).2.2.2).mono hsub)
  have hInside' (z : ComplexVector n) (hz : z ∈ ball 0 r) : e z ∈ sublevelComponent u o L :=
    hInside ⟨z, ball_subset_closedBall hz, rfl⟩
  let lift (z : ComplexVector n) (hz : z ∈ ball 0 r) : N.Carrier := ⟨e z, hInside' z hz⟩
  have hLiftK (z : ComplexVector n) (hz : z ∈ ball 0 r) : (lift z hz).val ∈ K :=
    ⟨z, ball_subset_closedBall hz, rfl⟩
  have hNative (z : ComplexVector n) (hz : z ∈ ball 0 r) (t : ℝ) (ht : t ∈ Icc 0 T) :
      gMat (h t) (lift z hz) = nativePotentialMatrix X.metric.form f t (e z) :=
    (hAmbient' (lift z hz) (hLiftK z hz) t ht).1
  have hReg (z : ComplexVector n) (hz : z ∈ ball 0 r) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContDiffAt ℝ 2 (inChart (e z) (fun y => f y t)) (chartPt (e z) (e z)) :=
    (openExtendedPotential_inChart_contDiffAt (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) U hU (lift z hz) (hsub ht)).of_le (by simp)
  have hClock (z : ComplexVector n) (hz : z ∈ ball 0 r) (t : ℝ) (ht : t ∈ Icc 0 T) :
      localNativePotentialClock (pullbackMatrix X.metric.form e) F (z,t) =
        flowLogDetRatio α h (lift z hz) t := by
    have hPos : (nativePotentialMatrix X.metric.form f t (e z)).PosDef := by
      rw [← hNative z hz t ht]
      exact Yau.LeafProofs.L12Aux.hMat_posDef (h t) _ _ (mem_extChartAt_target _)
    rw [localNativePotentialClock_eq_native_ratio X.metric.form hg f e he hei
      (hball (ball_subset_closedBall hz)) t (hReg z hz t ht) hPos,
      ← hNative z hz t ht]
    have hBase := ((hExact L hLe' ho).2 (lift z hz) (hLiftK z hz)).2.1
    change Real.log ((gMat (h t) (lift z hz)).det.re / (gMat X.metric.form (e z)).det.re) = _
    unfold flowLogDetRatio
    rw [hBase]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact openExtendedPotential_holomorphic_chart_smooth X.manifold
      (sublevelOpens X.manifold u hu.1 o L) (sublevelComponent_isConnected ho) U
      (fun x => (hU x).mono (prod_mono Subset.rfl hsub)) e he
      (ball_subset_closedBall.trans hball) hInside'
  · intro z hz
    exact ambientApproximationPotential_initial X o u hu L ho U hU0 (e z)
  · intro z hz t ht
    rw [hClock z hz t ht]
    exact ((hAmbient' (lift z hz) (hLiftK z hz) t ht).2).congr_deriv (by
      unfold flowLogDetRatio
      rw [((hExact L hLe' ho).2 (lift z hz) (hLiftK z hz)).2.1])
  · rintro ⟨z,t⟩ ⟨hz,ht⟩
    rw [hClock z hz t ht]
    exact (hB (lift z hz) (hLiftK z hz) t ht).1
  · rintro ⟨z,t⟩ ⟨hz,ht⟩
    let J := linearMatrix (coordinateDifferential e (e z) z)
    have hm := localNativePotentialMatrix_eq_native_congruence X.metric.form hg f e he hei
      (hball (ball_subset_closedBall hz)) t (hReg z hz t ht)
    have hBase := ((hExact L hLe' ho).2 (lift z hz) (hLiftK z hz)).2.1
    have hb := hB (lift z hz) (hLiftK z hz) t ht
    have hLow := hb.2.2.2.1
    have hHi := hb.2.2.2.2
    have hLone : 1 ≤ L := by
      have hLevel := (hu.2.2.1 o).trans ho.le
      exact hLevel
    have hHi' : ((Real.exp (2 * R) : ℂ) • gMat α (lift z hz) -
        gMat (h t) (lift z hz)).PosSemidef := real_metric_upper_order_mono
      (H := gMat α (lift z hz))
      (Yau.LeafProofs.L12Aux.hMat_posDef α (lift z hz) _ (mem_extChartAt_target _)).posSemidef
      (Real.exp_le_exp.mpr (div_le_self (by positivity : 0 ≤ 2 * R) hLone)) hHi
    rw [hBase, hNative z hz t ht] at hLow hHi'
    have hLowChart := hLow.conjTranspose_mul_mul_same J
    have hHiChart := hHi'.conjTranspose_mul_mul_same J
    have hG := pullbackMatrix_eq_congruence X.metric.form e (e z) z (mem_extChartAt_source (e z))
    have hRelative :
        (localNativePotentialMatrix (pullbackMatrix X.metric.form e) F (z,t) -
          (c0 : ℂ) • pullbackMatrix X.metric.form e z).PosSemidef ∧
        ((Real.exp (2 * R) : ℂ) • pullbackMatrix X.metric.form e z -
          localNativePotentialMatrix (pullbackMatrix X.metric.form e) F (z,t)).PosSemidef := by
      rw [hm, hG]
      constructor
      · simpa only [J, gMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using hLowChart
      · simpa only [J, gMat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using hHiChart
    have hRange := relative_scalar_matrix_sandwich hc0.le (Real.exp_pos _).le
      (hBackground z (ball_subset_closedBall hz)).1 (hBackground z (ball_subset_closedBall hz)).2
      hRelative.1 hRelative.2
    exact ⟨hRange.1, real_metric_upper_order_mono Matrix.PosSemidef.one (le_max_right _ _) hRange.2⟩

end Yau.NodeProofs.F01Aux
