import Yau.Proofs.D02JensenPotential
import Yau.Proofs.D02JensenLogL1
import Yau.Proofs.D02JensenHarmonic

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02JensenAux

/-- The actual L08 decomposition, the compact L¹ bound, the harmonic mean
value property and Jensen together give the all-index exponential estimate
used in D02. No harmonic lower bound or exponential bound is an antecedent. -/
theorem uniform_exp_three_halves {O : Set ℂ} (hO : IsOpen O)
    (ψ : ℕ → ℂ → ℝ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hball : Metric.closedBall z₀ R ⊆ O)
    (hψ : ∀ j, ContDiffOn ℝ ∞ (ψ j) O)
    (hΔ : ∀ j z, z ∈ O → 0 ≤ LeafCandidates.realPlanarLaplacian (ψ j) z)
    (b M : ℝ) (hb : 0 ≤ b) (hbcrit : b < 4 / 3)
    (hmass : ∀ j, LeafCandidates.smoothRieszMeasure (ψ j) z₀ R univ ≤ ENNReal.ofReal b)
    (hL1 : ∀ j, (∫ z in Metric.closedBall z₀ R, |ψ j z|) ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      IntegrableOn (fun z ↦ Real.exp (-((3 : ℝ) / 2) * ψ j z)) (Metric.ball z₀ (R / 4)) volume ∧
      (∫ z in Metric.ball z₀ (R / 4), Real.exp (-((3 : ℝ) / 2) * ψ j z)) ≤ C := by
  let p : ℝ := 3 / 2
  let D := Metric.ball z₀ R
  let K := Metric.closedBall z₀ (R / 2)
  let S := Metric.ball z₀ (R / 4)
  have hp : 0 ≤ p := by norm_num [p]
  have hpb : p * b < 2 := by dsimp [p]; linarith
  obtain ⟨L, hL, hLog⟩ := exists_uniform_logPotential_L1_bound z₀ R R b hb
  obtain ⟨B, hB, hExp⟩ := exists_uniform_exp_logPotential_bound z₀ R (R / 4) p b hp hpb
  let A := Real.pi * ((R / 4) ^ 2 - (R / 8) ^ 2)
  have hA : 0 < A := by dsimp [A]; apply mul_pos Real.pi_pos; nlinarith
  have hM : 0 ≤ M := (integral_nonneg fun z ↦ abs_nonneg (ψ 0 z)).trans (hL1 0)
  let H := (M + L) / A
  have hH : 0 ≤ H := div_nonneg (add_nonneg hM hL) hA.le
  refine ⟨Real.exp (p * H) * B, mul_nonneg (Real.exp_pos _).le hB, ?_⟩
  intro j
  let ν := LeafCandidates.smoothRieszMeasure (ψ j) z₀ R
  obtain ⟨hνfinite, hνatom, h, hh, hhΔ, hrepr⟩ :=
    LeafProofs.L08_smoothPlanarRieszDecomposition (ψ j) z₀ R hR
      ⟨O, hO, hball, hψ j, hΔ j⟩
  letI : IsFiniteMeasure ν := ⟨hνfinite⟩
  have hνD : ∀ᵐ w ∂ν, w ∈ Metric.ball z₀ R := by
    exact ae_restrict_mem measurableSet_ball
  have hmreal : (ν univ).toReal ≤ b := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmass j)
    simpa only [ENNReal.toReal_ofReal hb] using ht
  let P := fun z ↦ ∫ w, Real.log ‖w - z‖ ∂ν
  obtain ⟨hPi, hPL1⟩ := hLog ν (by infer_instance) hνD hmreal
  have hKD : K ⊆ D := by
    intro z hz
    change dist z z₀ < R
    have hz' : dist z z₀ ≤ R / 2 := hz
    linarith
  have hSD : S ⊆ D := Metric.ball_subset_ball (by linarith)
  have hKP : IntegrableOn P K volume := hPi.mono_set hKD
  have hPbound : (∫ z in K, |P z|) ≤ L := by
    exact (setIntegral_mono_set hPi.abs (Filter.Eventually.of_forall fun z ↦ abs_nonneg (P z))
      hKD.eventuallyLE).trans hPL1
  have hψi : IntegrableOn (ψ j) (Metric.closedBall z₀ R) volume :=
    ((hψ j).continuousOn.mono hball).integrableOn_compact (isCompact_closedBall _ _)
  have hKbig : K ⊆ Metric.closedBall z₀ R := Metric.closedBall_subset_closedBall (by linarith)
  have hψK := hψi.mono_set hKbig
  have hψbound : (∫ z in K, |ψ j z|) ≤ M :=
    (setIntegral_mono_set hψi.abs (Filter.Eventually.of_forall fun z ↦ abs_nonneg (ψ j z))
      hKbig.eventuallyLE).trans (hL1 j)
  have hhi : IntegrableOn h K volume :=
    (hh.continuousOn.mono hKD).integrableOn_compact (isCompact_closedBall _ _)
  have hrepr' : ∀ z ∈ D, ψ j z = h z + P z := by
    intro z hz
    simpa only [P, ν, norm_sub_rev] using (hrepr z hz).2
  have hhbound : (∫ z in K, |h z|) ≤ M + L := by
    have hle : (∫ z in K, |h z|) ≤ ∫ z in K, |ψ j z| + |P z| := by
      apply integral_mono_ae hhi.abs (hψK.abs.add hKP.abs)
      filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with z hz
      have heq : h z = ψ j z - P z := by linarith [hrepr' z (hKD hz)]
      rw [heq]
      exact abs_sub _ _
    rw [integral_add hψK.abs hKP.abs] at hle
    exact hle.trans (add_le_add hψbound hPbound)
  have hhpoint : ∀ z ∈ S, -H ≤ h z := by
    intro z hz
    have habs := (harmonic_abs_le_L1 hR hh hhΔ hz).trans
      (div_le_div_of_nonneg_right hhbound hA.le)
    change |h z| ≤ H at habs
    linarith [neg_abs_le (h z)]
  obtain ⟨hEi, hEB⟩ := hExp ν (by infer_instance) hνD hmreal
    (fun z hz ↦ by simpa only [norm_sub_rev] using (hrepr z (hSD hz)).1)
  have hsmall : Metric.closedBall z₀ (R / 4) ⊆ O := by
    exact (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have hψExp : IntegrableOn (fun z ↦ Real.exp (-p * ψ j z)) S volume := by
    exact ((Real.continuous_exp.comp_continuousOn
      (((hψ j).continuousOn.mono hsmall).const_mul (-p))).integrableOn_compact
        (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall
  refine ⟨hψExp, ?_⟩
  have hpoint : ∀ᵐ z ∂volume.restrict S,
      Real.exp (-p * ψ j z) ≤ Real.exp (p * H) * Real.exp (-p * P z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hhpoint z hz, hrepr' z (hSD hz)]
  have hle := integral_mono_ae hψExp (hEi.const_mul (Real.exp (p * H))) hpoint
  rw [integral_const_mul] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left hEB (Real.exp_pos _).le)

end Yau.NodeProofs.D02JensenAux
