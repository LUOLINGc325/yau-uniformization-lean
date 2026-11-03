import Yau.Proofs.C07ChartChordEnergy
import Yau.Proofs.C07RadialCurvePath

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07ChartChordAux

open Yau Set Filter
open C07RadialCurveAux

variable {n : ℕ} {M : ComplexManifold n}

theorem chord_point_mem {R : ℝ} {a b : ComplexVector n}
    (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : a + t • (b - a) ∈ Metric.ball 0 R :=
  (convex_ball (0 : ComplexVector n) R).add_smul_sub_mem ha hb ht

def chordPath (ψ : ComplexVector n → M.Carrier) (a b : ComplexVector n) (t : ℝ) : M.Carrier :=
  ψ (a + radialClamp t • (b - a))

theorem chordPath_self (ψ : ComplexVector n → M.Carrier) (a : ComplexVector n) (t : ℝ) :
    chordPath ψ a a t = ψ a := by simp [chordPath]

theorem chordPath_mem_image (ψ : ComplexVector n → M.Carrier) {R : ℝ}
    {a b : ComplexVector n} (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R) (t : ℝ) :
    chordPath ψ a b t ∈ ψ '' Metric.closedBall (0 : ComplexVector n) R :=
  ⟨a + radialClamp t • (b - a),
    Metric.ball_subset_closedBall (chord_point_mem ha hb (radialClamp_mem t)), rfl⟩

theorem chord_image_isCompact {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) : IsCompact (ψ '' Metric.closedBall (0 : ComplexVector n) R) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    (hψ.continuousOn.mono (Metric.closedBall_subset_ball hRr))

/-- Continuity in both endpoints and the real path parameter, inside one
fixed chart domain. -/
theorem chordPath_continuousOn {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) :
    ContinuousOn (fun p : (ComplexVector n × ComplexVector n) × ℝ => chordPath ψ p.1.1 p.1.2 p.2)
      ((Metric.ball 0 R ×ˢ Metric.ball 0 R) ×ˢ Set.univ) := by
  have harg : Continuous (fun p : (ComplexVector n × ComplexVector n) × ℝ =>
      p.1.1 + radialClamp p.2 • (p.1.2 - p.1.1)) :=
    continuous_fst.fst.add ((continuous_radialClamp.comp continuous_snd).smul
      (continuous_fst.snd.sub continuous_fst.fst))
  exact hψ.continuousOn.comp harg.continuousOn fun p hp =>
    Metric.ball_subset_ball hRr.le (chord_point_mem hp.1.1 hp.1.2 (radialClamp_mem p.2))

theorem chordPath_eq (ψ : ComplexVector n → M.Carrier) (a b : ComplexVector n)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    chordPath ψ a b t = ψ ((1 - (t : ℂ)) • a + (t : ℂ) • b) := by
  unfold chordPath
  rw [radialClamp_eq ht]
  change ψ (a + (t : ℂ) • (b - a)) = ψ ((1 - (t : ℂ)) • a + (t : ℂ) • b)
  congr 1
  rw [smul_sub, sub_smul, one_smul]
  abel

theorem chordPath_continuous {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) {a b : ComplexVector n}
    (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R) : Continuous (chordPath ψ a b) :=
  hψ.continuousOn.comp_continuous
    (continuous_const.add (continuous_radialClamp.smul continuous_const))
    (fun t => Metric.ball_subset_ball hRr.le (chord_point_mem ha hb (radialClamp_mem t)))

theorem chordPath_piecewise_c1 {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) {a b : ComplexVector n}
    (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R)
    {t : ℝ} (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) :
    ContDiffAt ℝ 1 (fun s : ℝ => chartPt (chordPath ψ a b t) (chordPath ψ a b s)) t := by
  by_cases ht : t < 0
  · apply (contDiffAt_const (c := chartPt (chordPath ψ a b t) (ψ a))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [chordPath, radialClamp_of_neg hs, zero_smul, add_zero]
  · by_cases ht' : 1 < t
    · apply (contDiffAt_const (c := chartPt (chordPath ψ a b t) (ψ b))).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds ht'] with s hs
      simp only [chordPath, radialClamp_of_gt_one hs, one_smul]
      congr 1
      abel
    · have hti : t ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne (le_of_not_gt ht) ht₀.symm, lt_of_le_of_ne (le_of_not_gt ht') ht₁⟩
      have hq : a + t • (b - a) ∈ Metric.ball (0 : ComplexVector n) r :=
        Metric.ball_subset_ball hRr.le (chord_point_mem ha hb ⟨hti.1.le, hti.2.le⟩)
      have hψt := hψ.contMDiffAt (Metric.isOpen_ball.mem_nhds hq)
      have hG : ContDiffAt ℂ ∞ (fun w => chartPt (ψ (a + t • (b - a))) (ψ w))
          (a + t • (b - a)) := (contMDiffAt_extChartAt.comp _ hψt).contDiffAt
      have hline : ContDiffAt ℝ 1 (fun s : ℝ => a + s • (b - a)) t :=
        contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
      have hcomp := ((hG.restrict_scalars ℝ).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp t hline
      unfold chordPath
      rw [radialClamp_eq ⟨hti.1.le, hti.2.le⟩]
      apply hcomp.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
      rw [radialClamp_eq ⟨hs.1.le, hs.2.le⟩]
      rfl

def chordPiecewise {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) {a b : ComplexVector n}
    (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R) :
    PiecewiseC1Curve (ψ a) (ψ b) where
  toFun := chordPath ψ a b
  start_eq := by simpa using chordPath_eq ψ a b (t := 0) (by norm_num)
  finish_eq := by simpa using chordPath_eq ψ a b (t := 1) (by norm_num)
  breakpoints := {0, 1}
  breakpoints_mem := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> norm_num
  continuous_on := (chordPath_continuous hψ hRr ha hb).continuousOn
  piecewise_c1 := by
    intro t ht
    have hts : t ≠ 0 ∧ t ≠ 1 := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ht
    exact chordPath_piecewise_c1 hψ hRr ha hb hts.1 hts.2

theorem chord_derivative {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) {a b : ComplexVector n}
    (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    realTangentDerivative (chordPiecewise hψ hRr ha hb) t =
      mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) ψ (a + t • (b - a)) (b - a) := by
  let G : ComplexVector n → ComplexVector n := fun w => chartPt (ψ (a + t • (b - a))) (ψ w)
  have hq : a + t • (b - a) ∈ Metric.ball (0 : ComplexVector n) r :=
    Metric.ball_subset_ball hRr.le (chord_point_mem ha hb ⟨ht.1.le, ht.2.le⟩)
  have hψt := hψ.contMDiffAt (Metric.isOpen_ball.mem_nhds hq)
  have hG : ContDiffAt ℂ ∞ G (a + t • (b - a)) :=
    (contMDiffAt_extChartAt.comp _ hψt).contDiffAt
  have hGD := (hG.differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ
  have hline : HasDerivAt (fun s : ℝ => a + s • (b - a)) (b - a) t := by
    simpa using ((hasDerivAt_id t).smul_const (b - a)).const_add a
  have hcomp := hGD.comp_hasDerivAt t hline
  have heq : (fun s : ℝ => chartPt ((chordPiecewise hψ hRr ha hb) t)
      ((chordPiecewise hψ hRr ha hb) s)) =ᶠ[𝓝 t] (fun s => G (a + s • (b - a))) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    change chartPt (chordPath ψ a b t) (chordPath ψ a b s) = G (a + s • (b - a))
    simp only [chordPath, radialClamp_eq ⟨ht.1.le, ht.2.le⟩, radialClamp_eq ⟨hs.1.le, hs.2.le⟩]
    rfl
  have hder := hcomp.congr_of_eventuallyEq heq
  have hself := mfderivWithin_range_extChartAt_symm (I := ComplexModel n)
    (x := (chordPiecewise hψ hRr ha hb) t)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hself
  unfold realTangentDerivative
  rw [hself]
  change deriv (fun s : ℝ => chartPt ((chordPiecewise hψ hRr ha hb) t)
    ((chordPiecewise hψ hRr ha hb) s)) t = _
  rw [hder.deriv]
  unfold mfderiv
  rw [if_pos (hψt.mdifferentiableAt (by simp))]
  simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

theorem chord_speed_eq (k : HermitianField M)
    {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) {a b : ComplexVector n}
    (ha : a ∈ Metric.ball 0 R) (hb : b ∈ Metric.ball 0 R)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    curveSpeed k (chordPiecewise hψ hRr ha hb) t =
      Real.sqrt (2 * chartEnergy k ψ (a + t • (b - a)) (b - a)) := by
  unfold curveSpeed
  rw [chord_derivative hψ hRr ha hb ht]
  change Real.sqrt (2 * hermitianNormSq (k (ψ (a + radialClamp t • (b - a)))) _) = _
  rw [radialClamp_eq ⟨ht.1.le, ht.2.le⟩]
  rfl

end Yau.Proofs.C07ChartChordAux
