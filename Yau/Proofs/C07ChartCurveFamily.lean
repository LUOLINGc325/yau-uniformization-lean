import Yau.Proofs.C07ChartChord
import Yau.Proofs.C07PolygonalPrefixConcat
import Yau.LeafProofs.L12

/-! A fixed initial curve followed by the actual radial chart chord. -/

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Set
open C07ChartChordAux C07PolygonalPrefixAux C07CurveConcatAux
open C07RadialCurveAux

variable {n : ℕ} {M : ComplexManifold n}

set_option maxHeartbeats 800000 in
theorem exists_chart_curve_family (g : SmoothMetric M) (o : M.Carrier)
    {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hR : 0 < R) (hRr : R < r) :
    ∃ (K : Set M.Carrier) (L : ℝ)
      (γ : ∀ z : Metric.ball (0 : ComplexVector n) R,
        IntegrableCurve g.form o (ψ z))
      (H : C(unitInterval × Metric.ball (0 : ComplexVector n) R, M.Carrier)),
      IsCompact K ∧ 0 ≤ L ∧
      (∀ p, H p = (γ p.2).1 p.1) ∧
      (∀ z, curveLength g.form (γ z).1 ≤ L) ∧
      (∀ z, ∀ u ∈ Icc (0 : ℝ) 1, (γ z).1 u ∈ K) := by
  let A := Metric.ball (0 : ComplexVector n) R
  have hzero : (0 : ComplexVector n) ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_self] using hR
  have hg : MetricSmooth g.form := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g
  obtain ⟨C, hC, hbound⟩ := exists_chord_length_bound (M := M) (k := g.form) hg hψ hRr
  let β : IntegrableCurve g.form o (ψ 0) :=
    Classical.choice (g.integrable_curve_nonempty o (ψ 0))
  let η : ∀ z : A, IntegrableCurve g.form (ψ 0) (ψ z) :=
    fun z => chordIntegrable hg hψ hRr hzero z.2
  let x : C(A, M.Carrier) := ContinuousMap.const _ o
  let y : C(A, M.Carrier) := ContinuousMap.const _ (ψ 0)
  let z : C(A, M.Carrier) :=
    ⟨fun z => ψ z, hψ.continuousOn.comp_continuous continuous_subtype_val
      (fun z => Metric.ball_subset_ball hRr.le z.2)⟩
  let P : C(unitInterval × A, M.Carrier) :=
    ⟨fun p => β.1 p.1,
      β.1.continuous_on.comp_continuous (continuous_subtype_val.comp continuous_fst)
        (fun p => p.1.2)⟩
  have harg : Continuous (fun p : unitInterval × A =>
      (0 : ComplexVector n) + radialClamp p.1 • ((p.2 : ComplexVector n) - 0)) :=
    continuous_const.add
      ((continuous_radialClamp.comp (continuous_subtype_val.comp continuous_fst)).smul
        ((continuous_subtype_val.comp continuous_snd).sub continuous_const))
  let Q : C(unitInterval × A, M.Carrier) :=
    ⟨fun p => chordPath ψ 0 p.2 p.1,
      hψ.continuousOn.comp_continuous harg (fun p =>
        Metric.ball_subset_ball hRr.le (chord_point_mem hzero p.2.2 (radialClamp_mem p.1)))⟩
  have hP : ∀ u a, P (u, a) = ((fun _ : A => β) a).1 u := fun _ _ => rfl
  have hQ : ∀ u a, Q (u, a) = (η a).1 u := fun _ _ => rfl
  obtain ⟨γ, H, hH, hlength, hγ⟩ :=
    concat_families (M := M) (g := g.form) x y z (fun _ => β) η P Q hP hQ
  let K := β.1 '' Icc (0 : ℝ) 1 ∪ ψ '' Metric.closedBall 0 R
  let L := max 0 (curveLength g.form β.1 + Real.sqrt (2 * C) * R)
  refine ⟨K, L, γ, H,
    (isCompact_Icc.image_of_continuousOn β.1.continuous_on).union
      (chord_image_isCompact hψ hRr), le_max_left _ _, ?_, ?_, ?_⟩
  · intro p
    exact hH p.1 p.2
  · intro a
    apply le_trans (le_of_eq (hlength a))
    apply le_trans (add_le_add (le_refl (curveLength g.form β.1))
      (hbound 0 hzero a a.2))
    apply le_trans _ (le_max_right _ _)
    apply add_le_add (le_refl _)
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    simpa only [sub_zero] using (show ‖(a : ComplexVector n)‖ ≤ R from
      le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using a.2))
  · intro a u hu
    rw [hγ, concatPath]
    split_ifs with ht
    · exact Or.inl ⟨2 * u, ⟨by linarith [hu.1], by linarith⟩, rfl⟩
    · exact Or.inr (chordPath_mem_image ψ hzero a.2 (2 * u - 1))

end Yau.Proofs.C07Aux
