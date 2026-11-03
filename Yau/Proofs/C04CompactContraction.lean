import Yau.Proofs.C04TangentComparison
import Yau.Proofs.C04FieldSmooth
import Yau.LeafProofs.L12HopfRinow
import Yau.LeafProofs.L23FieldMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Compact initial geodesic families give uniform contraction of the actual length distance. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
open LeafProofs.L12Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem hermLE_trans {A B C : Herm n} (hAB : HermLE A B) (hBC : HermLE B C) :
    HermLE A C := by
  change (C - A).PosSemidef
  have heq : C - A = (C - B) + (B - A) := by abel
  rw [heq]
  exact hBC.add hAB

theorem hermLE_real_smul_mono (H : Herm n) (hH : H.PosSemidef)
    {a b : ℝ} (hab : a ≤ b) : HermLE ((a : ℂ) • H) ((b : ℂ) • H) := by
  have hc : (0 : ℂ) ≤ ((b - a : ℝ) : ℂ) :=
    Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr hab, by simp⟩
  have hh := hH.smul (α := ℂ) hc
  change (((b : ℂ) • H) - ((a : ℂ) • H)).PosSemidef
  rw [← sub_smul, ← Complex.ofReal_sub]
  exact hh

theorem radial_curveLength (g : SmoothMetric X) (o : X.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) o) :
    letI := manifold_realSmooth X
    letI := underlyingRealTangentNormedAddCommGroup g.form o
    curveLength g.form (piecewiseC1Curve_of_contMDiff
      ((realExponentialMap_radial_contMDiff g o v).of_le (by simp))) = ‖v‖ := by
  letI := manifold_realSmooth X
  letI : ∀ x : X.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) x) :=
    fun x => underlyingRealTangentNormedAddCommGroup g.form x
  let hf := (realExponentialMap_radial_contMDiff g o v).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  let γ := piecewiseC1Curve_of_contMDiff hf
  change curveLength g.form γ = ‖v‖
  rw [curveLength, integral_Icc_eq_integral_Ioo]
  calc
    ∫ t in Set.Ioo (0 : ℝ) 1, curveSpeed g.form γ t =
        ∫ _t in Set.Ioo (0 : ℝ) 1, ‖v‖ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      rw [← realCurveVelocity_norm g.form γ ht (by simp [γ, piecewiseC1Curve_of_contMDiff])]
      exact realExponentialMap_radial_speed g o v t
    _ = ‖v‖ := by simp

/-- C01's compact power metric bound controls the genuine distances from
the same basepoint, uniformly over the original compact set. -/
theorem compact_distance_power_bound (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ C a D : ℝ, 0 < C ∧ 0 < a ∧ 0 < D ∧
      ∀ t, 1 ≤ t → ∀ x ∈ K,
        distFrom (h t) o x ≤ Real.sqrt (C * t ^ (-a)) * D := by
  letI := manifold_realSmooth X.manifold
  obtain ⟨D₀, hD₀⟩ := hK.bddAbove_image
    ((continuous_inducedDistance X.metric).comp (continuous_const.prodMk continuous_id)).continuousOn
  let D := max D₀ 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  let K' : Set (Pt X) := {x | inducedDistance X.metric.form o x ≤ D}
  have hK' : IsCompact K' := isCompact_inducedDistance_sublevel X.metric o D
  obtain ⟨C₀, a, ha, hb⟩ := hH.2.2.2.2.2.2.2.2 K' hK'
  let C := max C₀ 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨C, a, D, hC, ha, hD, ?_⟩
  intro t ht x hx
  letI : ∀ y : Pt X, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup X.metric.form y
  letI : ∀ y : Pt X, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace X.metric.form y
  obtain ⟨v, hv, hvnorm⟩ := exists_minimizing_realExponential X.metric o x
  let f := fun s : ℝ => realExponentialMap X.metric o (s • v)
  have hfγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f :=
    (realExponentialMap_radial_contMDiff X.metric o v).of_le (by simp)
  let γ := piecewiseC1Curve_of_contMDiff hfγ
  have hf0 : f 0 = o := by simp [f, realExponentialMap_zero]
  have hf1 : f 1 = x := by simpa only [f, one_smul] using hv
  have hvD : ‖v‖ ≤ D := hvnorm.trans_le
    ((hD₀ (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _))
  have hpath : ∀ s ∈ Set.Icc (0 : ℝ) 1, f s ∈ K' := by
    intro s hs
    change inducedDistance X.metric.form o (f s) ≤ D
    calc
      inducedDistance X.metric.form o (f s) ≤ ‖s • v‖ :=
        inducedDistance_realExponentialMap_le X.metric o (s • v)
      _ = |s| * ‖v‖ := norm_smul s v
      _ ≤ ‖v‖ := by
        rw [abs_of_nonneg hs.1]
        exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg v)).trans_eq (one_mul _)
      _ ≤ D := hvD
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have htpow : 0 < t ^ (-a) := Real.rpow_pos_of_pos htpos _
  have hc : 0 ≤ C * t ^ (-a) := (mul_pos hC htpow).le
  have hkint := LeafProofs.L23Aux.integrable_curveSpeed_of_contMDiff (h t)
    (localizedFlow_metricSmooth X o h U P ρ hf htpos.le) hfγ
  have hgint := integrable_curveSpeed_of_contMDiff X.metric hfγ
  have hmetric : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HermLE (gMat (h t) (γ s)) (((C * t ^ (-a) : ℝ) : ℂ) • gMat X.metric.form (γ s)) := by
    intro s hs
    have hg : (gMat X.metric.form (γ s)).PosSemidef :=
      (LeafProofs.L18Aux.hMat_posDef X.metric.form (γ s) (chartPt (γ s) (γ s))
        (mem_extChartAt_target (γ s))).posSemidef
    exact hermLE_trans (hb t ht (γ s) (hpath s hs))
      (hermLE_real_smul_mono _ hg (mul_le_mul_of_nonneg_right (le_max_left _ _) htpow.le))
  have hlen := curveLength_le_of_HermLE (h t) X.metric.form γ _ hc hkint hgint hmetric
  have hdist := inducedDistance_le_curveLength (h t) (⟨γ, hkint⟩ : IntegrableCurve (h t) (f 0) (f 1))
  have hdist' : inducedDistance (h t) o x ≤ curveLength (h t) γ := by
    calc
      inducedDistance (h t) o x = inducedDistance (h t) (f 0) (f 1) := by rw [hf0, hf1]
      _ ≤ curveLength (h t) γ := hdist
  have hrad : curveLength X.metric.form γ = ‖v‖ := radial_curveLength X.metric o v
  rw [hrad] at hlen
  exact hdist'.trans (hlen.trans (mul_le_mul_of_nonneg_left hvD (Real.sqrt_nonneg _)))

end Yau.Proofs.C04Aux
