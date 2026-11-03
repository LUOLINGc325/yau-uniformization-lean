import Yau.Proofs.F04NonlinearMassEstimate
import Yau.Proofs.F04CompactMassLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- Nonlinear vanishing follows by finite-radius Gronwall FIRST, followed
 by the compact-mass radius limit. Closed C0 at the initial face suffices. -/
theorem smooth_nonlinear_unique_with_cutoff
    (hG02 : G02) {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T C β : ℝ} {k : ℕ} (hT : 0 < T) (hC : 0 < C) (hβ : 0 < β) (hk : 2*n ≤ k)
    {χ w : STF X} (hχ : SmoothSpaceC1Time χ (Icc 0 T)) (hw : SmoothSpaceTime w (Ioo 0 T))
    (hwC : ContinuousOn (fun p : Pt X × ℝ => w p.1 p.2) (univ ×ˢ Icc 0 T))
    (hInitial : ∀ x, w x 0 = 0)
    (hdata : ∀ x t, t ∈ Icc 0 T →
      0 < χ x t ∧ χ x t ≤ C*(u x)^(-(k : ℤ)) ∧
      gradNormSq X.metric.form (fun y => χ y t) x ≤ (C*χ x t/u x)^2 ∧
      HermLE (levi (fun y => χ y t) x) (((C*χ x t : ℝ) : ℂ) • gMat (h t) x) ∧
      (0 < t → deriv (χ x) t ≤ C*(1+t^(β-1))*χ x t))
    (hwBound : ∀ x t, t ∈ Icc 0 T → 0 ≤ w x t ∧ w x t ≤ ρ x t)
    (hEq : ∀ x t, t ∈ Ioo 0 T → deriv (w x) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
      (1-Real.exp (-w x t))*scalarCurvature (h t) x) :
    ∀ x t, t ∈ Icc 0 T → w x t = 0 := by
  obtain ⟨E,_hE,hFinite⟩ := finite_nonlinear_mass_estimate hG02 X o h U P ρ hloc u hu μ hμ
    hT hC hβ hk hχ hw hwC hInitial hdata hwBound hEq
  have hden : SmoothSpaceTime (density ρ) (Icc 0 T) := (massVolumeTransport o h U P ρ hloc T hT).1
  intro x t ht
  let f : Pt X → ℝ := fun y => (Real.exp (w y t)-1)*χ y t*density ρ y t
  have hwSlice : Continuous (fun y => w y t) := hwC.comp_continuous
    (continuous_id.prodMk continuous_const) (fun y => ⟨mem_univ y,ht⟩)
  have hfc : Continuous f := (((Real.continuous_exp.comp hwSlice).sub continuous_const).mul
    (Yau.LeafProofs.L18Aux.continuous_of_smoothFn (hχ.1 t ht))).mul
    (Yau.LeafProofs.L18Aux.continuous_of_smoothFn ((smoothSpaceTime_c1 hden).1 t ht))
  have hf0 (y : Pt X) : 0 ≤ f y := mul_nonneg (mul_nonneg
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (hwBound y t ht).1)) (hdata y t ht).1.le) (density_pos ρ y t).le
  have hZero : ∀ N : ℕ, (∫ y, massCutoff u ((N : ℝ)+1) y*f y ∂μ) = 0 := by
    apply monotone_mass_eq_zero_of_error_tendsto
      (E*t*Real.exp ((((n : ℝ)+1)*C)*(t+t^β/β)))
      (compact_mass_monotone X o u hu μ hμ hfc hf0)
      (fun N => integral_nonneg (fun y => mul_nonneg (massCutoff_range u ((N : ℝ)+1) y).1 (hf0 y)))
      (e := fun N : ℕ => ((N : ℝ)+1)^(-(1 : ℝ)))
    · intro N
      calc
        _ ≤ (E/((N : ℝ)+1))*t*Real.exp ((((n : ℝ)+1)*C)*(t+t^β/β)) :=
          hFinite ((N : ℝ)+1) (by have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N; linarith) t ht
        _ = (E*t*Real.exp ((((n : ℝ)+1)*C)*(t+t^β/β)))*((N : ℝ)+1)^(-(1 : ℝ)) := by
          rw [Real.rpow_neg_one]; ring
    · exact cutoff_error_tendsto_zero (show (0 : ℝ) < 1 by norm_num)
  have hfx := compact_masses_zero_implies_zero X o u hu μ hμ hfc hf0 hZero x
  have he : (Real.exp (w x t)-1)*(χ x t*density ρ x t) = 0 := by simpa only [f,mul_assoc] using hfx
  have hZ : Real.exp (w x t)-1 = 0 := (mul_eq_zero.mp he).resolve_right
    (mul_ne_zero (hdata x t ht).1.ne' (density_pos ρ x t).ne')
  exact le_antisymm (by linarith only [self_le_exponential_sub_one (w x t),hZ]) (hwBound x t ht).1

/-- Only the EXACT registered dependencies supply the controlled
 exhaustion, initial volume and integrable cutoff for nonlinear vanishing. -/
theorem smooth_nonlinear_uniqueness_from_dependencies
    (hP07 : P07) (hF03 : F03) (hG02 : G02)
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) {w : STF X}
    (hw : SmoothSpaceTime w (Ioo 0 T))
    (hwC : ContinuousOn (fun p : Pt X × ℝ => w p.1 p.2) (univ ×ˢ Icc 0 T))
    (hInitial : ∀ x, w x 0 = 0)
    (hwBound : ∀ x t, t ∈ Icc 0 T → 0 ≤ w x t ∧ w x t ≤ ρ x t)
    (hEq : ∀ x t, t ∈ Ioo 0 T → deriv (w x) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
      (1-Real.exp (-w x t))*scalarCurvature (h t) x) :
    ∀ x t, t ∈ Icc 0 T → w x t = 0 := by
  obtain ⟨u,hu⟩ := hP07 n X o
  obtain ⟨μ,hμ,_⟩ := hG02 n X.manifold X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)
  obtain ⟨β,hβ,k₀,hCut⟩ := hF03 n X o h U P ρ hloc u hu T hT
  let k := max k₀ (2*n)
  obtain ⟨χ,C,hC,hχ,_hExtra,hData⟩ := hCut k (le_max_left _ _)
  apply smooth_nonlinear_unique_with_cutoff hG02 X o h U P ρ hloc u hu μ hμ hT hC hβ
    (k := k) (le_max_right _ _) hχ hw hwC hInitial
  · intro x t ht
    have hx := hData x t ht
    exact ⟨hx.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,hx.2.2.2.2.2⟩
  · exact hwBound
  · exact hEq

end Yau.F04Proof
