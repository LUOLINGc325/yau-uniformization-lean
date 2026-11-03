import Yau.Proofs.C04RescaledTubeHarnack

/-! Uniform scalar control on the fixed central ball, including negative
rescaled time. The negative half uses Harnack at the same spatial point. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs C04Aux
variable {n : ℕ}

theorem time_ratio_le_two {q d z w : ℝ} (hd : 0 < d) (hq : 4 * d ≤ q)
    (hz : |z| ≤ d) (hw : |w| ≤ d) :
    0 < q + z ∧ 0 ≤ (q + w) / (q + z) ∧ (q + w) / (q + z) ≤ 2 := by
  obtain ⟨hzl, hzu⟩ := abs_le.1 hz
  obtain ⟨hwl, hwu⟩ := abs_le.1 hw
  have hden : 0 < q + z := by linarith
  refine ⟨hden, div_nonneg (by linarith) hden.le, ?_⟩
  apply (div_le_iff₀ hden).2
  linarith

theorem rescaled_forward_central_scalar_bound (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (H : ℝ)
    (hHar : ∀ x y t t', 0 < t → t < t' →
      scalarCurvature (h t) x ≤ scalarCurvature (h t') y * (t' / t) *
        Real.exp (H * distFrom (h t) x y ^ 2 / (t' - t)))
    (ti R θ B r : ℝ) (hR : 0 < R) (hθ : 0 < θ) (hr : 0 < r) (hB : 0 < B)
    (hq : 16 * θ ≤ ti * R)
    (hbase : ∀ w, |w| ≤ 8 * θ → 0 < ti + w / R ∧
      scalarCurvature (scaleField R hR (h (ti + w / R))) o ≤ B)
    (x : Pt X) (hx : x ∈ distBall (scaleField R hR (h ti)) o (r + 2))
    {z : ℝ} (hz : z ∈ Set.Icc 0 (2 * θ)) :
    scalarCurvature (scaleField R hR (h (ti + z / R))) x ≤
      2 * B * Real.exp ((|H| + 1) * (r + 2) ^ 2 / (2 * θ)) := by
  have hzabs : |z| ≤ 8 * θ := by rw [abs_of_nonneg hz.1]; linarith [hz.2]
  have hfour : |4 * θ| ≤ 8 * θ := by rw [abs_of_pos (by positivity : 0 < 4 * θ)]; linarith
  have hzero := (hbase 0 (by simp; positivity)).1
  simp only [zero_div, add_zero] at hzero
  have hs0 := metricSmooth_scale R hR (h ti)
    (localizedFlow_metricSmooth X o h U P ρ hf hzero.le)
  have hsz := metricSmooth_scale R hR _
    (localizedFlow_metricSmooth X o h U P ρ hf (hbase z hzabs).1.le)
  have hrad : 0 < r + 2 := by linarith
  have hd0 := (L23Aux.mem_distBall_iff _ o x hrad).1 hx
  have hdmon := rescaled_distance_monotone X o h U P ρ hf hH ti R hR
    (z := 0) (w := z) (by simpa only [zero_div, add_zero] using hzero.le) hz.1 o x
  simp only [zero_div, add_zero] at hdmon
  have hsym := L23Aux.inducedDistance_symm (scaleField R hR (h (ti + z / R))) hsz x o
  have hdist : distFrom (scaleField R hR (h (ti + z / R))) x o < r + 2 := by
    change inducedDistance _ x o < _
    rw [hsym]
    exact hdmon.trans_lt hd0
  have hdistnonneg := L23Aux.inducedDistance_nonneg
    (scaleField R hR (h (ti + z / R))) hsz x o
  have hsq : distFrom (scaleField R hR (h (ti + z / R))) x o ^ 2 ≤ (r + 2) ^ 2 :=
    (sq_le_sq₀ hdistnonneg hrad.le).2 hdist.le
  have hden : 2 * θ ≤ 4 * θ - z := by linarith [hz.2]
  have hdenpos : 0 < 4 * θ - z := (by positivity : 0 < 2 * θ).trans_le hden
  have hnum : H * distFrom (scaleField R hR (h (ti + z / R))) x o ^ 2 ≤
      (|H| + 1) * (r + 2) ^ 2 := by
    have hHle : H ≤ |H| + 1 := by linarith [le_abs_self H]
    exact (mul_le_mul_of_nonneg_right hHle (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsq (by positivity))
  have hexp : Real.exp (H * distFrom (scaleField R hR (h (ti + z / R))) x o ^ 2 /
      (4 * θ - z)) ≤ Real.exp ((|H| + 1) * (r + 2) ^ 2 / (2 * θ)) := by
    apply Real.exp_le_exp.2
    exact (div_le_div_of_nonneg_right hnum hdenpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
  have hratio := time_ratio_le_two (d := 4 * θ) (q := ti * R) (z := z) (w := 4 * θ)
    (by positivity) (by nlinarith)
    (by rw [abs_of_nonneg hz.1]; linarith [hz.2]) (by simp [abs_of_pos hθ])
  have hfuture := (hbase (4 * θ) hfour).2
  have hfuturepos : 0 ≤ scalarCurvature (scaleField R hR (h (ti + (4 * θ) / R))) o := by
    rw [scalar_scaleField]
    exact mul_nonneg (inv_nonneg.2 hR.le)
      (scalar_pos X o h hH (hbase _ hfour).1.le o).le
  have hh := rescaled_integrated_harnack X o h U P ρ hf H hHar ti R hR x o
    (hbase z hzabs).1 (show z < 4 * θ by linarith [hz.2])
  calc
    _ ≤ scalarCurvature (scaleField R hR (h (ti + 4 * θ / R))) o *
        ((ti * R + 4 * θ) / (ti * R + z)) *
        Real.exp (H * distFrom (scaleField R hR (h (ti + z / R))) x o ^ 2 /
          (4 * θ - z)) := hh
    _ ≤ B * 2 * Real.exp ((|H| + 1) * (r + 2) ^ 2 / (2 * θ)) := by
      have hm := mul_le_mul hfuture hratio.2.2 hratio.2.1 hB.le
      exact mul_le_mul hm hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

theorem rescaled_central_scalar_bound (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (θ B r : ℝ)
    (hθ : 0 < θ) (hr : 0 < r) (hB : 0 < B) :
    ∃ A : ℝ, 0 < A ∧ ∀ ti R (hR : 0 < R),
      16 * θ ≤ ti * R →
      (∀ w, |w| ≤ 8 * θ → 0 < ti + w / R ∧
        scalarCurvature (scaleField R hR (h (ti + w / R))) o ≤ B) →
      ∀ x ∈ distBall (scaleField R hR (h ti)) o (r + 2),
      ∀ z ∈ Set.Icc (-2 * θ) (2 * θ),
        scalarCurvature (scaleField R hR (h (ti + z / R))) x ≤ A := by
  obtain ⟨H, hHar⟩ := hH.2.2.2.2.2.2.2.1
  let E := Real.exp ((|H| + 1) * (r + 2) ^ 2 / (2 * θ))
  have hE : 0 < E := Real.exp_pos _
  refine ⟨1 + 4 * B * E, by positivity, ?_⟩
  intro ti R hR hq hbase x hx z hz
  have hforward (v : ℝ) (hv : v ∈ Set.Icc 0 (2 * θ)) :
      scalarCurvature (scaleField R hR (h (ti + v / R))) x ≤ 2 * B * E :=
    rescaled_forward_central_scalar_bound X o h U P ρ hf hH H hHar
      ti R θ B r hR hθ hr hB hq hbase x hx hv
  by_cases hz0 : 0 ≤ z
  · have hh := hforward z ⟨hz0, hz.2⟩
    change scalarCurvature _ x ≤ 1 + 4 * B * E
    change scalarCurvature _ x ≤ 2 * B * E at hh
    nlinarith
  · have hzneg : z < 0 := lt_of_not_ge hz0
    have hzabs : |z| ≤ 8 * θ := by rw [abs_of_neg hzneg]; linarith [hz.1]
    have htime := (hbase z hzabs).1
    have hs := metricSmooth_scale R hR _
      (localizedFlow_metricSmooth X o h U P ρ hf htime.le)
    have hh := rescaled_integrated_harnack X o h U P ρ hf H hHar ti R hR x x htime hzneg
    have hself := L23Aux.inducedDistance_self (scaleField R hR (h (ti + z / R))) hs x
    simp only [zero_div, add_zero, distFrom, hself, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_div, Real.exp_zero, mul_one] at hh
    have hratio := time_ratio_le_two (d := 4 * θ) (q := ti * R) (z := z) (w := 0)
      (by positivity) (by nlinarith)
      (by rw [abs_of_neg hzneg]; linarith [hz.1]) (by simp; positivity)
    have hcentral := hforward 0 ⟨le_rfl, by positivity⟩
    simp only [zero_div, add_zero] at hcentral
    have hscalar : 0 ≤ scalarCurvature (scaleField R hR (h ti)) x := by
      rw [scalar_scaleField]
      have ht := (hbase 0 (by simp; positivity)).1
      simp only [zero_div, add_zero] at ht
      exact mul_nonneg (inv_nonneg.2 hR.le) (scalar_pos X o h hH ht.le x).le
    have hm := mul_le_mul_of_nonneg_left hratio.2.2 hscalar
    simp only [add_zero] at hm
    change scalarCurvature _ x ≤ 1 + 4 * B * E
    change scalarCurvature _ x ≤ 2 * B * E at hcentral
    nlinarith

end Yau.Proofs.C04RescaledTubeAux
