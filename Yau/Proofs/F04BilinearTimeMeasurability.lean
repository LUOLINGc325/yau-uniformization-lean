import Yau.Proofs.F04BochnerGrowth

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.F04Proof

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Uniformly bounded scalar bilinear forms with continuous fixed-vector time
 profiles have genuine joint scalar continuity. No operator-norm continuity
 or dual-valued measurability premise is required. -/
theorem bounded_bilinear_time_joint_continuous
    (B : ℝ → V →L[ℝ] W →L[ℝ] ℝ) (C : ℝ) (hB : ∀ t, ‖B t‖ ≤ C)
    (hc : ∀ u v, Continuous (fun t => B t u v)) :
    Continuous (fun p : ℝ × V × W => B p.1 p.2.1 p.2.2) := by
  have hbound (t : ℝ) (u : V) (v : W) : ‖B t u v‖ ≤ C * ‖u‖ * ‖v‖ :=
    ((B t).le_opNorm₂ u v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _)) (norm_nonneg _))
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, u, v⟩
  let G := fun p : ℝ × V × W => B p.1 p.2.1 p.2.2 - B p.1 u v
  let E := fun p : ℝ × V × W => C * ‖p.2.1 - u‖ * ‖p.2.2‖ + C * ‖u‖ * ‖p.2.2 - v‖
  have hG (p : ℝ × V × W) : ‖G p‖ ≤ E p := by
    have he : B p.1 p.2.1 p.2.2 - B p.1 u v =
        B p.1 (p.2.1 - u) p.2.2 + B p.1 u (p.2.2 - v) := by
      simp only [map_sub, sub_apply]
      ring
    dsimp only [G, E]
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (hbound _ _ _) (hbound _ _ _))
  have hEc : Continuous E := by fun_prop
  have hEl : Tendsto E (𝓝 (t, u, v)) (𝓝 (0 : ℝ)) := by
    simpa only [E, sub_self, norm_zero, mul_zero, zero_mul, zero_add] using hEc.tendsto (t, u, v)
  have hGl : Tendsto G (𝓝 (t, u, v)) (𝓝 (0 : ℝ)) := squeeze_zero_norm hG hEl
  have ht := ((hc u v).tendsto t).comp (continuous_fst.tendsto (t, u, v))
  change Tendsto (fun p : ℝ × V × W => B p.1 p.2.1 p.2.2) (𝓝 (t, u, v)) (𝓝 (B t u v))
  simpa only [G, Function.comp_def, sub_add_cancel, zero_add] using hGl.add ht

/-- Actual Bochner L2 sections may be tested in the constructed time-dependent
 form, and their scalar pairing is genuinely integrable. -/
theorem bounded_bilinear_time_integrable
    (B : ℝ → V →L[ℝ] W →L[ℝ] ℝ) (C : ℝ) (hB : ∀ t, ‖B t‖ ≤ C)
    (hc : ∀ u v, Continuous (fun t => B t u v))
    (ν : Measure ℝ) {U : ℝ → V} {Z : ℝ → W}
    (hU : MemLp U 2 ν) (hZ : MemLp Z 2 ν) :
    Integrable (fun t => B t (U t) (Z t)) ν := by
  have hm := (bounded_bilinear_time_joint_continuous B C hB hc).comp_aestronglyMeasurable
    (aestronglyMeasurable_id.prodMk (hU.aestronglyMeasurable.prodMk hZ.aestronglyMeasurable))
  apply ((hU.norm.integrable_mul hZ.norm).const_mul C).mono' hm
  apply ae_of_all
  intro t
  have hb := ((B t).le_opNorm₂ (U t) (Z t)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _)) (norm_nonneg _))
  simpa only [mul_assoc, Pi.mul_apply, id_eq] using hb

end Yau.F04Proof
