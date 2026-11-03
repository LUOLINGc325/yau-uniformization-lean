import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! A continuous linear-map field fixing each radial vector has identity
value at the origin. The limiting scalar is a parameter, not a chart choice. -/

noncomputable section
open Filter
open scoped Topology
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linearField_origin_eq_identity (B : E → E →L[ℝ] E) (hB : Continuous B)
    (hRad : ∀ x, B x x = x) : B 0 = ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro z
  have hf : Continuous (fun s : ℝ => B (s • z) z) :=
    (hB.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
  have heq : (fun s : ℝ => B (s • z) z) =ᶠ[𝓝[≠] (0 : ℝ)] (fun _ => z) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 0 := hs
    have he := hRad (s • z)
    rw [map_smul] at he
    have hcancel := congrArg (fun v : E => s⁻¹ • v) he
    simpa only [smul_smul, inv_mul_cancel₀ hs', one_smul] using hcancel
  have ht : Tendsto (fun s : ℝ => B (s • z) z) (𝓝[≠] (0 : ℝ)) (𝓝 (B 0 z)) := by
    simpa only [zero_smul] using (hf.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  exact tendsto_nhds_unique ht ((tendsto_congr' heq).mpr tendsto_const_nhds)

end Yau.Blueprint.C02Proof
