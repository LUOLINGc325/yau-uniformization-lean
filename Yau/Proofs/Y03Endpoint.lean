import Yau.Blueprint.Alignment

/-! Exact one-sided endpoint derivative order for scalar quadratic comparisons. -/

open scoped Topology
open Filter Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem left_endpoint_derivative_le {u v : ℝ → ℝ} {a b du dv : ℝ} (hab : a < b)
    (horder : ∀ t ∈ Icc a b, u t ≤ v t) (heq : u a = v a)
    (hu : HasDerivAt u du a) (hv : HasDerivAt v dv a) : du ≤ dv := by
  have hlim := (hu.sub hv).tendsto_slope.mono_left (nhdsGT_le_nhdsNE a)
  have hsign : ∀ᶠ t in 𝓝[>] a, slope (fun x => u x - v x) a t ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    rw [slope_def_field]
    simp only [heq, sub_self, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (horder t ⟨ht.1.le, ht.2.le⟩))
      (sub_nonneg.2 ht.1.le)
  have h := le_of_tendsto hlim hsign
  linarith

theorem right_endpoint_derivative_ge {u v : ℝ → ℝ} {a b du dv : ℝ} (hab : a < b)
    (horder : ∀ t ∈ Icc a b, u t ≤ v t) (heq : u b = v b)
    (hu : HasDerivAt u du b) (hv : HasDerivAt v dv b) : dv ≤ du := by
  have hlim := (hu.sub hv).tendsto_slope.mono_left (nhdsLT_le_nhdsNE b)
  have hsign : ∀ᶠ t in 𝓝[<] b, 0 ≤ slope (fun x => u x - v x) b t := by
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    rw [slope_def_field]
    simp only [heq, sub_self, sub_zero]
    exact div_nonneg_of_nonpos (sub_nonpos.2 (horder t ⟨ht.1.le, ht.2.le⟩))
      (sub_nonpos.2 ht.2.le)
  have h := ge_of_tendsto hlim hsign
  linarith

end Yau.Blueprint.Alignment.Y03Proof
