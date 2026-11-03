import Yau.Proofs.P02CircleSupports
import Yau.Proofs.D02RealPshConversion
import Yau.LeafProofs.L17HolomorphicRegularity
import Yau.LeafProofs.L17RicciNaturality

open scoped ContDiff Topology Matrix ComplexOrder

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Yau.LeafProofs Filter

/-- A nonvanishing holomorphic vector-valued map has plurisubharmonic
logarithmic norm. Supporting complex linear functionals provide genuine
local pluriharmonic lower supports at every point. -/
theorem log_norm_isPshOn_of_nonvanishing {n m : ℕ}
    {Ω : Set (ComplexVector n)} (hΩ : IsOpen Ω)
    {f : ComplexVector n → ComplexVector m} (hf : DifferentiableOn ℂ f Ω)
    (hne : ∀ z ∈ Ω, f z ≠ 0) :
    IsPshOn (fun z => (Real.log ‖f z‖ : EReal)) Ω := by
  have hfc := L17Holomorphic.complexVector_contDiffOn hΩ hf
  let q : ComplexVector n → ℝ := fun z => (1 / 2 : ℝ) * Real.log (‖f z‖ ^ 2)
  have hqeq : q = fun z => Real.log ‖f z‖ := by
    funext z
    dsimp [q]
    rw [Real.log_pow]
    ring
  have hqc : ContinuousOn q Ω := by
    rw [hqeq]
    exact hf.continuousOn.norm.log (fun z hz => norm_ne_zero_iff.mpr (hne z hz))
  have hline := Yau.NodeProofs.P02Aux.complexLinePshOn_of_lower_supports Ω q hqc
    (by
      intro a ha
      obtain ⟨ℓ, hℓnorm, hℓa⟩ := exists_dual_vector ℂ (f a) (norm_ne_zero_iff.mpr (hne a ha))
      let g : ComplexVector n → ℂ := fun z => ℓ (f z)
      have hgc : ContDiffAt ℂ 2 g a :=
        ℓ.contDiff.contDiffAt.comp a ((hfc.contDiffAt (hΩ.mem_nhds ha)).of_le (by simp))
      have hga : g a ≠ 0 := by
        dsimp [g]
        rw [hℓa]
        exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne a ha))
      have hlog := L17Aux.contDiffAt_log_normSq hgc hga
      let v : ComplexVector n → ℝ := fun z => (1 / 2 : ℝ) * Real.log (Complex.normSq (g z))
      have hvc : ContDiffAt ℝ 2 v a := contDiffAt_const.mul hlog
      have hvL : leviC v a = 0 := by
        rw [show v = fun z => (1 / 2 : ℝ) * Real.log (Complex.normSq (g z)) from rfl,
          L17Aux.leviC_const_mul hlog, L17Aux.leviC_log_normSq_holomorphic hgc hga, smul_zero]
      refine ⟨v, hvc, ?_, ?_, ?_⟩
      · have hnorm : ‖g a‖ = ‖f a‖ := by
          dsimp [g]
          rw [hℓa]
          simpa using (Complex.norm_of_nonneg (show 0 ≤ (algebraMap ℝ ℝ) ‖f a‖ by
            simpa using norm_nonneg (f a)))
        simp only [v, q, Complex.normSq_eq_norm_sq, hnorm]
      · filter_upwards [hgc.continuousAt.eventually_ne hga] with z hz
        have hnorm : ‖g z‖ ≤ ‖f z‖ := by
          simpa only [g, hℓnorm, one_mul] using ℓ.le_opNorm (f z)
        have hlogle := Real.log_le_log (pow_pos (norm_pos_iff.mpr hz) 2)
          (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
        change (1 / 2 : ℝ) * Real.log (Complex.normSq (g z)) ≤
          (1 / 2 : ℝ) * Real.log (‖f z‖ ^ 2)
        rw [Complex.normSq_eq_norm_sq]
        exact mul_le_mul_of_nonneg_left hlogle (by norm_num)
      · exact (L22Aux.leviC_posSemidef_iff hvc).mp
          (hvL.symm ▸ (Matrix.PosSemidef.zero : (0 : Blueprint.Herm n).PosSemidef)))
  rw [hqeq] at hline
  exact Yau.NodeProofs.D02Aux.isPshOn_of_complexLinePshOn hline

end Yau.Proofs.C07Aux
