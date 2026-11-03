import Yau.Proofs.V04NegativeLimits
import Yau.Proofs.V04FrequencySelection

/-! The actual negative-part error tends to zero in the epsilon limit:
energy cap, frequency shift, and full Frobenius Fejer error each keep
their original order and normalization. -/

open Filter
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

def negativeFamilyError (D C Q : ℝ) (B : ℝ → ℝ) (P : ℝ → ℕ) (ε : ℝ) : ℝ :=
  D * ε * (B ε + C * (P ε + 1)) + Q * Real.sqrt (C * B ε / (P ε : ℝ))

theorem negativeFamilyError_tendsto (D C Q : ℝ) (B : ℝ → ℝ) (P : ℝ → ℕ)
    (hB : Tendsto (fun ε => ε * B ε) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hP : IntermediateFrequency B P) :
    Tendsto (negativeFamilyError D C Q B P) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hmain : Tendsto (fun ε => D * (ε * B ε) + (D * C) * (ε * (P ε : ℝ)) + (D * C) * ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((tendsto_const_nhds.mul hB).add
      (tendsto_const_nhds.mul hP.2)).add (tendsto_const_nhds.mul hε)
  have hratio : Tendsto (fun ε => C * (B ε / (P ε : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hP.1
  have hsqrt : Tendsto (fun ε => Real.sqrt (C * (B ε / (P ε : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hratio)
  have hq : Tendsto (fun ε => Q * Real.sqrt (C * (B ε / (P ε : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hsqrt
  have hh := hmain.add hq
  convert hh using 1
  · funext ε
    unfold negativeFamilyError
    congr 1 <;> ring
  · simp

end Yau.Blueprint.V04Proof
