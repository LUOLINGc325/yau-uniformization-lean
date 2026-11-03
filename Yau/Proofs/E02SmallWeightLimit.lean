import Yau.Proofs.E02WeightCoefficientLimit

open Matrix Filter Set
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The original B is fixed BEFORE all small contact lists. Their
cardinalities disappear before this final finite-dimensional limit. -/
theorem exists_psd_majorant_from_small_weights {n : ℕ}
    (B S : Herm n) (hB : B.PosDef) (r : ℝ)
    (hSmall : ∀ δ : ℝ, 0 < δ → δ < 1/2 →
      ∃ K : Herm n, K.PosSemidef ∧ (K-S).PosSemidef ∧
        (1-δ)^2*tracePair B K ≤ r) :
    ∃ K : Herm n, K.PosSemidef ∧ (K-S).PosSemidef ∧ tracePair B K ≤ r := by
  obtain ⟨δ,_hAnti,hδ,hδLim⟩ := exists_seq_strictAnti_tendsto' (by norm_num : (0:ℝ) < 1/2)
  have hBase : Tendsto (fun j => 1-δ j) atTop (𝓝 (1:ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hδLim
  have hLim : Tendsto (fun j => (1-δ j)^2) atTop (𝓝 (1:ℝ)) := by
    simpa only [one_pow] using hBase.pow 2
  have hCoeff : ∀ j, (1/4:ℝ) ≤ (1-δ j)^2 := by
    intro j
    have hD : (1/2:ℝ) ≤ 1-δ j := by linarith [(hδ j).2]
    have hSq := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1/2)
      (by linarith : (0:ℝ) ≤ 1-δ j)).mpr hD
    norm_num at hSq
    exact hSq
  exact exists_psd_majorant_limit_coefficients B S hB r (1/4) (by norm_num)
    (fun j => (1-δ j)^2) hCoeff hLim (fun j => hSmall (δ j) (hδ j).1 (hδ j).2)

end Yau.NodeProofs.E02Aux
