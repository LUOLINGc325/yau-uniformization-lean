import Yau.Proofs.E02BaseTimeJetContinuity
import Yau.Proofs.E02FixedCoefficientLimit

open Matrix Filter
open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- Pass κ to zero at the ACTUAL common base/time limit. The SAME PSD
subsequence handles every positive vertical coefficient loss, and the
ordinary physical time error vanishes. -/
theorem exists_actual_base_time_majorant_limit {n : ℕ}
    (f : ComplexVector n × ℝ → ℝ) (a : ComplexVector n × ℝ)
    (hf : ContDiffAt ℝ 2 f a) (B : Herm n) (hB : B.PosDef) (c : ℝ) (hc : 0 < c)
    (base : ℕ → ComplexVector n × ℝ) (hBase : Tendsto base atTop (𝓝 a))
    (error : ℕ → ℝ) (hError : Tendsto error atTop (𝓝 0))
    (L : ℕ → Herm n) (hL : ∀ j, (L j).PosSemidef)
    (hDom : ∀ j, (L j-leviC (fun z => f (z,(base j).2)) (base j).1).PosSemidef)
    (hLoss : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop,
      (c-r)*tracePair B (L j) ≤ deriv (fun t => f ((base j).1,t)) (base j).2+error j) :
    ∃ K : Herm n, K.PosSemidef ∧ (K-leviC (fun z => f (z,a.2)) a.1).PosSemidef ∧
      c*tracePair B K ≤ deriv (fun t => f (a.1,t)) a.2 := by
  have hS : Tendsto (fun j => leviC (fun z => f (z,(base j).2)) (base j).1)
      atTop (𝓝 (leviC (fun z => f (z,a.2)) a.1)) :=
    (continuousAt_baseTime_leviC f a hf).tendsto.comp hBase
  have hTime : Tendsto (fun j => deriv (fun t => f ((base j).1,t)) (base j).2+error j)
      atTop (𝓝 (deriv (fun t => f (a.1,t)) a.2)) := by
    simpa only [add_zero,Function.comp_def] using
      ((continuousAt_baseTime_time_deriv f a hf).tendsto.comp hBase).add hError
  exact exists_psd_limit_forall_coefficient_losses B hB L
    (fun j => leviC (fun z => f (z,(base j).2)) (base j).1)
    (leviC (fun z => f (z,a.2)) a.1)
    (fun j => deriv (fun t => f ((base j).1,t)) (base j).2+error j)
    (deriv (fun t => f (a.1,t)) a.2) c hc hL hDom hS hTime hLoss

end Yau.NodeProofs.E02Aux
