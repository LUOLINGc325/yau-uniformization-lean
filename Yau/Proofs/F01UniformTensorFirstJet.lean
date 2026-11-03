import Yau.Proofs.F01UniformFirstJetBudget

/-! The next actual background jet controls the supremum and first
spatial derivative of the tensor of any fixed preceding order. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau.LeafProofs.L17Aux
variable {ι E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_tensor_first_jet {f : ι → E → F} {s : ι → Set E} (k : ℕ)
    (hf : UniformJetBounds (k + 1) f s) :
    UniformJetBounds 1 (fun i => iteratedFDeriv ℝ k (f i)) s := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨C, hC, ?_⟩
  intro i x hx j hj
  interval_cases j
  · simpa only [norm_iteratedFDeriv_zero] using hb i x hx k (Nat.le_succ _)
  · simpa only [norm_iteratedFDeriv_one, norm_fderiv_iteratedFDeriv] using
      hb i x hx (k + 1) le_rfl

end Yau.NodeProofs.F01Aux
