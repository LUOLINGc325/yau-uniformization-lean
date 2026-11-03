import Yau.Proofs.F04SupportedCutoff
import Yau.Proofs.F04ScalarExteriorLocality
import Yau.Proofs.F03ScalarForms

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Only local L2 membership of df is asserted. The smooth function itself
need not have compact support or zero boundary trace on the domain. -/
theorem scalarExterior_L2_on_compact_domain
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O K : Set M.Carrier) (hO : MeasurableSet O) (hK : IsCompact K) (hOK : O ⊆ K)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    L2RealForm g.form (μ.restrict O) (scalarExterior f) := by
  obtain ⟨η, W, hη, hcη, _hηU, hWo, hKW, _hWU, hηone, _hηrange⟩ :=
    exists_supported_smooth_cutoff K univ hK isOpen_univ (subset_univ _)
  let q := fun x => η x * f x
  have hq : SmoothFn q := fun c => (hη c).mul (hf c)
  have heq : EqOn q f W := by
    intro x hx
    change η x * f x = f x
    rw [hηone x hx, one_mul]
  have hAE : ∀ᵐ x ∂μ.restrict O, scalarExterior q x = scalarExterior f x := by
    filter_upwards [ae_restrict_mem hO] with x hx
    exact scalarExterior_congr_on_open hq hf W hWo heq x (hKW (hOK hx))
  exact l2RealForm_of_ae_eq g.form hAE
    (scalarExterior_l2_restrict g μ hμ O hq hcη.mul_right)

end Yau.F04Proof
