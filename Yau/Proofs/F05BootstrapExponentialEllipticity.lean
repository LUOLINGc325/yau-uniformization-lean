import Yau.Proofs.F05BootstrapDefinitions
import Yau.LeafProofs.L16DeGiorgiTruncation

/-! The original value bound supplies genuine ellipticity of exp(-u)A.
The constants use only the fixed value interval and background ellipticity. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_exp_principal_elliptic {Q : Set (Point n)} {A : Point n → Mat n}
    {lam upper K : ℝ} (hA : Elliptic Q A lam upper) (hK : 0 ≤ K)
    {u : Point n → ℝ} (hu : ∀ z ∈ Q, |u z| ≤ K) :
    Elliptic Q (fun z => Real.exp (-u z) • A z)
      (lam/Real.exp K) (upper/Real.exp (-K)) := by
  have hExp := elliptic_div_of_bounds (q := fun z => Real.exp (u z)) hA
    (Real.exp_pos (-K)) (Real.exp_le_exp.mpr (by linarith : -K ≤ K))
    (fun z hz => ⟨Real.exp_le_exp.mpr (abs_le.mp (hu z hz)).1,
      Real.exp_le_exp.mpr (abs_le.mp (hu z hz)).2⟩)
  simpa only [Real.exp_neg] using hExp

end Yau.Proofs.F05Aux
