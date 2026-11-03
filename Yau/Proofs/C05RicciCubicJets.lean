import Yau.Proofs.C05RicciCubicJetsBudget

/-! An explicit dimensional cubic budget for the actual Ricci-cube scalar jets. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciCubicJetsAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarJetNorm_ricciCube_le (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (m : ℕ) (hm : m ≤ 2) (x : M.Carrier)
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ j ≤ 2, realRicciJetNorm k j x ≤ B) :
    scalarJetNorm k (ricciCube k) m x ≤ 64 * (2 * (n : ℝ) + 1)^3 * B^3 := by
  let d : ℝ := (2*n:ℕ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hsqrt : Real.sqrt d ≤ d + 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [sq_nonneg d]
  have hcoeff : 8 * d * Real.sqrt d ≤ 64 * (d+1)^3 := by
    have H := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 8*d)
    nlinarith [mul_nonneg hd (sq_nonneg d)]
  calc
    _ ≤ 8 * d * Real.sqrt d * B^3 := scalarJetNorm_ricciCube_le_sqrt k hk hK m hm x hB hR
    _ ≤ 64 * (d+1)^3 * B^3 := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hB _)
    _ = _ := by dsimp only [d]; push_cast; ring

end Yau.Proofs.C05RicciCubicJetsAux
