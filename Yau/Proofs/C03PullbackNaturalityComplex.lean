import Yau.Proofs.C03PullbackNaturalityLocal
import Yau.LeafProofs.L23DistanceEnergyCovariant

/-! Complex structure is preserved by the local source connection, as a
consequence of holomorphic coordinate derivatives and the connection chain. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

open Filter Yau Yau.LeafProofs.L23Aux
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem coordinate_hessian_I
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {f : ComplexVector n → ComplexVector n} (hf : ContDiffOn ℂ ∞ f O)
    {z : ComplexVector n} (hz : z ∈ O) (u v : ComplexVector n) :
    fderiv ℝ (fderiv ℝ f) z u (Complex.I • v) =
      Complex.I • fderiv ℝ (fderiv ℝ f) z u v := by
  have hfz : ContDiffAt ℝ 2 f z :=
    ((hf.contDiffAt (hO.mem_nhds hz)).restrict_scalars ℝ).of_le (by simp)
  have he : (fun p => fderiv ℝ f p (Complex.I • v)) =ᶠ[𝓝 z]
      (fun p => Complex.I • fderiv ℝ f p v) := by
    filter_upwards [hO.mem_nhds hz] with p hp
    exact coordinate_fderiv_I ((hf.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)) v
  have he' := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L u) he.fderiv_eq
  have hl := mapDirection_hasFDerivAt f hfz (Complex.I • v)
  have hr := (mapDirection_hasFDerivAt f hfz v).const_smul Complex.I
  change HasFDerivAt (fun p => fderiv ℝ f p (Complex.I • v))
    ((fderiv ℝ (fderiv ℝ f) z).flip (Complex.I • v)) z at hl
  change HasFDerivAt (fun p => Complex.I • fderiv ℝ f p v)
    (Complex.I • (fderiv ℝ (fderiv ℝ f) z).flip v) z at hr
  rw [hl.fderiv, hr.fderiv] at he'
  exact he'

theorem connection_I_right_of_chain
    (Γ₀ Γ₁ : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (J : ComplexVector n →L[ℝ] ComplexVector n)
    (H : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (hJinj : Function.Injective J)
    (hJI : ∀ v, J (Complex.I • v) = Complex.I • J v)
    (hHI : ∀ u v, H u (Complex.I • v) = Complex.I • H u v)
    (hΓI : ∀ u v, Γ₁ u (Complex.I • v) = Complex.I • Γ₁ u v)
    (hchain : ∀ u v, J (Γ₀ u v) = H u v + Γ₁ (J u) (J v))
    (u v : ComplexVector n) :
    Γ₀ u (Complex.I • v) = Complex.I • Γ₀ u v := by
  apply hJinj
  calc
    J (Γ₀ u (Complex.I • v)) = H u (Complex.I • v) +
        Γ₁ (J u) (J (Complex.I • v)) := hchain u (Complex.I • v)
    _ = Complex.I • (H u v + Γ₁ (J u) (J v)) := by
      rw [hHI, hJI, hΓI, smul_add]
    _ = Complex.I • J (Γ₀ u v) := congrArg (Complex.I • ·) (hchain u v).symm
    _ = J (Complex.I • Γ₀ u v) := (hJI (Γ₀ u v)).symm

theorem connection_I_I_of_I_right
    (Γ : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (hsymm : ∀ u v, Γ u v = Γ v u)
    (hI : ∀ u v, Γ u (Complex.I • v) = Complex.I • Γ u v)
    (u v : ComplexVector n) :
    Γ (Complex.I • u) (Complex.I • v) = -Γ u v := by
  rw [hI, hsymm (Complex.I • u) v, hI, hsymm v u, smul_smul, Complex.I_mul_I]
  simp only [neg_one_smul]

end Yau.Proofs.C03Aux.PullbackNaturality
