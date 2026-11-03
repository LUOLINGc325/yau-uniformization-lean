import Yau.Proofs.F05BootstrapZeroTraceSmooth
import Yau.Proofs.F05BootstrapValueGoodWords

/-! Actual positive-time joint smoothness for the original value-bounded
nonlinear equation with its smooth physical datum. Both the boundary and
terminal faces are included; no smooth candidate coefficient is assumed. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ}

theorem F05_flat_nonlinear_positive_cap_smooth {ν : Option (RIdx n)} {T α lam upper K r τ : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K)
    (hr : 0 < r) (hr2 : r < 2) (hτ : 0 < τ) (hτT : τ ≤ T)
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (R p u : Point n → ℝ)
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun z => B z i) (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hp : ContDiffOn ℝ ∞ p (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hu : F05LocalSchauder α ν T u) (hFace : F05ZeroFace ν T (fun z => u z-p z))
    (hEll : Elliptic (F05PosPatch ν T) A lam upper)
    (hBound : ∀ z ∈ F05PosPatch ν T, |u z| ≤ K)
    (hPDE : ∀ z ∈ F05PosPatch ν T,
      F05RelT (Ioc 0 T) u z = Real.exp (-u z)*
        ((∑ i,∑ l,A z i l*F05RelDD (F05PosSpace ν) u z (realVec i) (realVec l))+
          ∑ i,B z i*F05RelD (F05PosSpace ν) u z (realVec i))+(1-Real.exp (-u z))*R z) :
    ContDiffOn ℝ ∞ u (region ν r ×ˢ Icc τ T) := by
  let v : Point n → ℝ := fun z => u z-p z
  let S := τ/2
  have hS : 0 < S := by dsimp only [S]; positivity
  have hST : S < T := by dsimp only [S]; linarith
  have hSτ : S ≤ τ := by dsimp only [S]; linarith
  have hV := F05_local_schauder_sub hu (F05_smooth_background_local_schauder hα hα1 hp)
  have hCoefficients := F05_datum_coefficients_smooth A B R p hA hB hR hp
  have hExpEll := F05_exp_principal_elliptic hEll hK hBound
  have hEllV : Elliptic (F05PosPatch ν T)
      (fun z => Real.exp (-v z) • F05DatumPrincipal p A z)
      (lam/Real.exp K) (upper/Real.exp (-K)) := by
    change Elliptic (F05PosPatch ν T)
      (fun z => Real.exp (-(u z-p z)) • F05DatumPrincipal p A z) _ _
    rw [F05_datum_principal_identity]
    exact hExpEll
  have hEquation : ∀ z ∈ F05PosPatch ν T,
      F05RelOp (F05PosSpace ν) (Ioc 0 T) (fun z => Real.exp (-u z) • A z)
        (fun z i => Real.exp (-u z)*B z i) u z = (1-Real.exp (-u z))*R z := by
    intro z hz
    rw [F05_relative_exponential_operator,hPDE z hz]
    ring
  have hVEq := F05_subtract_datum_equation A B R p u hp (F05_local_schauder_to_relative hu) hEquation
  have hVSmooth := F05_zero_trace_cap_smooth hT hα hα1 hr hr2 hS hST
    (F05DatumPrincipal p A) (F05DatumDrift p B) (F05DatumSource p A B R) (F05DatumFree T p R) v
    hCoefficients.1 hCoefficients.2.1 hCoefficients.2.2.1 hCoefficients.2.2.2 hV hFace hEllV hVEq
  have hQ : region ν r ×ˢ Icc S T ⊆ Metric.ball 0 3 ×ˢ Ioc 0 T :=
    (F05_receiving_subset_posPatch ν hr2 hS).trans (F05_pos_patch_subset_background ν T)
  have hUSmooth : ContDiffOn ℝ ∞ u (region ν r ×ˢ Icc S T) := by
    apply (hVSmooth.add (hp.mono hQ)).congr
    intro z hz
    dsimp only [v]
    ring
  exact hUSmooth.mono (fun z hz => ⟨hz.1,hSτ.trans hz.2.1,hz.2.2⟩)

end Yau.Proofs.F05Aux
