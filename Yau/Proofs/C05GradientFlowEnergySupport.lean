import Yau.Proofs.C05GradientFlowDini
import Yau.LeafProofs.L12BrokenEnergy
import Yau.LeafProofs.L12EndpointEnergy

/-! Actual broken-geodesic energy gives a right upper support for distance. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem distance_sq_le_twice_broken_energy (g : SmoothMetric M)
    (p₀ p₁ p₂ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    {s e d : ℝ} (hs : 0 < s) (he : 0 < e) (hd : 0 < d) (hT : s + e + d = 1)
    (hjoin₀ : (realGeodesicFlow g p₀ s).proj = p₁.proj)
    (hjoin₁ : (realGeodesicFlow g p₁ e).proj = p₂.proj) :
    inducedDistance g.form p₀.proj (realGeodesicFlow g p₂ d).proj ^ 2 ≤
      2 * (realSegmentEnergy g s p₀ + realSegmentEnergy g e p₁ + realSegmentEnergy g d p₂) := by
  have H := realBrokenGeodesicEnergy_lower_bound g p₀ p₁ p₂ hs he hd
    (g.induced_distance_nonneg _ _) hjoin₀ hjoin₁ (by rw [hT, one_mul])
  rw [hT] at H
  dsimp only [realSegmentEnergy]
  nlinarith only [H]

theorem upperRightSlopeLE_of_energy_support {u E : ℝ → ℝ} {t L e : ℝ}
    (hL : 0 < L) (hu : u t = L) (hE : E t = L ^ 2 / 2)
    (hbound : ∀ᶠ s in 𝓝[>] t, u s ^ 2 ≤ 2 * E s)
    (hder : HasDerivAt E e t) : UpperRightSlopeLE u t (e / L) := by
  have hEpos : 0 < 2 * E t := by rw [hE]; nlinarith only [hL, sq_pos_of_pos hL]
  have hsqrt : Real.sqrt (2 * E t) = L := by
    rw [hE]
    convert Real.sqrt_sq hL.le using 1 <;> ring
  have hsup : ∀ᶠ s in 𝓝[>] t, u s ≤ Real.sqrt (2 * E s) := by
    filter_upwards [hbound] with s hs
    have hpos : 0 ≤ 2 * E s := (sq_nonneg _).trans hs
    have H := Real.sq_sqrt hpos
    have hn := Real.sqrt_nonneg (2 * E s)
    nlinarith only [hs, H, hn, sq_nonneg (u s - Real.sqrt (2 * E s))]
  have H := (hder.const_mul 2).sqrt (ne_of_gt hEpos)
  have hder' : HasDerivAt (fun s => Real.sqrt (2 * E s)) (e / L) t := by
    convert H using 1
    rw [hsqrt]
    field_simp
  exact upperRightSlopeLE_of_upper_support (hu.trans hsqrt.symm) hsup hder'

end Yau.Proofs.C05GradientFlowAux
