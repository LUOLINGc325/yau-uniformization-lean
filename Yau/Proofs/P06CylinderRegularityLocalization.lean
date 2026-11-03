import Yau.Proofs.P06CylinderRegularityEnergy

/-! Localizing the actual coupled equation preserves it on the inner test
plateau. Only compact value energy remains on the right of Caccioppoli. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

variable {n : ℕ} {α : Type*} [Fintype α]

theorem systemFlux_germ {a : Point n → Mat n}
    {d : α → α → Yau.RIdx n → Point n → ℝ} {U V : Point n → α → ℝ}
    {p : Point n} (h : U =ᶠ[𝓝 p] V) (r : α) (i : Yau.RIdx n) :
    (fun q => systemFlux a d U r q i) =ᶠ[𝓝 p]
      (fun q => systemFlux a d V r q i) := by
  have hc (c : α) : (fun q => U q c) =ᶠ[𝓝 p] (fun q => V q c) :=
    h.mono fun q hq => congrFun hq c
  have hD : (fun q => fderiv ℝ (fun s => U s r) q) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ (fun s => V s r) q) := (hc r).fderiv
  filter_upwards [h, hD] with q hq hDq
  simp only [systemFlux, energyFlux, spatialGradient, valueFlux, hDq, hq]

theorem cutoff_system_equation {Q : Set (Point n)}
    {a : Point n → Mat n} {d : α → α → Yau.RIdx n → Point n → ℝ}
    {e : α → α → Point n → ℝ} {U : Point n → α → ℝ} {η ζ : Point n → ℝ}
    (hηQ : tsupport η ⊆ Q)
    (hζone : ∀ p ∈ tsupport η, ζ =ᶠ[𝓝 p] (fun _ => 1))
    (hPDE : ∀ p ∈ Q, ∀ r, fderiv ℝ (fun q => U q r) p (0,1) =
      (∑ i, fderiv ℝ (fun q => systemFlux a d U r q i) p (Yau.realVec i,0)) +
        valueSource e U r p) :
    ∀ p ∈ tsupport η, ∀ r,
      fderiv ℝ (fun q => ζ q * U q r) p (0,1) =
      (∑ i, fderiv ℝ (fun q => systemFlux a d (fun s c => ζ s * U s c) r q i)
        p (Yau.realVec i,0)) + valueSource e (fun s c => ζ s * U s c) r p := by
  intro p hp r
  have hUg : (fun q c => ζ q * U q c) =ᶠ[𝓝 p] U := by
    filter_upwards [hζone p hp] with q hq
    funext c
    simp only [hq, one_mul]
  have hcomp : (fun q => ζ q * U q r) =ᶠ[𝓝 p] (fun q => U q r) :=
    hUg.mono fun q hq => congrFun hq r
  have hFlux (i : Yau.RIdx n) :
      fderiv ℝ (fun q => systemFlux a d (fun s c => ζ s * U s c) r q i) p =
      fderiv ℝ (fun q => systemFlux a d U r q i) p := (systemFlux_germ hUg r i).fderiv.eq_of_nhds
  have hDeriv : fderiv ℝ (fun q => ζ q * U q r) p = fderiv ℝ (fun q => U q r) p :=
    hcomp.fderiv.eq_of_nhds
  rw [hDeriv]
  simp_rw [hFlux]
  have hValue : valueSource e (fun s c => ζ s * U s c) r p = valueSource e U r p := by
    have hz : ζ p = 1 := (hζone p hp).eq_of_nhds
    simp only [valueSource, hz, one_mul]
  rw [hValue]
  exact hPDE p (hηQ hp) r

/-- The localized square value energy is controlled by the original local
square energy, with no derivatives or global norms on the right. -/
theorem cutoff_valueSquare_bound {Q : Set (Point n)} (hQ : MeasurableSet Q)
    {ζ : Point n → ℝ} {U : Point n → α → ℝ}
    (hζQ : tsupport ζ ⊆ Q) (hζB : ∀ p, |ζ p| ≤ 1)
    (hInt : IntegrableOn (valueSquare U) Q)
    (hCutInt : Integrable (valueSquare (fun p c => ζ p * U p c)) volume) :
    (∫ p, valueSquare (fun p c => ζ p * U p c) p) ≤ ∫ p in Q, valueSquare U p := by
  have hI : Integrable (Q.indicator (valueSquare U)) volume :=
    (integrable_indicator_iff hQ).mpr hInt
  rw [← integral_indicator hQ]
  apply integral_mono hCutInt hI
  intro p
  by_cases hp : p ∈ Q
  · rw [Set.indicator_of_mem hp]
    unfold valueSquare
    apply Finset.sum_le_sum
    intro c _
    have hζ := hζB p
    have hsq : (ζ p)^2 ≤ 1 := by nlinarith [sq_abs (ζ p), abs_nonneg (ζ p)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg (U p c))]
  · rw [Set.indicator_of_notMem hp]
    have hz : ζ p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hζQ h))
    simp only [valueSquare, hz, zero_mul, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    exact le_rfl

end Yau.NodeProofs.P06Aux.CylinderReg
