import Yau.Proofs.P06SmallTimeCylinderEnergy
import Yau.Proofs.P06SmallTimeCylinderScaling
import Yau.Proofs.P06CylinderRegularityHeatBounds

/-! One quantitative spatial-prolongation step on every time dilation of
fixed buffers.  The actual profiles and coefficient bounds precede τ and U. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.SmallTimeCylinder
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux CylinderReg
variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

theorem exists_small_time_one_step_energy_constant
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {Q K : Set (Point n)} (hQ : IsOpen Q) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (lam upper A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hEll : ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      Elliptic (timeScale τ hτ.ne' '' Q) (heatPrincipal q) lam upper)
    (ha : ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ p ∈ timeScale τ hτ.ne' '' Q, ∀ i j, |heatPrincipal q p i j| ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : ℝ) (hτ : 0 < τ), τ ≤ 1 →
      ∀ U : Point n → α → ℝ,
      (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
      heatEquation q e1 e0 (timeScale τ hτ.ne' '' Q) U →
      IntegrableOn (valueSquare U) (timeScale τ hτ.ne' '' Q) →
      (∫ p in timeScale τ hτ.ne' '' K,
        valueSquare (regularityProlongValue (fun i => (Yau.realVec i,0)) U) p) ≤
        (C / τ ^ 2) * ∫ p in timeScale τ hτ.ne' '' Q, valueSquare U p := by
  obtain ⟨η, hη, hηB, hηNear⟩ := exists_bounded_test_eq_one_near_compact hQ hK hKQ
  obtain ⟨ζ, hζ, hζB, hζNear⟩ :=
    exists_bounded_test_eq_one_near_compact hQ hη.2.1 hη.2.2
  obtain ⟨M, hM, hDeriv⟩ := exists_rescaleProfile_firstDerivative_bound hη.1 hη.2.1
  obtain ⟨D, B, hD, hB, hd, he⟩ :=
    exists_heatCoefficient_bounds q e1 e0 hq hcq he1 hce1 he0 hce0
  have hCoeff := heatCoefficients_regular q e1 e0 hq hcq he1 hce1 he0 hce0
  obtain ⟨C, hC, hEst⟩ := exists_small_time_local_gradient_constant n α
    lam upper A D B M hlam hA hD hB hM
  refine ⟨1 + C, by positivity, ?_⟩
  intro τ hτ hτ1 U hU hPDE hUI
  let T := timeScale (n := n) τ hτ.ne'
  let ητ := rescaleProfile τ hτ.ne' η
  let ζτ := rescaleProfile τ hτ.ne' ζ
  have hQτ : IsOpen (T '' Q) := T.toHomeomorph.isOpenMap _ hQ
  have hKτ : IsCompact (T '' K) := hK.image T.continuous
  have hητ : Test (T '' Q) ητ := rescaleProfile_test τ hτ.ne' hη
  have hζτ : Test (T '' Q) ζτ := rescaleProfile_test τ hτ.ne' hζ
  have hNear : ∀ p ∈ tsupport ητ, ζτ =ᶠ[𝓝 p] (fun _ => 1) := by
    intro p hp
    rw [rescaleProfile_tsupport] at hp
    rcases hp with ⟨p, hp, rfl⟩
    exact rescaleProfile_germ τ hτ.ne' (hζNear p hp)
  have hOne : ∀ p ∈ T '' K, ητ p = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact (rescaleProfile_germ τ hτ.ne' (hηNear p hp)).eq_of_nhds
  have hFluxPDE : ∀ p ∈ T '' Q, ∀ r, fderiv ℝ (fun s => U s r) p (0,1) =
      (∑ i, fderiv ℝ (fun s => systemFlux (heatPrincipal q) (heatFluxCoeff q e1) U r s i)
        p (Yau.realVec i,0)) + valueSource (heatSourceCoeff q e1 e0) U r p := by
    intro p hp r
    rw [heat_valueFlux_identity q e1 e0 U hq he1 hU p r]
    exact hPDE p hp r
  have hGrad := hEst τ hτ hτ1 (T '' Q) (T '' K) (heatPrincipal q)
    (heatFluxCoeff q e1) (heatSourceCoeff q e1 e0) ητ ζτ U hQτ hKτ.measurableSet
    (hEll τ hτ hτ1) (ha τ hτ hτ1) (fun i j => (hq i j).div_const 2)
    (fun r c i => (hCoeff.1 r c i).1) (fun r c => (hCoeff.2 r c).1) hd he
    hητ hζτ (rescaleProfile_bound τ hτ.ne' hηB) (rescaleProfile_bound τ hτ.ne' hζB)
    hNear hOne (hDeriv τ hτ hτ1).1 (hDeriv τ hτ hτ1).2
    (fun r => (hU r).contDiffOn) hUI hFluxPDE
  have hSub : T '' K ⊆ T '' Q := Set.image_mono hKQ
  have hVal := integral_valueSquare_mono hSub hUI
  have hGI : IntegrableOn (gradientSquare U) (T '' K) := by
    have hG : ContDiff ℝ ∞ (gradientSquare U) :=
      ContDiff.sum fun r _ => ContDiff.sum fun i _ => (gradient_contDiff (hU r) i).pow 2
    exact hG.continuous.continuousOn.integrableOn_compact hKτ
  have hVI := hUI.mono_set hSub
  have hNonneg : 0 ≤ ∫ p in T '' Q, valueSquare U p :=
    integral_nonneg (fun p => valueSquare_nonneg U p)
  have hInv : 1 ≤ 1 / τ ^ 2 := (one_le_div (sq_pos_of_pos hτ)).mpr (by nlinarith)
  have hVal' : (∫ p in T '' K, valueSquare U p) ≤
      (1 / τ ^ 2) * ∫ p in T '' Q, valueSquare U p :=
    hVal.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hInv hNonneg)
  simp_rw [prolong_valueSquare]
  rw [integral_add hVI hGI]
  have hTotal := add_le_add hVal' hGrad
  convert hTotal using 1 <;> ring

end Yau.NodeProofs.P06Aux.SmallTimeCylinder
