import Yau.Proofs.F03CompactGreenError
import Yau.Proofs.F03ExhaustionCutoffConvergence

/-! The genuine compact Green generators converge uniformly under the actual first-gradient envelope. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Blueprint F02Aux LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exhaustionCutoff_green_generators_tendstoUniformlyOn
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) {C A : ℝ} (hC : 0 < C)
    (hlower : ∀ y,C⁻¹*(1+distFrom X.metric.form o y) ≤ u y)
    (hupper : ∀ y,u y ≤ C*(1+distFrom X.metric.form o y))
    (hCA : C ≤ A) (hA : 1 ≤ A)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (v : Pt X → ℝ) (hv : SmoothFn v) (S : Set ℝ)
    (k : ℝ → Pt X → ℝ) (hk : ∀ b ∈ S,SmoothFn (k b))
    (E : Pt X → ℝ) (hE : Integrable E μ) (hE0 : ∀ y,0 ≤ E y)
    (hEnvelope : ∀ b ∈ S,∀ y,|v y*k b y| ≤ E y ∧
      |v y| * Real.sqrt (gradNormSq X.metric.form (k b) y) ≤ E y ∧
      |k b y*laplacian X.metric.form v y| ≤ E y) :
    TendstoUniformlyOn
      (fun j : ℕ => fun b => ∫ y,k b y*laplacian X.metric.form
        (fun z => exhaustionCutoff u A ((j:ℝ)+1) z*v z) y ∂μ)
      (fun b => ∫ y,k b y*laplacian X.metric.form v y ∂μ) atTop S := by
  obtain ⟨K₀,hK₀,hLap⟩ := exhaustionCutoff_laplacian_bound X o u hu
  obtain ⟨K₁,hK₁,hGrad⟩ := exhaustionCutoff_gradient_bound X o u hu
  let K := K₀+2*K₁
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hIE : 0 ≤ ∫ y,E y ∂μ := integral_nonneg hE0
  have hBound (j : ℕ) (b : ℝ) (hb : b ∈ S) :
      |(∫ y,k b y*laplacian X.metric.form
          (fun z => exhaustionCutoff u A ((j:ℝ)+1) z*v z) y ∂μ)-
        (∫ y,k b y*laplacian X.metric.form v y ∂μ)| ≤
      (∫ y,(1-exhaustionCutoff u A ((j:ℝ)+1) y)*E y ∂μ)+
        K/((j:ℝ)+1)*(∫ y,E y ∂μ) := by
    let L : ℝ := (j:ℝ)+1
    have hL : 1 ≤ L := by dsimp [L];linarith [Nat.cast_nonneg (α := ℝ) j]
    have hL0 : 0 < L := zero_lt_one.trans_le hL
    have hR : 0 < (3*C*A+1)*L := by positivity
    have hGreen := integral_compact_green_error_le X.metric X.kahler_metric μ hμ hv (hk b hb)
      (exhaustionCutoff_smooth hu.1 A L) (exhaustionCutoff_compact X o u hu hA0 hL0) o hR
      (exhaustionCutoff_tsupport_ball X o u hu C hC hlower hA0 hL0)
      (exhaustionCutoff_range u A L) hE hE0 (hEnvelope b hb)
      (a := K₀/L^2) (b := K₁/L) (by positivity) (by positivity)
      (hLap A hA L hL) (hGrad A hA L hL)
    have hCoeff : K₀/L^2+2*(K₁/L) ≤ K/L := by
      have hLL : L ≤ L^2 := by nlinarith
      have hDiv : K₀/L^2 ≤ K₀/L := div_le_div_of_nonneg_left hK₀.le hL0 hLL
      calc
        _ ≤ K₀/L+2*(K₁/L) := add_le_add hDiv le_rfl
        _ = _ := by dsimp [K];ring
    exact hGreen.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hCoeff hIE))
  have hRest := exhaustionCutoff_integral_remainder_tendsto_zero X o u hu hC hupper hCA hA0 μ E hE
  have hScale : Tendsto (fun j : ℕ => K/((j:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [one_div,mul_zero,div_eq_mul_inv,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K
  have hError := hRest.add (hScale.mul_const (∫ y,E y ∂μ))
  simp only [zero_mul,add_zero] at hError
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hError.eventually (gt_mem_nhds hδ)] with j hj
  intro b hb
  rw [Real.dist_eq,abs_sub_comm]
  exact (hBound j b hb).trans_lt hj

end Yau.Proofs.F03Aux
