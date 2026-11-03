import Yau.Proofs.F05TimeMultiplication
import Yau.Proofs.F05BootstrapSchauderLimit

/-! A fixed smooth time cutoff preserves a uniform bound for all four
actual jets and creates the genuine homogeneous initial value/time jet
required by the already proved zero-FTC Banach graph. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_time_cutoff_full_holder {X : Set (Space n)} {T α E C : ℝ}
    (hT : 0 < T) {u : Point n → ℝ} (hu : C2 (cylinder X 0 T) u)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ)
    (hθ0 : HolderBound α (cylinder X 0 T) (fun p => θ p.2) E)
    (hθ1 : HolderBound α (cylinder X 0 T) (fun p => deriv θ p.2) E)
    (hLow : HolderBound α (cylinder X 0 T) (fun p => (u p,spatialD u p)) C)
    (hHess : HolderBound α (cylinder X 0 T) (spatialDD u) C)
    (hTime : HolderBound α (cylinder X 0 T) (timeD (cylinder X 0 T) u) C) :
    C2 (cylinder X 0 T) (fun p => θ p.2*u p) ∧
      HolderBound α (cylinder X 0 T)
        (fun p => (((θ p.2*u p),spatialD (fun z => θ z.2*u z) p),
          (spatialDD (fun z => θ z.2*u z) p,timeD (cylinder X 0 T) (fun z => θ z.2*u z) p)))
        (4*E*C) := by
  have hE := hθ0.1
  have hC := hLow.1
  have hBudget : 2*E*C ≤ 4*E*C := by nlinarith [mul_nonneg hE hC]
  have hLowMul : HolderBound α (cylinder X 0 T)
      (fun p => θ p.2 • (u p,spatialD u p)) (2*E*C) := by
    convert! holderBound_smul_refined hθ0 hLow hE hC
      (fun p hp => by simpa only [Real.norm_eq_abs] using hθ0.2.1 p hp) hLow.2.1 using 1 <;> ring
  have hHessMul : HolderBound α (cylinder X 0 T)
      (fun p => θ p.2 • spatialDD u p) (2*E*C) := by
    convert! holderBound_smul_refined hθ0 hHess hE hC
      (fun p hp => by simpa only [Real.norm_eq_abs] using hθ0.2.1 p hp) hHess.2.1 using 1 <;> ring
  have hLowActual : HolderBound α (cylinder X 0 T)
      (fun p => (θ p.2*u p,spatialD (fun z => θ z.2*u z) p)) (4*E*C) := by
    apply holderBound_congr_on (holderBound_mono_const hLowMul hBudget)
    intro p hp
    apply Prod.ext
    · rfl
    · exact (spatialD_time_mul hu θ hp).symm
  have hHessActual : HolderBound α (cylinder X 0 T)
      (spatialDD (fun z => θ z.2*u z)) (4*E*C) :=
    holderBound_congr_on (holderBound_mono_const hHessMul hBudget)
      (fun p hp => (spatialDD_time_mul hu θ hp).symm)
  have hTimeRaw := holderBound_add (holderBound_mul hθ1 (holderBound_fst hLow))
    (holderBound_mul hθ0 hTime)
  have hTimeActual : HolderBound α (cylinder X 0 T)
      (timeD (cylinder X 0 T) (fun z => θ z.2*u z)) (4*E*C) := by
    have hh := holderBound_congr_on hTimeRaw (fun p hp =>
      (F05_timeD_time_mul hT hu (hθ.differentiable (by norm_num)) hp).symm)
    convert! hh using 1 <;> ring
  exact ⟨F05_c2_time_mul hT hu hθ,
    F05_holderBound_prod_same hLowActual (F05_holderBound_prod_same hHessActual hTimeActual)⟩

theorem F05_time_cutoff_zero_initial {X : Set (Space n)} {T : ℝ} (hT : 0 < T)
    {u : Point n → ℝ} (hu : C2 (cylinder X 0 T) u)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (hθ0 : θ 0 = 0) (hθ1 : deriv θ 0 = 0) :
    ∀ x ∈ X, θ 0*u (x,0) = 0 ∧
      timeD (cylinder X 0 T) (fun p => θ p.2*u p) (x,0) = 0 := by
  intro x hx
  refine ⟨by rw [hθ0,zero_mul],?_⟩
  rw [F05_timeD_time_mul hT hu (hθ.differentiable (by norm_num)) ⟨hx,le_rfl,hT.le⟩,
    hθ0,hθ1,zero_mul,zero_mul,zero_add]

end Yau.Proofs.F05Aux
