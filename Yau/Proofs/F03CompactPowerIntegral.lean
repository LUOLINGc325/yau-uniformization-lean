import Yau.Proofs.F03EllipticChartIntegrability

/-! A genuine uniform power bound controls the actual finite sum of L² power integrals. -/
noncomputable section
open MeasureTheory Filter Set
namespace Yau.Proofs.F03Aux

theorem finite_power_integral_sq_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Set X) (hS : MeasurableSet S) (hFin : μ S ≠ ⊤)
    (N : ℕ) (F : ℕ → X → ℂ)
    (hI : ∀ p ≤ N,IntegrableOn (fun x => ‖F p x‖^2) S μ)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ p ≤ N,∀ x ∈ S,‖F p x‖ ≤ B) :
    (∑ p ∈ Finset.range (N+1),∫ x in S,‖F p x‖^2 ∂μ) ≤
      (N+1 : ℝ)*μ.real S*B^2 := by
  have hConst : IntegrableOn (fun _ : X => B^2) S μ := integrableOn_const hFin
  have hEach (p : ℕ) (hp : p ≤ N) : (∫ x in S,‖F p x‖^2 ∂μ) ≤ μ.real S*B^2 := by
    calc
      _ ≤ ∫ _ in S,B^2 ∂μ := by
        apply integral_mono_ae (hI p hp) hConst
        filter_upwards [ae_restrict_mem hS] with x hx
        exact pow_le_pow_left₀ (norm_nonneg _) (hBound p hp x hx) 2
      _ = μ.real S*B^2 := by rw [setIntegral_const,smul_eq_mul]
  calc
    _ ≤ ∑ _p ∈ Finset.range (N+1),μ.real S*B^2 :=
      Finset.sum_le_sum (fun p hp => hEach p (by have := Finset.mem_range.mp hp;omega))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one];ring

end Yau.Proofs.F03Aux
