import Yau.Proofs.F01CommonBackwardPatch
import Yau.Proofs.F01LocalHolderPatching

/-! Actual uniform backward-patch Holder estimates give a bound on
the full fixed inner cylinder. Neither the domain nor the numerical
constant is chosen after the realized function. -/
noncomputable section
open Set Metric
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]

theorem affineParabolicPoint_inverse_left {ρ : ℝ} (hρ : ρ ≠ 0)
    (c : Space n) (τ : ℝ) (p : Point n) :
    affineParabolicPoint ρ⁻¹ (-(ρ⁻¹ • c)) (-τ / ρ ^ 2)
      (affineParabolicPoint ρ c τ p) = p := by
  apply Prod.ext
  · simp only [affineParabolicPoint, smul_add, smul_smul, inv_mul_cancel₀ hρ, one_smul]
    abel
  · dsimp only [affineParabolicPoint]
    field_simp
    ring

theorem backward_holder_patching_budget {κ β C : ℝ}
    (hκ : 0 < κ) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (r l s : ℝ) (f : Point n → E),
      (∀ c ∈ ball 0 r, ∀ τ ∈ Icc l s,
        HolderBound β (backward 1) (fun p => f (affineParabolicPoint κ c τ p)) C) →
      HolderBound β (cylinder (ball 0 r) l s) f B := by
  let K := C * affineHolderScale κ⁻¹ β
  have hK : 0 ≤ K := mul_nonneg hC (affineHolderScale_nonneg _ _)
  obtain ⟨B, hB, hb⟩ := local_holder_patching_budget (n := n) (E := E) hκ hβ hC hK
  refine ⟨B, hB, ?_⟩
  intro r l s f hLocal
  apply hb (cylinder (ball 0 r) l s) f
  · intro p hp
    have h0 : ((0 : Space n), (0 : ℝ)) ∈ backward 1 := by
      constructor <;> norm_num [backward, mem_ball, dist_zero_right]
    have hh := (hLocal p.1 hp.1 p.2 hp.2).2.1 _ h0
    simpa only [affineParabolicPoint, smul_zero, zero_add, mul_zero, add_zero] using hh
  · intro p hp q hq hSpace hTime
    let τ := max p.2 q.2
    have hτ : τ ∈ Icc l s :=
      ⟨hp.2.1.trans (le_max_left _ _), max_le hp.2.2 hq.2.2⟩
    obtain ⟨p', q', hp', hq', hep, heq⟩ := close_pair_common_backward_patch hκ p q hSpace hTime
    let inv := affineParabolicPoint κ⁻¹ (-(κ⁻¹ • p.1)) (-τ / κ ^ 2)
    have hpi : inv p = p' := by
      rw [← hep]
      exact affineParabolicPoint_inverse_left hκ.ne' p.1 τ p'
    have hqi : inv q = q' := by
      rw [← heq]
      exact affineParabolicPoint_inverse_left hκ.ne' p.1 τ q'
    have hWeight : holderWeight β p' q' ≤ affineHolderScale κ⁻¹ β * holderWeight β p q := by
      rw [← hpi, ← hqi]
      exact holderWeight_affineParabolicPoint_general κ⁻¹ β (-(κ⁻¹ • p.1)) (-τ / κ ^ 2) p q
    have hh := (hLocal p.1 hp.1 τ hτ).2.2 p' hp' q' hq'
    change ‖f (affineParabolicPoint κ p.1 τ p') - f (affineParabolicPoint κ p.1 τ q')‖ ≤ _ at hh
    rw [hep, heq] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hWeight hC).trans_eq (by dsimp only [K]; ring))

end Yau.NodeProofs.F01Aux
