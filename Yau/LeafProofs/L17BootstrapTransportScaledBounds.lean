import Yau.LeafProofs.L17BootstrapTransportInterpolation
import Yau.LeafProofs.L17BootstrapTransportCollarBounds

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17LocalizedSchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T beta : ℝ}

theorem scaled_zero_collar_holder_bounds {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (p : P.centers) (R : LocalHolderSpace F P T beta) (hR : ‖R‖ ≤ A)
    (f : ComplexVector n × Time T → F)
    (hZero : ∀ q : ComplexVector n × Time T, q.1 ∉ ball (0 : ComplexVector n) (P.radius/4) → f q=0)
    (hRep : ∀ q : ComplexVector n × Time T, ∀ hq : q.1 ∈ ball (0 : ComplexVector n) P.radius,
      f q=s • localFun F R ⟨p,(⟨q.1,hq⟩,q.2)⟩) :
    (∀ q : ComplexVector n × Time T, ‖f q‖ ≤ s*(2*A)) ∧
      ∀ q r : ComplexVector n × Time T, ‖f q-f r‖ ≤ s*(2*A)*(localScaledDistance P.radius q r)^beta := by
  have hSup : ∀ q : ComplexVector n × Time T, q.1 ∈ ball (0 : ComplexVector n) P.radius → ‖f q‖ ≤ s*A := by
    intro q hq
    rw [hRep q hq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left ((localValue_norm_le F R _).trans hR) hs
  have hPair : ∀ q r : ComplexVector n × Time T, q.1 ∈ ball (0 : ComplexVector n) P.radius →
      r.1 ∈ ball (0 : ComplexVector n) P.radius →
      ‖f q-f r‖ ≤ (s*A)*(localScaledDistance P.radius q r)^beta := by
    intro q r hq hr
    rw [hRep q hq,hRep r hr,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    have h := local_difference_bound R p (⟨q.1,hq⟩,q.2) (⟨r.1,hr⟩,r.2)
    rw [norm_sub_rev] at h
    change ‖localFun F R ⟨p,(⟨q.1,hq⟩,q.2)⟩-localFun F R ⟨p,(⟨r.1,hr⟩,r.2)⟩‖ ≤
      ‖R‖*(localScaledDistance P.radius q r)^beta at h
    have hPow : 0 ≤ (localScaledDistance P.radius q r)^beta := Real.rpow_nonneg
      (div_nonneg (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) P.radius_pos.le) _
    calc
      _ ≤ s*(A*(localScaledDistance P.radius q r)^beta) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hR hPow)) hs
      _ = _ := by ring
  constructor
  · intro q
    exact (zero_collar_sup_bound P.radius_pos (mul_nonneg hs hA) f hZero hSup q).trans
      (mul_le_mul_of_nonneg_left (by linarith : A ≤ 2*A) hs)
  · intro q r
    exact (zero_collar_difference_bound P.radius_pos (mul_nonneg hs hA) hbeta0 hbeta1 f hZero hSup hPair q r).trans_eq
      (by ring)

end Yau.LeafProofs.L17BootstrapTransportAux
