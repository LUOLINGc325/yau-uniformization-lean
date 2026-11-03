import Yau.Proofs.C04NormalEllipticModelCalculus
import Yau.Proofs.C04NormalModelJetsInverse
import Yau.Proofs.C04FrameComplexConnection

/-! The coframe formula gives the same-radius connection jets directly
from the coframe and connection-form jets. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalEllipticOmegaProduct :
    (E →L[ℝ] E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  ContinuousLinearMap.precompL E (ContinuousLinearMap.compL ℝ E E E)

def normalEllipticLeftCompose :
    (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  ContinuousLinearMap.precompR E (ContinuousLinearMap.compL ℝ E E E)

theorem normalEllipticOmegaProduct_norm : ‖normalEllipticOmegaProduct (E := E)‖ ≤ 1 :=
  (ContinuousLinearMap.norm_precompL_le E _).trans (ContinuousLinearMap.norm_compL_le ℝ E E E)

theorem normalEllipticLeftCompose_norm : ‖normalEllipticLeftCompose (E := E)‖ ≤ 1 :=
  (ContinuousLinearMap.norm_precompR_le E _).trans (ContinuousLinearMap.norm_compL_le ℝ E E E)

variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_normal_connection_jet_bounds (B : ℕ → ℝ) (hB : ∀ m, 0 < B m) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ R : ℝ, 0 < R → ∀ (A : E → E →L[ℝ] E)
        (conn : E → E →L[ℝ] E →L[ℝ] E),
        ContDiff ℝ ∞ A → ContDiff ℝ ∞ conn →
        (∀ x ∈ Metric.ball (0 : E) R,
          ‖A x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) →
        (∀ m x, x ∈ Metric.ball (0 : E) R →
          ‖iteratedFDeriv ℝ m A x‖ ≤ B m ∧ ‖iteratedFDeriv ℝ m conn x‖ ≤ B m) →
        ContDiffOn ℝ ∞ (coframeModelConnection A conn) (Metric.ball (0 : E) R) ∧
          ∀ m x, x ∈ Metric.ball (0 : E) R →
            ‖iteratedFDeriv ℝ m (coframeModelConnection A conn) x‖ ≤ C m := by
  obtain ⟨P, hPpos, hPb⟩ := exists_normal_inverse_jet_bounds (E := E) B hB
  let S : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * B i * B (m - i)
  have hS (m : ℕ) : 0 ≤ S m := Finset.sum_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i).le) (hB _).le
  let H : ℕ → ℝ := fun m => B (m + 1) + S m
  have hH (m : ℕ) : 0 ≤ H m := add_nonneg (hB _).le (hS m)
  let T : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * P i * H (m - i)
  have hT (m : ℕ) : 0 ≤ T m := Finset.sum_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hPpos i).le) (hH _)
  refine ⟨fun m => 1 + T m, fun m => by linarith [hT m], ?_⟩
  intro R hR A conn hA hconn hnear hjet
  obtain ⟨hinv, hInvBound⟩ := hPb R hR A hA hnear (fun m x hx => (hjet m x hx).1)
  let U := Metric.ball (0 : E) R
  let prod : E → E →L[ℝ] E →L[ℝ] E :=
    fun x => normalEllipticOmegaProduct (conn x) (A x)
  let raw : E → E →L[ℝ] E →L[ℝ] E := fun x => fderiv ℝ A x + prod x
  have hprod : ContDiff ℝ ∞ prod :=
    ((normalEllipticOmegaProduct (E := E)).contDiff.comp hconn).clm_apply hA
  have hDA : ContDiff ℝ ∞ (fderiv ℝ A) := hA.fderiv_right (by simp)
  have hraw : ContDiff ℝ ∞ raw := hDA.add hprod
  have hprodBound (m : ℕ) (x : E) (hx : x ∈ U) :
      ‖iteratedFDeriv ℝ m prod x‖ ≤ S m := by
    have hh := normal_elliptic_bilinear_jet (normalEllipticOmegaProduct (E := E))
      hconn.contDiffOn hA.contDiffOn Metric.isOpen_ball hx B B (fun j => (hB j).le)
      (fun j => (hjet j x hx).2) (fun j => (hjet j x hx).1) m
    exact hh.trans (mul_le_of_le_one_left (hS m) normalEllipticOmegaProduct_norm)
  have hrawBound (m : ℕ) (x : E) (hx : x ∈ U) :
      ‖iteratedFDeriv ℝ m raw x‖ ≤ H m := by
    have hd : ‖iteratedFDeriv ℝ m (fderiv ℝ A) x‖ ≤ B (m + 1) := by
      rw [norm_iteratedFDeriv_fderiv]
      exact (hjet (m + 1) x hx).1
    exact (normal_elliptic_add_jet hDA.contDiffOn hprod.contDiffOn Metric.isOpen_ball hx m).trans
      (add_le_add hd (hprodBound m x hx))
  have hGamma : (coframeModelConnection A conn) =
      fun x => normalEllipticLeftCompose (A x).inverse (raw x) := rfl
  rw [hGamma]
  refine ⟨((normalEllipticLeftCompose (E := E)).contDiff.comp_contDiffOn hinv).clm_apply
    hraw.contDiffOn, ?_⟩
  intro m x hx
  have hh := normal_elliptic_bilinear_jet (normalEllipticLeftCompose (E := E))
    hinv hraw.contDiffOn Metric.isOpen_ball hx P H (fun j => (hPpos j).le)
    (fun j => hInvBound j x hx) (fun j => hrawBound j x hx) m
  exact (hh.trans (mul_le_of_le_one_left (hT m) normalEllipticLeftCompose_norm)).trans
    (by linarith)

end Yau.Proofs.C04Aux
