import Yau.Proofs.F03MovingBumpDerivatives

/-! Actual positive compact comparison functions with a finite decay rate. -/
noncomputable section
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def decayingMovingBump (ε C s₀ R : ℝ) (c : ℝ → E) (p : E × ℝ) : ℝ :=
  ε*Real.exp (-C*(p.2-s₀))*movingBallBump R c p

theorem movingBallBump_le_radius_power {R : ℝ} (hR : 0 ≤ R)
    (c : ℝ → E) (p : E × ℝ) : movingBallBump R c p ≤ R^6 := by
  have hq : max 0 (R^2-‖p.1-c p.2‖^2) ≤ R^2 :=
    max_le (sq_nonneg R) (sub_le_self _ (sq_nonneg _))
  change max 0 (R^2-‖p.1-c p.2‖^2)^3 ≤ _
  calc
    _ ≤ (R^2)^3 := pow_le_pow_left₀ (le_max_left _ _) hq 3
    _ = R^6 := by ring

theorem decayingMovingBump_contDiff (ε C s₀ R : ℝ) {c : ℝ → E} (hc : ContDiff ℝ 2 c) :
    ContDiff ℝ 2 (decayingMovingBump ε C s₀ R c) := by
  have hw : ContDiff ℝ 2 (fun p : E × ℝ => ε*Real.exp (-C*(p.2-s₀))) := by fun_prop
  exact hw.mul (movingBallBump_contDiff R hc)

theorem decayingMovingBump_pos {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (C s₀ : ℝ) (c : ℝ → E) (x : E) (t : ℝ) (hx : ‖x-c t‖ < R) :
    0 < decayingMovingBump ε C s₀ R c (x,t) :=
  mul_pos (mul_pos hε (Real.exp_pos _)) (movingBallBump_pos hR c x t hx)

theorem decayingMovingBump_zero_off {R : ℝ} (hR : 0 ≤ R)
    (ε C s₀ : ℝ) (c : ℝ → E) (x : E) (t : ℝ) (hx : R ≤ ‖x-c t‖) :
    decayingMovingBump ε C s₀ R c (x,t)=0 := by
  rw [decayingMovingBump,movingBallBump_eq_zero hR c x t hx,mul_zero]

theorem decayingMovingBump_time_hasDerivAt (ε C s₀ R : ℝ)
    {c : ℝ → E} {c' : E} (x : E) {t : ℝ} (hc : HasDerivAt c c' t) :
    HasDerivAt (fun s => decayingMovingBump ε C s₀ R c (x,s))
      (ε*Real.exp (-C*(t-s₀)) *
        (6*positivePower 2 (R^2-‖x-c t‖^2)*inner ℝ (x-c t) c' - C*movingBallBump R c (x,t))) t := by
  have hw := ((Real.hasDerivAt_exp (-C*(t-s₀))).comp t
    (((hasDerivAt_id t).sub_const s₀).const_mul (-C))).const_mul ε
  have hd := hw.mul (movingBallBump_time_hasDerivAt R x hc)
  convert hd using 1
  · rfl
  · simp only [Function.comp_def,id_eq]
    ring

end Yau.Proofs.F03Aux
