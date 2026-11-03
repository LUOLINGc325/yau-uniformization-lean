import Yau.Proofs.F03CoarseKernelBound

/-! The same kernel has a genuine Gaussian bound for its right spatial gradient. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings LeafProofs.L24Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernelCandidate_right_gradient_single_center
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (b : ℝ),0 < b → ∀ x y,
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z) y) ≤
        C/Real.sqrt b*Real.exp (-c*distFrom X.metric.form x y^2/b)/
          (μ (distBall X.metric.form x (Real.sqrt b))).toReal := by
  obtain ⟨_K,_d,C,c,_hK,_hd,hC,hc,hBound⟩ :=
    dirichletMinimalKernelCandidate_gaussian_gradient X o h U P ρ hf
  refine ⟨C*Real.exp ((n:ℝ)^2/(2*c)),c/2,by positivity,by positivity,?_⟩
  intro μ hμ O hO b hb x y
  let a := Real.sqrt (gradNormSq X.metric.form (fun z =>
    dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z) y)
  have hs : (fun z => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z)=
      (fun z => dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b z x) :=
    funext (fun z => dirichletMinimalKernelCandidate_symm X.metric X.kahler_metric μ hμ O hO hb x z)
  have hInput : Real.sqrt b*a ≤ C*Real.exp (-c*distFrom X.metric.form x y^2/(Real.sqrt b)^2)/
      Real.sqrt ((μ (distBall X.metric.form x (Real.sqrt b))).toReal*
        (μ (distBall X.metric.form y (Real.sqrt b))).toReal) := by
    have hh := mul_le_mul_of_nonneg_left (hBound μ hμ O hO b hb y x).2 (Real.sqrt_nonneg b)
    rw [Real.sq_sqrt hb.le]
    dsimp [a]
    rw [hs]
    convert hh using 1
    rw [show distFrom X.metric.form y x=distFrom X.metric.form x y from
      X.metric.induced_distance_symm y x,mul_comm
        (μ (distBall X.metric.form y (Real.sqrt b))).toReal]
    field_simp
  have hSingle := symmetric_gaussian_to_single_center X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ x y (Real.sqrt_pos.mpr hb) hC.le hc hInput
  rw [Real.sq_sqrt hb.le] at hSingle
  have hDiv : a ≤ (C*Real.exp ((n:ℝ)^2/(2*c))*
      Real.exp (-(c/2)*distFrom X.metric.form x y^2/b)/
      (μ (distBall X.metric.form x (Real.sqrt b))).toReal)/Real.sqrt b :=
    (le_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr
      (by
        calc
          a*Real.sqrt b=Real.sqrt b*a := mul_comm _ _
          _ ≤ _ := hSingle)
  convert hDiv using 1 <;> ring

theorem dirichletMinimalKernelCandidate_right_gradient_coarse_gaussian
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) (L : ℝ),1 ≤ L →
      ∀ b : ℝ,0 < b → b ≤ L^2 → ∀ x,inducedDistance X.metric.form o x ≤ C₀*L → ∀ y,
      Real.sqrt (gradNormSq X.metric.form (fun z =>
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x z) y) ≤
        C/Real.sqrt b*(L/Real.sqrt b)^(2*n)*
          Real.exp (-c*(inducedDistance X.metric.form o y/((C₀+1)*L))^2)/
          (μ (distBall X.metric.form o ((C₀+1)*L))).toReal := by
  obtain ⟨K,c,hK,hc,hBound⟩ := dirichletMinimalKernelCandidate_right_gradient_single_center X o h U P ρ hf
  let D := C₀+1
  have hD : 1 ≤ D := by dsimp [D];linarith
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let C := K*Real.exp c*(2*D)^(2*n)
  refine ⟨C,c/2,by dsimp [C];positivity,by positivity,?_⟩
  intro μ hμ O hO L hL b hb hbL x hx y
  let R := D*L
  let r := Real.sqrt b
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hR : 0 < R := mul_pos hD0 hL0
  have hr : 0 < r := Real.sqrt_pos.mpr hb
  have hrL : r ≤ L := Real.sqrt_le_iff.mpr ⟨hL0.le,hbL⟩
  have hLR : L ≤ R := by dsimp [R];nlinarith
  have hNear : inducedDistance X.metric.form o x ≤ R := by dsimp [R,D];nlinarith
  have hbR : b ≤ R^2 := hbL.trans (pow_le_pow_left₀ hL0.le hLR 2)
  have hInv := ball_inverse_volume_center_transfer X.metric X.complete_metric X.kahler_metric
    (F02Aux.initialRicci_posSemidef X o h U P ρ hf) μ hμ o x hr (hrL.trans hLR) hNear
  have hExponent := nearby_gaussian_exponent (c := c)
    (d := inducedDistance X.metric.form x y) (D := inducedDistance X.metric.form o y)
    (t := R^2) (s := b) (r := R) hc.le (sq_pos_of_pos hR) hb hbR hR.le rfl
    (X.metric.induced_distance_nonneg x y) (X.metric.induced_distance_nonneg o y)
    (by linarith [X.metric.induced_distance_triangle o x y])
  have hExp : Real.exp (-c*inducedDistance X.metric.form x y^2/b) ≤
      Real.exp c*Real.exp (-(c/2)*(inducedDistance X.metric.form o y/R)^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    convert hExponent using 1 <;> rw [div_pow] <;> ring
  calc
    _ ≤ (K/r)*Real.exp (-c*inducedDistance X.metric.form x y^2/b)*
        (1/(μ (distBall X.metric.form x r)).toReal) := by
      simpa only [distFrom,lengthDist,div_eq_mul_inv,one_mul,r] using hBound μ hμ O hO b hb x y
    _ ≤ (K/r)*(Real.exp c*Real.exp (-(c/2)*(inducedDistance X.metric.form o y/R)^2))*
        (((2*R)/r)^(2*n)/(μ (distBall X.metric.form o R)).toReal) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hExp (by positivity)) hInv (by positivity) (by positivity)
    _ = _ := by
      have hRatio : (2*R)/r=(2*D)*(L/r) := by dsimp [R];ring
      rw [hRatio,mul_pow]
      dsimp [C,R,D,r]
      ring

end Yau.Proofs.F03Aux
