import Yau.LeafProofs.L17SchauderSpaceLocal
import Yau.LeafProofs.L17BootstrapHolderTaylorCalculus

/-! Ordinary spatial and time derivative bounds give the actual weighted graph norm. -/

noncomputable section
open Set Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17BootstrapHolderTaylorAux
open L17Aux L17HolderAux L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def mixedHolderBudget (P : UniformChartPartition g) (beta A Z U : ℝ) : ℝ :=
  max A ((3 : ℝ)^(1-beta)*(P.radius*Z+P.radius^2*U))

theorem mixedHolderBudget_nonneg (P : UniformChartPartition g) (beta : ℝ)
    {A Z U : ℝ} (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hU : 0 ≤ U) :
    0 ≤ mixedHolderBudget P beta A Z U := le_max_of_le_left hA

theorem parabolic_time_difference_le (P : UniformChartPartition g)
    {T : ℝ} (hT : T ≤ P.radius^2) (q r : ChartCylinder P T) :
    |(r.2 : ℝ)-q.2| ≤ P.radius*parabolicDistance q r := by
  have habs : |(q.2 : ℝ)-(r.2 : ℝ)| ≤ T := by
    apply abs_sub_le_iff.mpr
    constructor <;> linarith [q.2.property.1, q.2.property.2, r.2.property.1, r.2.property.2]
  have hs := Real.sqrt_le_sqrt (habs.trans hT)
  rw [Real.sqrt_sq P.radius_pos.le] at hs
  have he := Real.sq_sqrt (abs_nonneg ((q.2 : ℝ)-(r.2 : ℝ)))
  have hd : Real.sqrt |(q.2 : ℝ)-(r.2 : ℝ)| ≤ parabolicDistance q r :=
    le_add_of_nonneg_left (norm_nonneg _)
  rw [abs_sub_comm]
  nlinarith [mul_le_mul_of_nonneg_left hd P.radius_pos.le,
    mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg |(q.2 : ℝ)-(r.2 : ℝ)|)]

theorem parabolic_distance_le (P : UniformChartPartition g)
    {T : ℝ} (hT : T ≤ P.radius^2) (q r : ChartCylinder P T) :
    parabolicDistance q r ≤ 3*P.radius := by
  have hq : ‖(q.1 : ComplexVector n)‖ < P.radius := by
    simpa only [mem_ball, dist_zero_right] using q.1.property
  have hr : ‖(r.1 : ComplexVector n)‖ < P.radius := by
    simpa only [mem_ball, dist_zero_right] using r.1.property
  have habs : |(q.2 : ℝ)-(r.2 : ℝ)| ≤ T := by
    apply abs_sub_le_iff.mpr
    constructor <;> linarith [q.2.property.1, q.2.property.2, r.2.property.1, r.2.property.2]
  have hs := Real.sqrt_le_sqrt (habs.trans hT)
  rw [Real.sqrt_sq P.radius_pos.le] at hs
  unfold parabolicDistance
  linarith [norm_sub_le (q.1 : ComplexVector n) (r.1 : ComplexVector n)]

/-- This estimate includes pairs at different closed times. -/
theorem mixed_derivative_pair_bound (P : UniformChartPartition g)
    {T beta Z U : ℝ} (hT : T ≤ P.radius^2) (hb : beta ≤ 1)
    (hZ : 0 ≤ Z) (hU : 0 ≤ U)
    (f : P.centers → ComplexVector n → ℝ → F)
    (hzDiff : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      DifferentiableAt ℝ (fun w => f p w t) z)
    (htDiff : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      DifferentiableAt ℝ (fun s => f p z s) t)
    (hzBound : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      ‖fderiv ℝ (fun w => f p w t) z‖ ≤ Z)
    (htBound : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      ‖deriv (fun s => f p z s) t‖ ≤ U)
    (i : ChartPairs P T) :
    ‖pairWeight P T beta i •
      (f i.1 i.2.val.2.1 i.2.val.2.2-f i.1 i.2.val.1.1 i.2.val.1.2)‖ ≤
      (3 : ℝ)^(1-beta)*(P.radius*Z+P.radius^2*U) := by
  let q := i.2.val.1
  let r := i.2.val.2
  let d := parabolicDistance q r
  let L := P.radius*Z+P.radius^2*U
  have hL : 0 ≤ L := add_nonneg (mul_nonneg P.radius_pos.le hZ)
    (mul_nonneg (sq_nonneg _) hU)
  have hd : 0 < d := parabolicDistance_pos_of_ne i.2.property
  have hr : 0 < d/P.radius := div_pos hd P.radius_pos
  have hsp := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => hzDiff i.1 z hz r.2 r.2.property)
    (fun z hz => hzBound i.1 z hz r.2 r.2.property)
    (convex_ball (0 : ComplexVector n) P.radius) q.1.property r.1.property
  have htm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t ht => htDiff i.1 q.1 q.1.property t ht)
    (fun t ht => htBound i.1 q.1 q.1.property t ht)
    (convex_Icc (0 : ℝ) T) q.2.property r.2.property
  have hz : ‖(r.1 : ComplexVector n)-q.1‖ ≤ d := by
    rw [norm_sub_rev]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have ht := parabolic_time_difference_le P hT q r
  have hdiff : ‖f i.1 r.1 r.2-f i.1 q.1 q.2‖ ≤ L*(d/P.radius) := by
    calc
      _ ≤ ‖f i.1 r.1 r.2-f i.1 q.1 r.2‖+‖f i.1 q.1 r.2-f i.1 q.1 q.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ Z*‖(r.1 : ComplexVector n)-q.1‖+U*|(r.2 : ℝ)-q.2| := by
        simpa only [Real.norm_eq_abs] using add_le_add hsp htm
      _ ≤ Z*d+U*(P.radius*d) := add_le_add
        (mul_le_mul_of_nonneg_left hz hZ) (mul_le_mul_of_nonneg_left ht hU)
      _ = L*(d/P.radius) := by dsimp [L]; field_simp [P.radius_pos.ne']
  have heq : pairWeight P T beta i*(L*(d/P.radius)) = L*(d/P.radius)^(1-beta) := by
    change (P.radius^beta/d^beta)*(L*(d/P.radius)) = _
    rw [Real.rpow_sub hr, Real.rpow_one, Real.div_rpow hd.le P.radius_pos.le]
    have hdpow := (Real.rpow_pos_of_pos hd beta).ne'
    have hrpow := (Real.rpow_pos_of_pos P.radius_pos beta).ne'
    field_simp
  have hp := Real.rpow_le_rpow hr.le
    ((div_le_iff₀ P.radius_pos).mpr (parabolic_distance_le P hT q r))
    (sub_nonneg.mpr hb)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pairWeight_pos P T beta i)]
  exact (mul_le_mul_of_nonneg_left hdiff (pairWeight_pos P T beta i).le).trans
    (heq.le.trans ((mul_le_mul_of_nonneg_left hp hL).trans_eq (mul_comm _ _)))

theorem local_field_continuous (P : UniformChartPartition g) (T : ℝ)
    (f : P.centers → ComplexVector n → ℝ → F)
    (hf : ∀ p, ContinuousOn (fun b : ComplexVector n × ℝ => f p b.1 b.2)
      (ball 0 P.radius ×ˢ Icc (0:ℝ) T)) :
    Continuous (fun q : LocalCylinder P T => f q.1 q.2.1 q.2.2) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact (hf p).comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
    (fun q => ⟨q.1.property,q.2.property⟩)

/-- Construction in the original graph using only ordinary derivative bounds. -/
def localMixedElement (P : UniformChartPartition g)
    {T beta A Z U : ℝ} (hT : T ≤ P.radius^2) (hb : beta ≤ 1)
    (hZ : 0 ≤ Z) (hU : 0 ≤ U)
    (f : P.centers → ComplexVector n → ℝ → F)
    (hf : ∀ p, ContinuousOn (fun b : ComplexVector n × ℝ => f p b.1 b.2)
      (ball 0 P.radius ×ˢ Icc (0:ℝ) T))
    (hzDiff : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      DifferentiableAt ℝ (fun w => f p w t) z)
    (htDiff : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      DifferentiableAt ℝ (fun s => f p z s) t)
    (hValue : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T, ‖f p z t‖ ≤ A)
    (hzBound : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      ‖fderiv ℝ (fun w => f p w t) z‖ ≤ Z)
    (htBound : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      ‖deriv (fun s => f p z s) t‖ ≤ U) : LocalHolderSpace F P T beta :=
  localOfBounds F P T beta (fun q => f q.1 q.2.1 q.2.2)
    (local_field_continuous P T f hf) A
    ((3:ℝ)^(1-beta)*(P.radius*Z+P.radius^2*U))
    (fun q => hValue q.1 q.2.1 q.2.1.property q.2.2 q.2.2.property)
    (mixed_derivative_pair_bound P hT hb hZ hU f hzDiff htDiff hzBound htBound)

theorem localMixedElement_value (P : UniformChartPartition g)
    {T beta A Z U : ℝ} (hT : T ≤ P.radius^2) (hb : beta ≤ 1)
    (hZ : 0 ≤ Z) (hU : 0 ≤ U)
    (f : P.centers → ComplexVector n → ℝ → F)
    (hf : ∀ p, ContinuousOn (fun b : ComplexVector n × ℝ => f p b.1 b.2)
      (ball 0 P.radius ×ˢ Icc (0:ℝ) T))
    (hzDiff : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      DifferentiableAt ℝ (fun w => f p w t) z)
    (htDiff : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      DifferentiableAt ℝ (fun s => f p z s) t)
    (hValue : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T, ‖f p z t‖ ≤ A)
    (hzBound : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      ‖fderiv ℝ (fun w => f p w t) z‖ ≤ Z)
    (htBound : ∀ p z, z ∈ ball 0 P.radius → ∀ t ∈ Icc (0:ℝ) T,
      ‖deriv (fun s => f p z s) t‖ ≤ U) (q : LocalCylinder P T) :
    localFun F (localMixedElement P hT hb hZ hU f hf hzDiff htDiff hValue hzBound htBound) q =
      f q.1 q.2.1 q.2.2 := rfl

end Yau.LeafProofs.L17BootstrapHolderTaylorAux
