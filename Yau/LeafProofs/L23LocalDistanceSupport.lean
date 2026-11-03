import Yau.LeafProofs.L23FieldMetricConnection
import Yau.LeafProofs.L23RicciBound

/-! Local scalar metric comparison and distance-cutoff infrastructure. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The integrating-factor argument uses only interior derivatives and endpoint
continuity, so it applies to the original closed time slab. -/
theorem exponential_comparison_on_Icc {f f' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt f (f' s) s)
    (hbound : ∀ s ∈ Set.Ioo a b, -(c * f s) ≤ f' s ∧ f' s ≤ c * f s)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    Real.exp (-c * (t-a)) * f a ≤ f t ∧
      f t ≤ Real.exp (c * (t-a)) * f a := by
  have hplus (s : ℝ) (hs : s ∈ Set.Ioo a b) :
      HasDerivAt (fun u => Real.exp (c * (u-a)) * f u)
        (Real.exp (c * (s-a)) * (c * f s + f' s)) s := by
    convert! (((hasDerivAt_id s).sub_const a).const_mul c).exp.mul (hd s hs) using 1 <;> dsimp <;> ring
  have hminus (s : ℝ) (hs : s ∈ Set.Ioo a b) :
      HasDerivAt (fun u => Real.exp (-c * (u-a)) * f u)
        (Real.exp (-c * (s-a)) * (f' s - c * f s)) s := by
    convert! (((hasDerivAt_id s).sub_const a).const_mul (-c)).exp.mul (hd s hs) using 1 <;> dsimp <;> ring
  have hmono : MonotoneOn (fun s => Real.exp (c * (s-a)) * f s) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.mul hf)
    · intro s hs
      exact (hplus s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Set.Ioo a b := by simpa only [interior_Icc] using hs
      change 0 ≤ deriv (fun u => Real.exp (c * (u-a)) * f u) s
      rw [(hplus s hs').deriv]
      exact mul_nonneg (Real.exp_pos _).le (by linarith [(hbound s hs').1])
  have hanti : AntitoneOn (fun s => Real.exp (-c * (s-a)) * f s) (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.mul hf)
    · intro s hs
      exact (hminus s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Set.Ioo a b := by simpa only [interior_Icc] using hs
      change deriv (fun u => Real.exp (-c * (u-a)) * f u) s ≤ 0
      rw [(hminus s hs').deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [(hbound s hs').2])
  have hl := hmono ⟨le_rfl, hab⟩ ht ht.1
  have hu := hanti ⟨le_rfl, hab⟩ ht ht.1
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hl hu
  constructor
  · have H := mul_le_mul_of_nonneg_left hl (Real.exp_pos (-c * (t-a))).le
    simpa only [← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero,
      one_mul] using H
  · have H := mul_le_mul_of_nonneg_left hu (Real.exp_pos (c * (t-a))).le
    simpa only [← mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero,
      one_mul] using H

/-- The actual Ricci tensor evaluated on the fixed project tangent vector. -/
def fieldRealRicciQuadratic (h : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) : ℝ :=
  ∑ i, ∑ j, realRicciCoeff h x (chartPt x x) i j *
    realCoord (tangentCoords x x v) i * realCoord (tangentCoords x x v) j

theorem metricFamilySmooth_tangentNorm_continuousOn
    (h : ℝ → HermitianField M) {I : Set ℝ} (hh : MetricFamilySmooth h I)
    (x : M.Carrier) (v : TangentVector M x) :
    ContinuousOn (fun s => 2 * hermitianNormSq ((h s) x) v) I := by
  have hc (i j : RIdx n) :
      ContinuousOn (fun s => realMetricFn (h s) x (chartPt x x) i j) I :=
    (hh x i j).continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_extChartAt_target x, hs⟩)
  have hsum : ContinuousOn (fun s => ∑ i, ∑ j,
      realMetricFn (h s) x (chartPt x x) i j *
        realCoord (tangentCoords x x v) i * realCoord (tangentCoords x x v) j) I :=
    continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _
      (fun j _ => ((hc i j).mul continuousOn_const).mul continuousOn_const))
  exact hsum.congr fun s _ => (realMetricTensor_quadratic (h s) x v).symm

theorem localRealRicciFlow_tangentNorm_hasDerivAt
    (h : ℝ → HermitianField M) {O : Set M.Carrier} {a b σ : ℝ}
    (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    {x : M.Carrier} (hx : x ∈ O) {t : ℝ} (ht : t ∈ Set.Ioo a b)
    (v : TangentVector M x) :
    HasDerivAt (fun s => 2 * hermitianNormSq ((h s) x) v)
      (-σ * fieldRealRicciQuadratic (h t) x v) t := by
  have hd (i j : RIdx n) :
      HasDerivAt (fun s => realMetricFn (h s) x (chartPt x x) i j)
        (-σ * realRicciCoeff (h t) x (chartPt x x) i j) t :=
    (hflow.2 x hx t ⟨ht.1.le, ht.2.le⟩ i j).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      ((hd i j).mul_const (realCoord (tangentCoords x x v) i)).mul_const
        (realCoord (tangentCoords x x v) j)))
  convert hsum using 1
  · ext s
    simpa only [Finset.sum_apply] using (realMetricTensor_quadratic (h s) x v).symm
  · simp only [fieldRealRicciQuadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring


theorem local_flow_metric_comparison
    (h : ℝ → HermitianField M) (p : M.Carrier) (a K r τ σ : ℝ)
    (hK : 0 < K) (_hr : 0 < r) (hτ : 0 < τ) (hσ : 0 < σ)
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r))
      (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ s ∈ Set.Icc a (a+2*τ),
      curvatureJetNorm (h s) 0 x ≤ K)
    (x : M.Carrier) (hx : x ∈ distBall (h a) p (2*r))
    (t : ℝ) (ht : t ∈ Set.Icc a (a+2*τ)) (v : TangentVector M x) :
    Real.exp (-2*σ*(2*n : ℕ)*K*τ) * (2*hermitianNormSq ((h a) x) v) ≤
      2*hermitianNormSq ((h t) x) v ∧
    2*hermitianNormSq ((h t) x) v ≤
      Real.exp (2*σ*(2*n : ℕ)*K*τ) * (2*hermitianNormSq ((h a) x) v) := by
  let Q : ℝ → ℝ := fun s => 2 * hermitianNormSq ((h s) x) v
  let c : ℝ := σ * (2*n : ℕ) * K
  have hQ (s : ℝ) : 0 ≤ Q s := mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _)
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg hσ.le (Nat.cast_nonneg _)) hK.le
  have hbound (s : ℝ) (hs : s ∈ Set.Ioo a (a+2*τ)) :
      -(c * Q s) ≤ -σ * fieldRealRicciQuadratic (h s) x v ∧
        -σ * fieldRealRicciQuadratic (h s) x v ≤ c * Q s := by
    have hRic := (realRicciQuadratic_abs_le (h s) x v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcurv x hx s ⟨hs.1.le, hs.2.le⟩)
          (Nat.cast_nonneg _)) (hQ s))
    change |fieldRealRicciQuadratic (h s) x v| ≤ (2*n : ℕ)*K*Q s at hRic
    have H := abs_le.mp hRic
    have Hlo := mul_le_mul_of_nonneg_left H.1 hσ.le
    have Hhi := mul_le_mul_of_nonneg_left H.2 hσ.le
    dsimp [c]
    constructor <;> nlinarith
  have H := exponential_comparison_on_Icc (f := Q)
    (f' := fun s => -σ * fieldRealRicciQuadratic (h s) x v)
    (c := c) (by linarith : a ≤ a+2*τ)
    (metricFamilySmooth_tangentNorm_continuousOn h hflow.1 x v)
    (fun s hs => localRealRicciFlow_tangentNorm_hasDerivAt h hflow hx hs v)
    hbound ht
  have hspan : t-a ≤ 2*τ := by linarith [ht.2]
  have helo : Real.exp (-2*σ*(2*n : ℕ)*K*τ) ≤ Real.exp (-c*(t-a)) := by
    apply Real.exp_le_exp.mpr
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_left hspan hc]
  have hehi : Real.exp (c*(t-a)) ≤ Real.exp (2*σ*(2*n : ℕ)*K*τ) := by
    apply Real.exp_le_exp.mpr
    dsimp [c]
    nlinarith [mul_le_mul_of_nonneg_left hspan hc]
  exact ⟨(mul_le_mul_of_nonneg_right helo (hQ a)).trans H.1,
    H.2.trans (mul_le_mul_of_nonneg_right hehi (hQ a))⟩

/-- The evolving distance cutoff uses the genuine project length distance. -/
def timeDistanceCutoff (h : ℝ → HermitianField M) (q : M.Carrier) (R : ℝ)
    (y : M.Carrier) (s : ℝ) : ℝ :=
  (max 0 (1 - inducedDistance (h s) q y ^ 2 / R ^ 2)) ^ 2

theorem timeDistanceCutoff_nonneg (h : ℝ → HermitianField M) (q : M.Carrier)
    (R : ℝ) (y : M.Carrier) (s : ℝ) : 0 ≤ timeDistanceCutoff h q R y s :=
  sq_nonneg _

theorem timeDistanceCutoff_le_one (h : ℝ → HermitianField M) (q : M.Carrier)
    (R : ℝ) (y : M.Carrier) (s : ℝ) : timeDistanceCutoff h q R y s ≤ 1 := by
  have ha : 1 - inducedDistance (h s) q y ^ 2 / R ^ 2 ≤ 1 :=
    sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hb : max 0 (1 - inducedDistance (h s) q y ^ 2 / R ^ 2) ≤ 1 := max_le zero_le_one ha
  have hc := le_max_left (0 : ℝ) (1 - inducedDistance (h s) q y ^ 2 / R ^ 2)
  dsimp only [timeDistanceCutoff]
  nlinarith

theorem timeDistanceCutoff_center (h : ℝ → HermitianField M) {I : Set ℝ}
    (hh : MetricFamilySmooth h I) (q : M.Carrier) (R : ℝ) {s : ℝ} (hs : s ∈ I) :
    timeDistanceCutoff h q R q s = 1 := by
  dsimp only [timeDistanceCutoff]
  rw [inducedDistance_self (h s) (metricFamilySmooth_slice h hh hs) q]
  norm_num

theorem timeDistanceCutoff_continuous_slice (h : ℝ → HermitianField M) {I : Set ℝ}
    (hh : MetricFamilySmooth h I) (q : M.Carrier) (R : ℝ) {s : ℝ} (hs : s ∈ I) :
    Continuous (fun y => timeDistanceCutoff h q R y s) := by
  exact (continuous_const.max
    (continuous_const.sub ((continuous_distFrom (h s) (metricFamilySmooth_slice h hh hs) q).pow 2
      |>.div_const (R ^ 2)))).pow 2

end Yau.LeafProofs.L23Aux
