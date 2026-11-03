import Yau.LeafProofs.L23LocalDistanceSupportEscape

/-! Comparison between any two times, needed for the joint continuity of
the clipped local distance. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exponential_comparison_between_on_Icc {f f' : ℝ → ℝ} {a b c : ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hd : ∀ u ∈ Set.Ioo a b, HasDerivAt f (f' u) u)
    (hbound : ∀ u ∈ Set.Ioo a b, -(c * f u) ≤ f' u ∧ f' u ≤ c * f u)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    Real.exp (-c*|t-s|)*f s ≤ f t ∧ f t ≤ Real.exp (c*|t-s|)*f s := by
  have hord (u v : ℝ) (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) (huv : u ≤ v) :
      Real.exp (-c*(v-u))*f u ≤ f v ∧ f v ≤ Real.exp (c*(v-u))*f u := by
    apply exponential_comparison_on_Icc huv
      (hf.mono (Set.Icc_subset_Icc hu.1 hv.2))
      (fun z hz => hd z ⟨hu.1.trans_lt hz.1, hz.2.trans_le hv.2⟩)
      (fun z hz => hbound z ⟨hu.1.trans_lt hz.1, hz.2.trans_le hv.2⟩)
      ⟨huv,le_rfl⟩
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hord s t hs ht hst
  · have H := hord t s ht hs hts
    rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub]
    constructor
    · have H' := mul_le_mul_of_nonneg_left H.2 (Real.exp_pos (-c*(s-t))).le
      simpa only [← mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel,
        Real.exp_zero, one_mul] using H'
    · have H' := mul_le_mul_of_nonneg_left H.1 (Real.exp_pos (c*(s-t))).le
      simpa only [← mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel,
        Real.exp_zero, one_mul] using H'

theorem local_flow_metric_comparison_between
    (h : ℝ → HermitianField M) (p : M.Carrier) (a K r τ σ : ℝ)
    (_hK : 0 < K) (_hr : 0 < r) (_hτ : 0 < τ) (hσ : 0 < σ)
    (hflow : LocalRealRicciFlow h (distBall (h a) p (2*r)) (Set.Icc a (a+2*τ)) σ)
    (hcurv : ∀ x ∈ distBall (h a) p (2*r), ∀ u ∈ Set.Icc a (a+2*τ),
      curvatureJetNorm (h u) 0 x ≤ K)
    (x : M.Carrier) (hx : x ∈ distBall (h a) p (2*r))
    (s t : ℝ) (hs : s ∈ Set.Icc a (a+2*τ)) (ht : t ∈ Set.Icc a (a+2*τ))
    (v : TangentVector M x) :
    Real.exp (-(σ*(2*n : ℕ)*K)*|t-s|)*(2*hermitianNormSq ((h s) x) v) ≤
      2*hermitianNormSq ((h t) x) v ∧
    2*hermitianNormSq ((h t) x) v ≤
      Real.exp ((σ*(2*n : ℕ)*K)*|t-s|)*(2*hermitianNormSq ((h s) x) v) := by
  let Q : ℝ → ℝ := fun u => 2*hermitianNormSq ((h u) x) v
  let c := σ*(2*n : ℕ)*K
  have hQ (u : ℝ) : 0 ≤ Q u := mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _)
  have hbound (u : ℝ) (hu : u ∈ Set.Ioo a (a+2*τ)) :
      -(c*Q u) ≤ -σ*fieldRealRicciQuadratic (h u) x v ∧
        -σ*fieldRealRicciQuadratic (h u) x v ≤ c*Q u := by
    have hRic := (realRicciQuadratic_abs_le (h u) x v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcurv x hx u ⟨hu.1.le, hu.2.le⟩)
          (Nat.cast_nonneg _)) (hQ u))
    change |fieldRealRicciQuadratic (h u) x v| ≤ (2*n : ℕ)*K*Q u at hRic
    have H := abs_le.mp hRic
    have Hlo := mul_le_mul_of_nonneg_left H.1 hσ.le
    have Hhi := mul_le_mul_of_nonneg_left H.2 hσ.le
    dsimp [c]
    constructor <;> nlinarith
  exact exponential_comparison_between_on_Icc
    (metricFamilySmooth_tangentNorm_continuousOn h hflow.1 x v)
    (fun u hu => localRealRicciFlow_tangentNorm_hasDerivAt h hflow hx hu v) hbound hs ht

end Yau.LeafProofs.L23Aux
