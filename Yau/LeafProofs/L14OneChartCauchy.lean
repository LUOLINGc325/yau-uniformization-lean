import Yau.LeafProofs.L14ChartNorm
import Yau.LeafProofs.L14CutoffNorm
import Yau.LeafProofs.L14InverseDual

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
theorem weightedOneChartSection_cauchySeq_of_model_errors
    (a : M.Carrier) (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hKO : K ⊆ localDomain (r := r) E a)
    (F : ℕ → ComplexVector n → Fin n → ComplexVector r)
    (hF : ∀ j,ContDiff ℝ ∞ (F j)) (hsF : ∀ j,tsupport (F j) ⊆ K)
    (G : ComplexVector n → Fin n → ComplexVector r)
    (he : ∀ j (c : Fin n × Fin r),MemLp (fun z => F j z c.1 c.2-G z c.1 c.2) 2 (lebesgueC n))
    (ht : ∀ c : Fin n × Fin r,Tendsto (fun j => ∫ z,‖F j z c.1 c.2-G z c.1 c.2‖^2 ∂lebesgueC n) atTop (𝓝 0)) :
    CauchySeq (fun j => realizeWeightedOneSection E g μ hμ h hh φ hφ
      (weightedOneChartSection E g μ hμ h hh φ hφ hE a (F j) (hF j)
        (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO))) := by
  classical
  let U := fun j => weightedOneChartSection E g μ hμ h hh φ hφ hE a (F j) (hF j)
    (hK.of_isClosed_subset (isClosed_tsupport _) (hsF j)) ((hsF j).trans hKO)
  let V := fun j => realizeWeightedOneSection E g μ hμ h hh φ hφ (U j)
  let e := fun j z (c : Fin n × Fin r) => F j z c.1 c.2-G z c.1 c.2
  let I := fun j => ∑ c : Fin n × Fin r,∫ z,‖e j z c‖^2 ∂lebesgueC n
  have hIn (j : ℕ) : 0 ≤ I j := Finset.sum_nonneg fun c _ => integral_nonneg fun z => sq_nonneg _
  have htI : Tendsto I atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun c _ => ht c)
  have hsComp (j : ℕ) (c : Fin n × Fin r) : tsupport (fun z => F j z c.1 c.2) ⊆ K :=
    (tsupport_comp_subset (g := fun W : Fin n → ComplexVector r => W c.1 c.2) (by rfl) (F j)).trans (hsF j)
  obtain ⟨C,hC,hbound⟩ := weightedNormSq_one_le_compact_model_errors E g μ hμ h hh φ hφ a K hK hKO
  have hPair (j k : ℕ) : ‖V j-V k‖^2 ≤ 2*C*(I j+I k) := by
    let d := fun z (c : Fin n × Fin r) => F j z c.1 c.2-F k z c.1 c.2
    have hd (c : Fin n × Fin r) : MemLp (fun z => d z c) 2 (lebesgueC n) := by
      apply ((he j c).sub (he k c)).ae_eq
      exact Eventually.of_forall fun z => by
        change (F j z c.1 c.2-G z c.1 c.2)-(F k z c.1 c.2-G z c.1 c.2) = F j z c.1 c.2-F k z c.1 c.2
        ring
    have hds (c : Fin n × Fin r) : tsupport (fun z => d z c) ⊆ K :=
      tsupport_sub_subset_closed hK.isClosed (hsComp j c) (hsComp k c)
    have hzero (x : M.Carrier) (hx : x ∉ bundleChartSource (r := r) E a) :
        (U j-U k).1 x = (0 : NQForm E 1) x := by
      have hsub := WeightedOneSection.toForm_sub E g μ hμ h hh φ hφ (U j) (U k)
      change (U j-U k).1 = (U j).1-(U k).1 at hsub
      rw [hsub]
      apply Subtype.ext
      change (oneFormPushforward (r := r) E a (F j) x).1-(oneFormPushforward (r := r) E a (F k) x).1 = _
      simp only [oneFormPushforward,dite_eq_right hx]
      exact sub_self _
    have hcoef (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (c : Fin n × Fin r) :
        coefficients (r := r) E (U j-U k).1 a z (fun _ => c.1) c.2 = d z c := by
      have hsub := WeightedOneSection.toForm_sub E g μ hμ h hh φ hφ (U j) (U k)
      change (U j-U k).1 = (U j).1-(U k).1 at hsub
      rw [hsub,coefficients_sub]
      change coefficients (r := r) E (oneFormPushforward E a (F j)) a z (fun _ => c.1) c.2-
        coefficients (r := r) E (oneFormPushforward E a (F k)) a z (fun _ => c.1) c.2 = _
      rw [oneFormPushforward_coefficients E a (F j) z hz,oneFormPushforward_coefficients E a (F k) z hz]
    have hb := hbound (U j-U k).1 (U j-U k).2.1 hzero d hd hds hcoef
    have hn : ‖V j-V k‖^2 = (weightedNormSq (r := r) E g.form h μ φ (U j-U k).1).toReal := by
      rw [← realizeWeightedOneSection_sub,realizeWeightedOneSection_norm_sq]
      rfl
    have hreal : ‖V j-V k‖^2 ≤ C*∑ c,∫ z,‖d z c‖^2 ∂lebesgueC n := by
      rw [hn]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hC (Finset.sum_nonneg fun c _ => integral_nonneg fun z => sq_nonneg _)))
    have hI (c : Fin n × Fin r) :
        (∫ z,‖d z c‖^2 ∂lebesgueC n) ≤
          2*((∫ z,‖e j z c‖^2 ∂lebesgueC n)+(∫ z,‖e k z c‖^2 ∂lebesgueC n)) := by
      have hij := (memLp_two_iff_integrable_sq_norm (he j c).aestronglyMeasurable).mp (he j c)
      have hik := (memLp_two_iff_integrable_sq_norm (he k c).aestronglyMeasurable).mp (he k c)
      rw [← integral_add hij hik,← integral_const_mul]
      apply integral_mono ((memLp_two_iff_integrable_sq_norm (hd c).aestronglyMeasurable).mp (hd c)) ((hij.add hik).const_mul 2)
      intro z
      change ‖d z c‖^2 ≤ 2*(‖e j z c‖^2+‖e k z c‖^2)
      have heq : d z c = e j z c-e k z c := by dsimp only [d,e];ring
      have hnorm := norm_sub_le (e j z c) (e k z c)
      rw [← heq] at hnorm
      have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
      nlinarith [sq_nonneg (‖e j z c‖-‖e k z c‖)]
    apply hreal.trans
    calc
      C*∑ c,∫ z,‖d z c‖^2 ∂lebesgueC n ≤
          C*∑ c,2*((∫ z,‖e j z c‖^2 ∂lebesgueC n)+(∫ z,‖e k z c‖^2 ∂lebesgueC n)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hI c) hC
      _ = _ := by
        dsimp only [I]
        rw [← Finset.mul_sum,Finset.sum_add_distrib]
        ring
  let b := fun j => Real.sqrt (2*C*I j)
  have hbn (j : ℕ) : 0 ≤ b j := Real.sqrt_nonneg _
  have hb : Tendsto b atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp (htI.const_mul (2*C))
    simpa only [b,Function.comp_def,mul_zero,Real.sqrt_zero] using ht
  have hdist (j k : ℕ) : dist (V j) (V k) ≤ b j+b k := by
    rw [dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (hbn j) (hbn k))).mp
    have hj : b j^2 = 2*C*I j := Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hC) (hIn j))
    have hk : b k^2 = 2*C*I k := Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hC) (hIn k))
    nlinarith [hPair j k,mul_nonneg (hbn j) (hbn k)]
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hb.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N,fun j hj k hk => (hdist j k).trans_lt ?_⟩
  linarith [hN j hj,hN k hk]

end Yau.LeafProofs.L14Aux
