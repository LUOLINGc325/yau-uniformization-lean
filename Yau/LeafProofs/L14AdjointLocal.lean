import Yau.LeafProofs.L14CompactAdjoint

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix Kronecker
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
theorem adjoint_graph_pairing
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S V : WeightedTopSection E g μ hμ h hh φ hφ)
    (D : WeightedOneSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (hVD : WeakDbar (r := r) E V.1 D.1) :
    weightedTopInner E g.form μ h φ S.1 V.1 =
      weightedOneInner E g.form μ h φ U.1 D.1 := by
  let T := weightedMaximalDbar E g μ hμ h hh φ hφ
  obtain ⟨u, hu, hTu⟩ := T.adjoint.mem_graph_iff.mp hUS
  have hmem : (realizeWeightedTopSection E g μ hμ h hh φ hφ V,
      realizeWeightedOneSection E g μ hμ h hh φ hφ D) ∈ T.graph := by
    rw [weightedMaximalDbar_graph]
    exact (weightedMaximalDbarHilbertGraph_realize_iff E g μ hμ h hh φ hφ V D).mpr hVD
  obtain ⟨v, hv, hTv⟩ := T.mem_graph_iff.mp hmem
  have hp := LinearPMap.adjoint_isFormalAdjoint
    (weightedMaximalDbar_domain_dense E g μ hμ h hh φ hφ hE) u v
  rw [hTu, hTv, hu, hv] at hp
  rw [realizeWeightedTopSection_inner, realizeWeightedOneSection_inner] at hp
  exact hp

include hh hφ in
theorem chartOneDual_contDiffOn
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ∀ i α, ContDiffOn ℝ ∞ (fun z => F z i α) (localDomain (r := r) E a))
    (i : Fin n) (α : Fin r) :
    ContDiffOn ℝ ∞ (fun z => chartOneDual (r := r) E g.form h φ a F z i α)
      (localDomain (r := r) E a) := by
  have hρ : ContDiffOn ℝ ∞ (fun z => (Real.exp (-φ (chartInv a z)) : ℂ))
      (localDomain (r := r) E a) :=
    (((hφ a).neg.exp).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  apply hρ.mul
  apply ContDiffOn.sum
  intro j _
  apply ((L18Aux.hMat_inverse_contDiffOn g a i j).mono Set.inter_subset_left).mul
  apply ContDiffOn.sum
  intro β _
  exact (hh a α β).mul (hF j β)

theorem chartOneDual_conj_symm
    (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (F G : ComplexVector n → Fin n → ComplexVector r) :
    (∑ i, ∑ α, star (F z i α) * chartOneDual (r := r) E g h φ a G z i α) =
      ∑ i, ∑ α, star (chartOneDual (r := r) E g h φ a F z i α) * G z i α := by
  let P := chartOneMetricMatrix (r := r) E g h a z
  let v := fun p : Fin n × Fin r => F z p.1 p.2
  let w := fun p : Fin n × Fin r => G z p.1 p.2
  let ρ : ℂ := Real.exp (-φ (chartInv a z))
  have hdual (Q : ComplexVector n → Fin n → ComplexVector r) (i : Fin n) (α : Fin r) :
      chartOneDual (r := r) E g h φ a Q z i α =
        ρ * (P *ᵥ (fun p => Q z p.1 p.2)) (i, α) := by
    simp only [chartOneDual, P, chartOneMetricMatrix, Matrix.mulVec, dotProduct,
      Matrix.kronecker_apply, Fintype.sum_prod_type, Finset.mul_sum, ρ, mul_assoc]
  have hherm : P.IsHermitian := (chartOneMetricMatrix_posDef (r := r) E g h a z hz).isHermitian
  have he : star v ⬝ᵥ (P *ᵥ w) = star (P *ᵥ v) ⬝ᵥ w := by
    rw [Matrix.star_mulVec, hherm.eq, Matrix.dotProduct_mulVec]
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, v, w] at he
  simp_rw [hdual, star_mul]
  have hρ : star ρ = ρ := by simp only [ρ, Complex.star_def, Complex.conj_ofReal]
  rw [hρ]
  calc
    _ = ρ * (∑ i, ∑ α, star (F z i α) *
        (P *ᵥ (fun p => G z p.1 p.2)) (i, α)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro α _
      ring
    _ = ρ * (∑ i, ∑ α, star ((P *ᵥ (fun p => F z p.1 p.2)) (i, α)) *
        G z i α) := congrArg (ρ * ·) he
    _ = _ := by simp only [Finset.mul_sum]; ring_nf

theorem hermitian_real_weight_pairing {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (ρ : ℝ) (v w : ι → ℂ) :
    (∑ α, ∑ β, star (v α) * H α β * w β) * (ρ : ℂ) =
      ∑ β, star ((H *ᵥ v) β * (ρ : ℂ)) * w β := by
  have he : star v ⬝ᵥ (H *ᵥ w) = star (H *ᵥ v) ⬝ᵥ w := by
    rw [Matrix.star_mulVec, hH.eq, Matrix.dotProduct_mulVec]
  have he' : (∑ α, ∑ β, star (v α) * H α β * w β) =
      ∑ β, star ((H *ᵥ v) β) * w β := by
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc] using he
  rw [he', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro β _
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

include hh hφ in
theorem chart_formal_adjoint_pairing
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ∀ i α, ContDiffOn ℝ ∞ (fun z => F z i α) (localDomain (r := r) E a))
    (G : ComplexVector n → ComplexVector r) (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (hs : tsupport G ⊆ localDomain (r := r) E a) :
    (∫ z, ∑ i, ∑ α, star (F z i α) *
      chartOneDual (r := r) E g.form h φ a (modelTopDbar G) z i α ∂lebesgueC n) =
    ∫ z, (∑ α, ∑ β,
      star (chartDbarAdjoint (r := r) E g.form h φ a F z α) *
        BundleDbar.metricMatrix (r := r) E h a z α β * G z β) *
          (Real.exp (-φ (chartInv a z)) : ℂ) ∂lebesgueC n := by
  classical
  let O := localDomain (r := r) E a
  let B := chartOneDual (r := r) E g.form h φ a F
  let δ := chartDbarAdjoint (r := r) E g.form h φ a F
  have hB (i : Fin n) (α : Fin r) : ContDiffOn ℝ ∞ (fun z => B z i α) O :=
    chartOneDual_contDiffOn E g h hh φ hφ a F hF i α
  have hGα (α : Fin r) : ContDiff ℝ ∞ (fun z => G z α) := (contDiff_piLp 2).mp hG α
  have hsGα (α : Fin r) : tsupport (fun z => G z α) ⊆ tsupport G :=
    tsupport_comp_subset (g := fun v : ComplexVector r => v α) (by rfl) G
  have hcGα (α : Fin r) : HasCompactSupport (fun z => G z α) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (hsGα α)
  have hDG (i : Fin n) (α : Fin r) : ContDiff ℝ ∞
      (fun z => wirtBar (fun y => G y α) z (stdVec i)) := by
    simpa only [contDiffOn_univ] using wirtBar_contDiffOn isOpen_univ _ (hGα α).contDiffOn (stdVec i)
  have hsDG (i : Fin n) (α : Fin r) :
      tsupport (fun z => wirtBar (fun y => G y α) z (stdVec i)) ⊆ tsupport G :=
    (closure_minimal (support_wirtBar_subset _ _) (isClosed_tsupport _)).trans (hsGα α)
  have hL (i : Fin n) (α : Fin r) : Integrable
      (fun z => star (B z i α) * wirtBar (fun y => G y α) z (stdVec i)) (lebesgueC n) := by
    have he := integrable_compactTest_mul_complex (localDomain_isOpen E a) (hDG i α).continuous
      (hc.of_isClosed_subset (isClosed_tsupport _) (hsDG i α)) ((hsDG i α).trans hs)
      ((hB i α).continuousOn.star)
    simpa only [mul_comm] using he
  have hR (i : Fin n) (α : Fin r) : Integrable
      (fun z => star (wirt (fun y => B y i α) z (stdVec i)) * G z α) (lebesgueC n) := by
    have he := integrable_compactTest_mul_complex (localDomain_isOpen E a) (hGα α).continuous
      (hcGα α) ((hsGα α).trans hs)
      ((wirt_contDiffOn (localDomain_isOpen E a) _ (hB i α) (stdVec i)).continuousOn.star)
    simpa only [mul_comm] using he
  have hIBP (i : Fin n) (α : Fin r) :
      (∫ z, star (B z i α) * wirtBar (fun y => G y α) z (stdVec i) ∂lebesgueC n) =
      -(∫ z, star (wirt (fun y => B y i α) z (stdVec i)) * G z α ∂lebesgueC n) := by
    have he := integral_compactTest_wirtBar_on (localDomain_isOpen E a) (hGα α)
      (hcGα α) ((hsGα α).trans hs)
      ((hB i α).continuousLinearMap_comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)) (stdVec i)
    change (∫ z, wirtBar (fun y => star (B y i α)) z (stdVec i) * G z α ∂lebesgueC n) =
      -(∫ z, star (B z i α) * wirtBar (fun y => G y α) z (stdVec i) ∂lebesgueC n) at he
    simp only [wirtBar_star] at he
    simpa only [neg_neg] using congrArg Neg.neg he.symm
  have hsum (P : Fin n → Fin r → ComplexVector n → ℂ)
      (hP : ∀ i α, Integrable (P i α) (lebesgueC n)) :
      (∫ z, ∑ i, ∑ α, P i α z ∂lebesgueC n) = ∑ i, ∑ α, ∫ z, P i α z ∂lebesgueC n := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun α _ => hP i α))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finset_sum _ (fun α _ => hP i α)
  have hpointL (z : ComplexVector n) :
      (∑ i, ∑ α, star (F z i α) * chartOneDual (r := r) E g.form h φ a (modelTopDbar G) z i α) =
      ∑ i, ∑ α, star (B z i α) * wirtBar (fun y => G y α) z (stdVec i) := by
    by_cases hz : z ∈ O
    · exact chartOneDual_conj_symm E g.form h φ a z hz F (modelTopDbar G)
    · have hd : modelTopDbar G z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hn => hz ((tsupport_modelTopDbar_subset G).trans hs hn))
      have he (i : Fin n) (α : Fin r) : wirtBar (fun y => G y α) z (stdVec i) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y => wirtBar (fun w => G w α) y (stdVec i))
          (fun hn => hz ((hsDG i α).trans hs hn))
      simp only [chartOneDual, hd, Pi.zero_apply, PiLp.zero_apply, he, mul_zero,
        Finset.sum_const_zero]
  have hpointR (z : ComplexVector n) :
      (∑ α, ∑ β, star (δ z α) * BundleDbar.metricMatrix (r := r) E h a z α β * G z β) *
        (Real.exp (-φ (chartInv a z)) : ℂ) =
      -(∑ i, ∑ α, star (wirt (fun y => B y i α) z (stdVec i)) * G z α) := by
    by_cases hz : z ∈ O
    · rw [hermitian_real_weight_pairing _ (metricMatrix_posDef E h a z hz).isHermitian]
      have hδdual : ∀ α, (BundleDbar.metricMatrix (r := r) E h a z *ᵥ (fun β => δ z β)) α *
          (Real.exp (-φ (chartInv a z)) : ℂ) =
          -∑ i, wirt (fun y => B y i α) z (stdVec i)  :=
        fun α => chartDbarAdjoint_dual E g.form h φ a F z hz α
      simp only [hδdual, star_neg, star_sum, Finset.sum_neg_distrib, Finset.sum_mul]
      simp only [neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
    · have hzG : G z = 0 := image_eq_zero_of_notMem_tsupport (fun hn => hz (hs hn))
      simp only [hzG, PiLp.zero_apply, mul_zero, Finset.sum_const_zero, zero_mul, neg_zero]
  calc
    _ = ∫ z, ∑ i, ∑ α, star (B z i α) * wirtBar (fun y => G y α) z (stdVec i) ∂lebesgueC n :=
      integral_congr_ae (Eventually.of_forall hpointL)
    _ = ∑ i, ∑ α, ∫ z, star (B z i α) * wirtBar (fun y => G y α) z (stdVec i) ∂lebesgueC n := hsum _ hL
    _ = -(∑ i, ∑ α, ∫ z, star (wirt (fun y => B y i α) z (stdVec i)) * G z α ∂lebesgueC n) := by
      simp_rw [hIBP, Finset.sum_neg_distrib]
    _ = -(∫ z, ∑ i, ∑ α, star (wirt (fun y => B y i α) z (stdVec i)) * G z α ∂lebesgueC n) :=
      congrArg Neg.neg (hsum _ hR).symm
    _ = _ := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun z => (hpointR z).symm)

include hh hφ in
theorem chartDbarAdjoint_contDiffOn
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ∀ i α, ContDiffOn ℝ ∞ (fun z => F z i α) (localDomain (r := r) E a))
    (α : Fin r) :
    ContDiffOn ℝ ∞ (fun z => chartDbarAdjoint (r := r) E g.form h φ a F z α)
      (localDomain (r := r) E a) := by
  have hρ : ContDiffOn ℝ ∞ (fun z => (Real.exp (φ (chartInv a z)) : ℂ))
      (localDomain (r := r) E a) :=
    (((hφ a).exp).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  have hdet : ∀ z ∈ localDomain (r := r) E a,
      (BundleDbar.metricMatrix (r := r) E h a z).det ≠ 0 := fun z hz =>
    ((metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom).ne_zero
  apply hρ.neg.mul
  apply ContDiffOn.sum
  intro β _
  apply (L18Aux.contDiffOn_matrix_inv (hh a) hdet α β).mul
  apply ContDiffOn.sum
  intro i _
  exact wirt_contDiffOn (localDomain_isOpen E a) _
    (chartOneDual_contDiffOn E g h hh φ hφ a F hF i β) (stdVec i)

include hE in
theorem adjoint_graph_chart_test_pairing
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (a : M.Carrier) (G : ComplexVector n → ComplexVector r)
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    (hs : tsupport G ⊆ localDomain (r := r) E a) :
    (∫ z, (∑ α, ∑ β, star (coefficients (r := r) E S.1 a z Fin.elim0 α) *
        BundleDbar.metricMatrix (r := r) E h a z α β * G z β) *
          (Real.exp (-φ (chartInv a z)) : ℂ) ∂lebesgueC n) =
      ∫ z, ∑ i, ∑ α, star (coefficients (r := r) E U.1 a z (fun _ => i) α) *
        chartOneDual (r := r) E g.form h φ a (modelTopDbar G) z i α ∂lebesgueC n := by
  let hg := topFormPushforward_maximalDbarGraph E g μ hμ h hh φ hφ hE a G hG hc hs
  let V : WeightedTopSection E g μ hμ h hh φ hφ := ⟨topFormPushforward (r := r) E a G, hg.1⟩
  let D : WeightedOneSection E g μ hμ h hh φ hφ :=
    ⟨oneFormPushforward (r := r) E a (modelTopDbar G), hg.2.1⟩
  have hp := adjoint_graph_pairing E g μ hμ h hh φ hφ hE U S V D hUS hg.2.2
  have hcD : HasCompactSupport (modelTopDbar G) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelTopDbar_subset G)
  have hsD := (tsupport_modelTopDbar_subset G).trans hs
  rw [weightedTopInner_topFormPushforward_right E g μ hμ h hh φ hφ hE a G hG hc hs S,
    weightedOneInner_oneFormPushforward_right E g μ hμ h hh φ hφ hE a (modelTopDbar G)
      (modelTopDbar_smooth G hG) hcD hsD U] at hp
  simp only [Complex.real_smul] at hp
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) n))) hp

include hE in
theorem smooth_adjoint_local_formula
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hU : SmoothForm (r := r) E U.1) (hS : SmoothForm (r := r) E S.1)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    coefficients (r := r) E S.1 a z Fin.elim0 =
      chartDbarAdjoint (r := r) E g.form h φ a
        (fun w i => coefficients (r := r) E U.1 a w (fun _ => i)) z := by
  classical
  let O := localDomain (r := r) E a
  let F := fun w i => coefficients (r := r) E U.1 a w (fun _ => i)
  let δ := chartDbarAdjoint (r := r) E g.form h φ a F
  let V := fun w α => (∑ β, BundleDbar.metricMatrix (r := r) E h a w α β * δ w β) *
    (Real.exp (-φ (chartInv a w)) : ℂ)
  let W := fun w α => weightedTopDualCoefficient (r := r) E h φ S.1 a w α
  have hF (i : Fin n) (α : Fin r) : ContDiffOn ℝ ∞ (fun w => F w i α) O := hU a (fun _ => i) α
  have hρ : ContDiffOn ℝ ∞ (fun w => (Real.exp (-φ (chartInv a w)) : ℂ)) O :=
    (((hφ a).neg.exp).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  have hV (α : Fin r) : ContinuousOn (fun w => V w α) O := by
    apply ContinuousOn.mul _ hρ.continuousOn
    apply continuousOn_finset_sum
    intro β _
    exact (hh a α β).continuousOn.mul
      (chartDbarAdjoint_contDiffOn E g h hh φ hφ a F hF β).continuousOn
  have hW (α : Fin r) : ContinuousOn (fun w => W w α) O := by
    apply ContinuousOn.mul _ hρ.continuousOn
    apply continuousOn_finset_sum
    intro β _
    exact (hh a α β).continuousOn.mul (hS a Fin.elim0 β).continuousOn
  have htest (α : Fin r) (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ O) :
      (∫ w, star (W w α) * (ψ w : ℂ) ∂lebesgueC n) =
        ∫ w, star (V w α) * (ψ w : ℂ) ∂lebesgueC n := by
    obtain ⟨hG, hcG, hsG⟩ := scalarTopTest_properties α 1 ψ hψ hc
    let G := scalarTopTest α 1 ψ
    have hsGO := hsG.trans hs
    have he := (adjoint_graph_chart_test_pairing E g μ hμ h hh φ hφ hE U S hUS a G hG hcG hsGO).trans
      (chart_formal_adjoint_pairing E g h hh φ hφ a F hF G hG hcG hsGO)
    have hpoint (v : ComplexVector n → ComplexVector r) (w : ComplexVector n) :
        (∑ β, ∑ γ, star (v w β) * BundleDbar.metricMatrix (r := r) E h a w β γ * G w γ) *
          (Real.exp (-φ (chartInv a w)) : ℂ) =
        star ((∑ β, BundleDbar.metricMatrix (r := r) E h a w α β * v w β) *
          (Real.exp (-φ (chartInv a w)) : ℂ)) * (ψ w : ℂ) := by
      by_cases hw : w ∈ O
      · rw [hermitian_real_weight_pairing _ (metricMatrix_posDef E h a w hw).isHermitian]
        simp [G, scalarTopTest, stdVec, PiLp.single_apply, Pi.single_apply, Matrix.mulVec, dotProduct, mul_assoc]
      · have hψw : ψ w = 0 := image_eq_zero_of_notMem_tsupport (fun hn => hw (hs hn))
        simp [G, scalarTopTest, hψw]
    calc
      _ = ∫ w, (∑ β, ∑ γ, star (coefficients (r := r) E S.1 a w Fin.elim0 β) *
          BundleDbar.metricMatrix (r := r) E h a w β γ * G w γ) *
          (Real.exp (-φ (chartInv a w)) : ℂ) ∂lebesgueC n :=
        integral_congr_ae (Eventually.of_forall fun w => (hpoint (fun y => coefficients (r := r) E S.1 a y Fin.elim0) w).symm)
      _ = _ := he
      _ = _ := integral_congr_ae (Eventually.of_forall (hpoint δ))
  have hzero (α : Fin r) : ∀ w ∈ O, W w α = V w α := by
    let Q := fun w => star (W w α) - star (V w α)
    have hQ : ContinuousOn Q O := (hW α).star.sub (hV α).star
    letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
    letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
    have hae : ∀ᵐ w ∂lebesgueC n, w ∈ O → Q w = 0 :=
      (localDomain_isOpen E a).ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hQ.locallyIntegrableOn (localDomain_isOpen E a).measurableSet) (by
          intro ψ hψ hc hs
          have hiW := integrable_compactTest_mul_complex (localDomain_isOpen E a)
            (Complex.continuous_ofReal.comp hψ.continuous)
            (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero ψ).trans hs)
            (hW α).star
          have hiV := integrable_compactTest_mul_complex (localDomain_isOpen E a)
            (Complex.continuous_ofReal.comp hψ.continuous)
            (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero ψ).trans hs)
            (hV α).star
          dsimp only [Function.comp_def] at hiW hiV
          simp only [Q, Complex.real_smul, mul_sub]
          rw [integral_sub hiW hiV]
          have ht := htest α ψ hψ hc hs
          simpa only [mul_comm] using sub_eq_zero.mpr ht)
    have heq : Set.EqOn Q 0 O := MeasureTheory.Measure.eqOn_open_of_ae_eq
      ((ae_restrict_iff' (localDomain_isOpen E a).measurableSet).mpr hae)
      (localDomain_isOpen E a) hQ continuousOn_const
    intro w hw
    exact star_injective (sub_eq_zero.mp (heq hw))
  let H := BundleDbar.metricMatrix (r := r) E h a z
  let c := fun α => coefficients (r := r) E S.1 a z Fin.elim0 α
  have hρz : (Real.exp (-φ (chartInv a z)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
  have heq : H *ᵥ c = H *ᵥ (fun α => δ z α) := by
    funext α
    exact mul_right_cancel₀ hρz (hzero α z hz)
  have hinv := congrArg (fun v => H⁻¹ *ᵥ v) heq
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((metricMatrix_posDef E h a z hz).isUnit.map Matrix.detMonoidHom),
    Matrix.one_mulVec, Matrix.one_mulVec] at hinv
  apply (WithLp.ofLp_injective 2)
  exact hinv

end Yau.LeafProofs.L14Aux
