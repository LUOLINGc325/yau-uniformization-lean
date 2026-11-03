import Yau.LeafProofs.L16LocalWeakEvolution
import Yau.LeafProofs.L16InteriorCoefficients

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Continuity gives the actual local L² bound on a relatively compact region. -/
theorem continuous_memLp_two_relcompact {n : ℕ} {V : Set (Point n)}
    (hVC : IsCompact (closure V)) {f : Point n → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict V) := by
  let : IsFiniteMeasure (volume.restrict (closure V)) :=
    ⟨by simpa using hVC.measure_lt_top (μ := volume)⟩
  obtain ⟨C,hC⟩ := hVC.exists_bound_of_continuousOn hf.continuousOn
  have h : MemLp f 2 (volume.restrict (closure V)) := MemLp.of_bound
    hf.aestronglyMeasurable C (by
      filter_upwards [ae_restrict_mem isClosed_closure.measurableSet] with p hp
      exact hC p hp)
  exact h.mono_measure (Measure.restrict_mono subset_closure le_rfl)

/-- The classical directional derivative satisfies the concrete test identity. -/
theorem smooth_test_directional_ibp {n : ℕ} {Q : Set (Point n)}
    {v φ : Point n → ℝ} (hv : ContDiff ℝ ∞ v) (hφ : Test Q φ) (e : Point n) :
    (∫ p, v p*fderiv ℝ φ p e ∂volume.restrict Q) =
      -(∫ p, fderiv ℝ v p e*φ p ∂volume.restrict Q) := by
  rw [test_pairing_integral_restrict (test_directionalDerivative hφ e) v,
    test_pairing_integral_restrict hφ (fun p => fderiv ℝ v p e)]
  have hDv : Continuous (fun p => fderiv ℝ v p e) :=
    ((hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hDv.mul hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.1.mul_left)
    ((hv.continuous.mul (test_directionalDerivative hφ e).1.continuous).integrable_of_hasCompactSupport
      (hφ.2.1.fderiv_apply ℝ e).mul_left)
    ((hv.continuous.mul hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.1.mul_left)
    (fun p _ => hv.differentiable (by simp) p)
    (fun p _ => hφ.1.differentiable (by simp) p)

/-- A smooth representative has precisely the original energy gradient. -/
theorem localEnergy_smooth_representative_gradient {n : ℕ}
    {O : Set (Space n)} {l r : ℝ} (hO : IsOpen O)
    {u v : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    {V : Set (Point n)} (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVQ : closure V ⊆ O ×ˢ Set.Ioo l r)
    (hv : ContDiff ℝ ∞ v) (hAE : u =ᵐ[volume.restrict V] v) :
    ∀ i, (fun p => G p i) =ᵐ[volume.restrict V]
      (fun p => fderiv ℝ v p (Yau.realVec i,0)) := by
  have hG := (localEnergy_memLp_on_compact hO hE hVC hVQ).2
  have hW := weakGradientOn_mono
    ((weakGradientOn_prod_iff O (Set.Ioo l r) u G).2 hE.1) (subset_closure.trans hVQ)
  intro i
  apply ae_eq_of_test_integrals_eq hV
    ((hG i).mono_measure (Measure.restrict_mono subset_closure le_rfl))
    (continuous_memLp_two_relcompact hVC
      ((hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous)
  intro φ hφ
  have hLeft : (∫ p, u p*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V) =
      ∫ p, v p*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V := by
    apply integral_congr_ae
    filter_upwards [hAE] with p hp
    rw [hp]
  have h1 := hW φ hφ i
  have h2 := smooth_test_directional_ibp hv hφ (Yau.realVec i,0)
  rw [hLeft] at h1
  linarith

/-- Conversion from the joint Hessian to the frozen spatial Hessian. -/
theorem smooth_joint_spatial_hessian {n : ℕ} {v : Point n → ℝ}
    (hv : ContDiff ℝ ∞ v) (p : Point n) (i j : Yau.RIdx n) :
    fderiv ℝ (fun q => fderiv ℝ v q (Yau.realVec j,0)) p (Yau.realVec i,0) =
      spatialDD v p (Yau.realVec i) (Yau.realVec j) := by
  have hDj : ContDiff ℝ ∞ (fun q => fderiv ℝ v q (Yau.realVec j,0)) :=
    (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [← d_eq_joint_fderiv (hDj.differentiable (by simp) p) i]
  have hEq : (fun x : Space n => fderiv ℝ v (x,p.2) (Yau.realVec j,0)) =
      fun x => fderiv ℝ (fun y => v (y,p.2)) x (Yau.realVec j) := by
    funext x
    exact (d_eq_joint_fderiv (hv.differentiable (by simp) (x,p.2)) j).symm
  rw [hEq]
  unfold d spatialDD
  apply fderiv_clm_const_eval
  exact ((hv.comp (contDiff_id.prodMk contDiff_const)).fderiv_right
    (m := ∞) (by simp)).differentiable (by simp) p.1

/-- For smooth fields, the concrete distributional evolution equation is pointwise. -/
theorem smooth_weakDivergenceEvolutionOn_classical {n : ℕ} {V : Set (Point n)}
    (hV : IsOpen V) (hVC : IsCompact (closure V))
    {v R : Point n → ℝ} {P : Point n → Yau.RIdx n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hP : ∀ i, ContDiff ℝ ∞ (fun p => P p i))
    (hR : Continuous R) (hEq : WeakDivergenceEvolutionOn V v P R) :
    ∀ p ∈ V, fderiv ℝ v p (0,1)-
      (∑ i, fderiv ℝ (fun q => P q i) p (Yau.realVec i,0))-R p = 0 := by
  let T : Point n → ℝ := fun p => fderiv ℝ v p (0,1)
  let S : Yau.RIdx n → Point n → ℝ :=
    fun i p => fderiv ℝ (fun q => P q i) p (Yau.realVec i,0)
  have hT : Continuous T :=
    ((hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hS (i : Yau.RIdx n) : Continuous (S i) :=
    (((hP i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  let E : Point n → ℝ := fun p => T p-(∑ i, S i p)-R p
  have hE : Continuous E := (hT.sub (continuous_finsetSum _ (fun i _ => hS i))).sub hR
  have hEA : E =ᵐ[volume.restrict V] 0 := by
    apply ae_eq_of_test_integrals_eq hV (continuous_memLp_two_relcompact hVC hE) MemLp.zero'
    intro φ hφ
    have hTInt : Integrable (fun p => T p*φ p) (volume.restrict V) :=
      (continuous_memLp_two_relcompact hVC hT).integrable_mul (test_memLp hφ)
    have hSInt (i : Yau.RIdx n) : Integrable (fun p => S i p*φ p) (volume.restrict V) :=
      (continuous_memLp_two_relcompact hVC (hS i)).integrable_mul (test_memLp hφ)
    have hRInt : Integrable (fun p => R p*φ p) (volume.restrict V) :=
      (continuous_memLp_two_relcompact hVC hR).integrable_mul (test_memLp hφ)
    have hSumInt : Integrable (fun p => (∑ i, S i p)*φ p) (volume.restrict V) := by
      simpa only [Finset.sum_mul] using integrable_finsetSum Finset.univ (fun i _ => hSInt i)
    have h := hEq φ hφ
    rw [smooth_test_directional_ibp hv hφ (0,1)] at h
    simp_rw [smooth_test_directional_ibp (hP _) hφ (Yau.realVec _,0)] at h
    rw [Finset.sum_neg_distrib] at h
    change (∫ p, (T p-(∑ i, S i p)-R p)*φ p ∂volume.restrict V) = _
    simp_rw [sub_mul]
    have hSplit1 := integral_sub (hTInt.sub hSumInt) hRInt
    have hSplit2 := integral_sub hTInt hSumInt
    simp only [Pi.sub_apply] at hSplit1 hSplit2
    rw [hSplit1,hSplit2]
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum Finset.univ (fun i _ => hSInt i)]
    simp only [zero_mul,integral_zero]
    dsimp only [T,S] at *
    linarith
  exact Measure.eqOn_open_of_ae_eq hEA hV hE.continuousOn continuousOn_const

/-- The original weak homogeneous equation holds classically for any smooth
representative on a relatively compact open interior region. -/
theorem localEnergy_weakEquation_smooth_representative_classical {n : ℕ}
    {O : Set (Space n)} {l r : ℝ} (hO : IsOpen O)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    {u v : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    {V : Set (Point n)} (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVQ : closure V ⊆ O ×ˢ Set.Ioo l r)
    (hv : ContDiff ℝ ∞ v) (hAE : u =ᵐ[volume.restrict V] v) :
    (∀ i, (fun p => G p i) =ᵐ[volume.restrict V]
      (fun p => fderiv ℝ v p (Yau.realVec i,0))) ∧
      ∀ p ∈ V, linearOp V a b v p = 0 := by
  classical
  have hQ : IsOpen (O ×ˢ Set.Ioo l r) := hO.prod isOpen_Ioo
  have hVSub : V ⊆ O ×ˢ Set.Ioo l r := subset_closure.trans hVQ
  have hGAE := localEnergy_smooth_representative_gradient hO hE hV hVC hVQ hv hAE
  refine ⟨hGAE,?_⟩
  obtain ⟨A,c,C,_hC,hA,_hcA,hc,hAgree,_hAVal,_hADq,_hcVal,_hcDq⟩ :=
    exists_compact_coefficient_extensions hQ hVC hVQ hSmooth
  let D : Point n → Yau.RIdx n → ℝ := fun p j => fderiv ℝ v p (Yau.realVec j,0)
  let P : Point n → Yau.RIdx n → ℝ := energyFlux A D
  let R : Point n → ℝ := fun p => ∑ j, c p j*D p j
  have hD (j : Yau.RIdx n) : ContDiff ℝ ∞ (fun p => D p j) :=
    (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hP (i : Yau.RIdx n) : ContDiff ℝ ∞ (fun p => P p i) := by
    apply ContDiff.sum
    intro j _
    exact ((matrixEntryCLM i j).contDiff.comp hA).mul (hD j)
  have hR : ContDiff ℝ ∞ R := by
    apply ContDiff.sum
    intro j _
    exact (hc j).1.mul (hD j)
  have hAG (p : Point n) (hp : p ∈ V) : A p = a p :=
    (hAgree p (subset_closure hp)).1.eq_of_nhds
  have hcG (p : Point n) (hp : p ∈ V) (j : Yau.RIdx n) : c p j = energyDrift a b p j :=
    ((hAgree p (subset_closure hp)).2 j).eq_of_nhds
  have hEqNew : WeakDivergenceEvolutionOn V v P R := by
    intro φ hφ
    have hφQ : Test (O ×ˢ Set.Ioo l r) φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans hVSub⟩
    have h := weakEquation_homogeneous_divergence hEq φ hφQ
    rw [productVolume_eq_restrict] at h
    simp_rw [test_timeDerivative_eq_joint_fderiv (hφ.1.differentiable (by simp) _),
      d_eq_joint_fderiv (hφ.1.differentiable (by simp) _)] at h
    rw [divergence_test_integral_restrict_eq_global hφQ] at h
    rw [← divergence_test_integral_restrict_eq_global hφ] at h
    have hChange : (∫ p, -u p*fderiv ℝ φ p (0,1)+
        (∑ i, energyFlux a G p i*fderiv ℝ φ p (Yau.realVec i,0))-
        (∑ j, energyDrift a b p j*G p j)*φ p ∂volume.restrict V) =
        ∫ p, -v p*fderiv ℝ φ p (0,1)+
          (∑ i, P p i*fderiv ℝ φ p (Yau.realVec i,0))-R p*φ p ∂volume.restrict V := by
      apply integral_congr_ae
      filter_upwards [hAE,(ae_all_iff.2 hGAE),ae_restrict_mem hV.measurableSet] with p hp hGp hpV
      dsimp only [P,R,energyFlux,D]
      simp_rw [hp,hGp,← hAG p hpV,← hcG p hpV]
    rw [hChange,integral_divergence_test_form
      (continuous_memLp_two_relcompact hVC hv.continuous)
      (fun i => continuous_memLp_two_relcompact hVC (hP i).continuous)
      (continuous_memLp_two_relcompact hVC hR.continuous) hφ] at h
    exact h
  have hClass := smooth_weakDivergenceEvolutionOn_classical hV hVC hv hP hR.continuous hEqNew
  intro p hp
  have hCoeff (i j : Yau.RIdx n) :
      fderiv ℝ (fun q => A q i j) p (Yau.realVec i,0) =
        d (fun x => a (x,p.2) i j) p.1 i := by
    have hNear : (fun q => A q i j) =ᶠ[𝓝 p] (fun q => a q i j) := by
      filter_upwards [(hAgree p (subset_closure hp)).1] with q hq
      rw [hq]
    rw [hNear.fderiv_eq]
    exact (d_eq_joint_fderiv
      (((((matrixEntryCLM i j).contDiff.comp_contDiffOn hSmooth.1) p (hVSub hp)).contDiffAt
        (hQ.mem_nhds (hVSub hp))).differentiableAt (by simp)) i).symm
  have hFlux (i : Yau.RIdx n) :
      fderiv ℝ (fun q => P q i) p (Yau.realVec i,0) =
        ∑ j, (d (fun x => a (x,p.2) i j) p.1 i*D p j+
          a p i j*spatialDD v p (Yau.realVec i) (Yau.realVec j)) := by
    have hDiff (j : Yau.RIdx n) (_ : j ∈ Finset.univ) :
        DifferentiableAt ℝ (fun q => A q i j*D q j) p :=
      (((matrixEntryCLM i j).contDiff.comp hA).mul (hD j)).differentiable (by simp) p
    change fderiv ℝ (fun q => ∑ j, A q i j*D q j) p (Yau.realVec i,0) = _
    rw [fderiv_fun_sum hDiff]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hAij : DifferentiableAt ℝ (fun q => A q i j) p :=
      ((matrixEntryCLM i j).contDiff.comp hA).differentiable (by simp) p
    rw [fderiv_fun_mul hAij ((hD j).differentiable (by simp) p)]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [hCoeff i j,hAG p hp]
    change a p i j*fderiv ℝ (fun q => fderiv ℝ v q (Yau.realVec j,0)) p (Yau.realVec i,0)+D p j*_ = _
    rw [smooth_joint_spatial_hessian hv]
    ring
  have hResidual := hClass p hp
  simp_rw [hFlux] at hResidual
  have hDSpatial (j : Yau.RIdx n) : D p j = spatialD v p (Yau.realVec j) :=
    (d_eq_joint_fderiv (hv.differentiable (by simp) p) j).symm
  have hRFormula : R p = ∑ j, (b p j-∑ i, d (fun x => a (x,p.2) i j) p.1 i)*D p j := by
    dsimp only [R]
    apply Finset.sum_congr rfl
    intro j _
    rw [hcG p hp j]
    rfl
  rw [hRFormula] at hResidual
  simp_rw [Finset.sum_add_distrib,sub_mul,Finset.sum_sub_distrib,Finset.sum_mul] at hResidual
  have hSwap : (∑ i, ∑ j, d (fun x => a (x,p.2) i j) p.1 i*D p j) =
      ∑ j, ∑ i, d (fun x => a (x,p.2) i j) p.1 i*D p j := Finset.sum_comm
  rw [hSwap] at hResidual
  simp_rw [hDSpatial] at hResidual
  unfold linearOp
  rw [timeD_eq_deriv_of_isOpen hV hp,test_timeDerivative_eq_joint_fderiv (hv.differentiable (by simp) p)]
  linarith

end Yau.LeafProofs.L16Aux
