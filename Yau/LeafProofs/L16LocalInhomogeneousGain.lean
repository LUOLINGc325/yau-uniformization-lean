import Yau.LeafProofs.L16InhomogeneousWeakGain
import Yau.LeafProofs.L16WeakEvolutionCutoff

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem local_inhomogeneous_spatial_weak_derivative_gain {n : ℕ}
    {Q V : Set (Point n)} (hQ : IsOpen Q) (hV : IsOpen V)
    (hVC : IsCompact (closure V)) (hVQ : closure V ⊆ Q)
    {a : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {lam upper C : ℝ}
    (hC : 0 ≤ C) (hEll : Elliptic Q a lam upper)
    (ha : ContDiff ℝ ∞ a) (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hAVal : ∀ p, ‖a p‖ ≤ C) (hCVal : ∀ j p, |c p j| ≤ C)
    (hADq : ∀ i h p, ‖spatialDifferenceQuotient a (Yau.realVec i) h p‖ ≤ C)
    (hCDq : ∀ j i h p, |spatialDifferenceQuotient (fun q => c q j) (Yau.realVec i) h p| ≤ C)
    {w R f : Point n → ℝ} {H P F J : Point n → Yau.RIdx n → ℝ}
    {K : Yau.RIdx n → Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 (volume.restrict Q))
    (hH : ∀ j, MemLp (fun p => H p j) 2 (volume.restrict Q))
    (hP : ∀ j, MemLp (fun p => P p j) 2 (volume.restrict Q))
    (hR : MemLp R 2 (volume.restrict Q))
    (hGrad : WeakGradientOn Q w H) (hEq : WeakDivergenceEvolutionOn Q w P R)
    (hF : ∀ j, MemLp (fun p => F p j) 2 (volume.restrict Q))
    (hf : MemLp f 2 (volume.restrict Q))
    (hK : ∀ j k, MemLp (fun p => K j p k) 2 (volume.restrict Q))
    (hJ : ∀ k, MemLp (fun p => J p k) 2 (volume.restrict Q))
    (hGradF : ∀ j, WeakGradientOn Q (fun p => F p j) (K j))
    (hGradf : WeakGradientOn Q f J)
    (hFlux : ∀ p ∈ Q, ∀ j, P p j = energyFlux a H p j+F p j)
    (hSource : ∀ p ∈ Q, R p = (∑ j, c p j*H p j)+f p)
    (i j : Yau.RIdx n) :
    ∃ Z : Point n → ℝ, MemLp Z 2 (volume.restrict V) ∧
      ∀ φ : Point n → ℝ, Test V φ →
        (∫ p, H p j*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V) =
          -(∫ p, Z p*φ p ∂volume.restrict V) := by
  obtain ⟨U,hU,hVU,hUQ,hUC⟩ := exists_open_between_and_isCompact_closure hVC hQ hVQ
  obtain ⟨η,hη,hNear⟩ := exists_test_eq_one_near_compact hQ hUC hUQ
  have hUQ' : U ⊆ Q := subset_closure.trans hUQ
  have hOne (p : Point n) (hp : p ∈ U) : η p = 1 :=
    (hNear p (subset_closure hp)).eq_of_nhds
  let w0 : Point n → ℝ := fun p => η p*w p
  let H0 : Point n → Yau.RIdx n → ℝ := fun p k => η p*H p k+w p*fderiv ℝ η p (Yau.realVec k,0)
  let P0 : Point n → Yau.RIdx n → ℝ := fun p k => η p*P p k
  let R0 : Point n → ℝ := cutoffEvolutionSource w P R η
  let F0 : Point n → Yau.RIdx n → ℝ := fun p k => η p*F p k
  let f0 : Point n → ℝ := fun p => η p*f p
  let K0 : Yau.RIdx n → Point n → Yau.RIdx n → ℝ := fun k p z =>
    η p*K k p z+F p k*fderiv ℝ η p (Yau.realVec z,0)
  let J0 : Point n → Yau.RIdx n → ℝ := fun p z =>
    η p*J p z+f p*fderiv ℝ η p (Yau.realVec z,0)
  obtain ⟨hw0,hcw0,hH0,hGrad0⟩ := weakGradientOn_cutoff_weakH1 hQ hw hH hGrad hη
  obtain ⟨_hw0,_hcw0,hP0,hR0,hcR0,hEq0⟩ := weakDivergenceEvolutionOn_cutoff_fields hQ hw hP hR hEq hη
  have hF0Data (k : Yau.RIdx n) := weakGradientOn_cutoff_weakH1 hQ (hF k) (hK k) (hGradF k) hη
  obtain ⟨hf0,hcf0,hJ0,hGradf0⟩ := weakGradientOn_cutoff_weakH1 hQ hf hJ hGradf hη
  have hHPlateau (p : Point n) (hp : p ∈ U) : ∀ k, H0 p k = H p k :=
    (weakGradientOn_cutoff_eq_on_open_plateau hU hOne w H hp).2
  have hDη (p : Point n) (hp : p ∈ U) : fderiv ℝ η p = 0 :=
    fderiv_cutoff_eq_zero_on_open_plateau hU hOne hp
  have hFlux0 (p : Point n) (hp : p ∈ U) (k : Yau.RIdx n) :
      P0 p k = energyFlux a H0 p k+F0 p k := by
    dsimp only [P0,F0]
    rw [hOne p hp,one_mul,one_mul,hFlux p (hUQ' hp)]
    simp only [energyFlux,hHPlateau p hp]
  have hSource0 (p : Point n) (hp : p ∈ U) :
      R0 p = (∑ k, c p k*H0 p k)+f0 p := by
    have hTime : deriv (fun t => η (p.1,t)) p.2 = 0 := by
      rw [test_timeDerivative_eq_joint_fderiv (hη.1.differentiable (by simp) p),hDη p hp,zero_apply]
    have hSpace (k : Yau.RIdx n) : d (fun x => η (x,p.2)) p.1 k = 0 := by
      rw [d_eq_joint_fderiv (hη.1.differentiable (by simp) p) k,hDη p hp,zero_apply]
    simp only [R0,cutoffEvolutionSource,hOne p hp,hTime,hSpace,mul_zero,Finset.sum_const_zero,
      one_mul,add_zero,sub_zero,hHPlateau p hp,f0]
    exact hSource p (hUQ' hp)
  have hEllU : Elliptic U a lam upper :=
    ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p (hUQ' hp)⟩
  obtain ⟨Z,hZ,hZWeak⟩ := inhomogeneous_global_weak_fields_spatial_derivative_gain
    hU hV hVC hVU hC hEllU ha hc hAVal hCVal hADq hCDq
    hw0 (fun k => (hH0 k).1) (fun k => (hP0 k).1) hR0 hcw0
    (fun k => (hH0 k).2) (fun k => (hP0 k).2) hcR0 hGrad0 hEq0
    (fun k => (hF0Data k).1) hf0 (fun k z => ((hF0Data k).2.2.1 z).1) (fun z => (hJ0 z).1)
    (fun k => (hF0Data k).2.1) hcf0 (fun k z => ((hF0Data k).2.2.1 z).2) (fun z => (hJ0 z).2)
    (fun k => (hF0Data k).2.2.2) hGradf0 hFlux0 hSource0 i j
  refine ⟨Z,hZ,?_⟩
  intro φ hφ
  have hIdent : (∫ p, H p j*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V) =
      ∫ p, H0 p j*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with p hp
    rw [hHPlateau p (hVU (subset_closure hp)) j]
  exact hIdent.trans (hZWeak φ hφ)

end Yau.LeafProofs.L16Aux
