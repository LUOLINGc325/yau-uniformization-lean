import Yau.LeafProofs.L05PerronLattice
import Yau.LeafProofs.L05ABPQuadraticPolynomial
import Yau.LeafProofs.L05JetCombinationTaylor

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perronSlab (n : ℕ) : Set (Point n) := Metric.closedBall 0 1 ×ˢ Set.Ico (-1) 1

def perronOpen (n : ℕ) : Set (Point n) := abpOpen n 1 (-1) 1

def perronBoundary (n : ℕ) : Set (Point n) :=
  (Metric.closedBall 0 1 ×ˢ ({-1} : Set ℝ)) ∪
    (Metric.sphere 0 1 ×ˢ Set.Ico (-1) 1)

theorem perronOpen_isOpen (n : ℕ) : IsOpen (perronOpen n) :=
  Metric.isOpen_ball.prod isOpen_Ioo

theorem perronOpen_subset_slab {n : ℕ} : perronOpen n⊆perronSlab n :=
  fun _ hz => ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2⟩

theorem perronBoundary_subset_slab {n : ℕ} : perronBoundary n⊆perronSlab n := by
  intro p hp
  rcases hp with hp | hp
  · exact ⟨hp.1,by rw [show p.2=(-1:ℝ) from hp.2]; norm_num⟩
  · exact ⟨Metric.sphere_subset_closedBall hp.1,hp.2⟩

theorem unitClosed_subset_perronSlab {n : ℕ} : unitClosed n⊆perronSlab n :=
  fun _ hp => ⟨hp.1,hp.2.1,hp.2.2.trans_lt (by norm_num)⟩

theorem unitOpen_subset_perronOpen {n : ℕ} : unitOpen n⊆perronOpen n :=
  fun _ hp => ⟨hp.1,hp.2.1,hp.2.2.trans (by norm_num)⟩

theorem parabolicBoundary_subset_perronBoundary {n : ℕ} :
    parabolicBoundary n⊆perronBoundary n := by
  intro p hp
  rcases hp with hp | hp
  · exact Or.inl hp
  · exact Or.inr ⟨hp.1,hp.2.1,hp.2.2.trans_lt (by norm_num)⟩

theorem perron_local_c2_jets {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hp : ContDiffAt ℝ 2 phi p) :
    ∃ V : Set (Point n), IsOpen V ∧ p∈V ∧
      (∀ q∈V, ContDiffAt ℝ 2 phi q) ∧
      ContinuousOn (timeD Set.univ phi) V ∧ ContinuousOn (hessian phi) V := by
  let V := interior {q | ContDiffAt ℝ 2 phi q}
  have hpV : p∈V := mem_interior_iff_mem_nhds.mpr (hp.eventually (by norm_num))
  have hV (q : Point n) (hq : q∈V) : ContDiffAt ℝ 2 phi q := interior_subset hq
  refine ⟨V,isOpen_interior,hpV,hV,?_,?_⟩
  · have hc : ContinuousOn (fun q => fderiv ℝ phi q ((0,1) : Point n)) V := by
      intro q hq
      exact (((hV q hq).fderiv_right (m := 1) (by norm_num)).continuousAt.clm_apply
        continuousAt_const).continuousWithinAt
    apply hc.congr
    intro q hq
    exact timeD_univ_eq_joint ((hV q hq).differentiableAt (by norm_num))
  · have hc : ContinuousOn (fun q => jointHessian (fderiv ℝ (fderiv ℝ phi) q)) V := by
      intro q hq
      have hdd := (((hV q hq).fderiv_right (m := 1) (by norm_num)).fderiv_right
        (m := 0) (by norm_num)).continuousAt
      exact ((jointHessian_continuous n).continuousAt.comp hdd).continuousWithinAt
    apply hc.congr
    intro q hq
    exact jet_hessian_eq_joint_at (hV q hq)

theorem perron_timeD_sub {n : ℕ} {phi s : Point n → ℝ} {p : Point n}
    (hp : ContDiffAt ℝ 2 phi p) (hs : ContDiffAt ℝ 2 s p) :
    timeD Set.univ (fun q => phi q-s q) p=timeD Set.univ phi p-timeD Set.univ s p := by
  have hpd := hp.differentiableAt (by norm_num)
  have hsd := hs.differentiableAt (by norm_num)
  change timeD Set.univ (phi-s) p=timeD Set.univ phi p-timeD Set.univ s p
  rw [timeD_univ_eq_joint (hpd.sub hsd),timeD_univ_eq_joint hpd,timeD_univ_eq_joint hsd,
    fderiv_sub hpd hsd]
  rfl

theorem perron_hessian_sub {n : ℕ} {phi s : Point n → ℝ} {p : Point n}
    (hp : ContDiffAt ℝ 2 phi p) (hs : ContDiffAt ℝ 2 s p) :
    hessian (fun q => phi q-s q) p=hessian phi p-hessian s p := by
  rw [jet_hessian_eq_joint_at (hp.sub hs),jet_hessian_eq_joint_at hp,
    jet_hessian_eq_joint_at hs,L16Aux.secondFDeriv_sub hp hs]
  exact (selfAdjointPart ℝ).map_sub _ _

theorem perron_localMax_timeD_zero {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hp : ContDiffAt ℝ 2 phi p) (hm : IsLocalMax phi p) : timeD Set.univ phi p=0 := by
  have hd := hp.differentiableAt (by norm_num)
  rw [timeD_univ_eq_joint hd,hm.hasFDerivAt_eq_zero hd.hasFDerivAt]
  rfl

theorem perron_spatial_localMax_hessian_nonpos {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hp : ContDiffAt ℝ 2 phi p) (hm : IsLocalMax (fun x : Space n => phi (x,p.2)) p.1) :
    (-(hessian phi p : Mat n)).PosSemidef := by
  have hs : ContDiffAt ℝ 2 (fun x : Space n => phi (x,p.2)) p.1 := by
    exact hp.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
  have hnon (v : Space n) : spatialDD phi p v v≤0 :=
    L16Aux.secondFDeriv_nonpos_of_isLocalMax hs hm v
  have hraw : (hessian phi p : Mat n)=secondFDerivMatrix (fun x => phi (x,p.2)) p.1 :=
    hessian_space_eq_secondFDeriv hs
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr (hessian phi p).property.neg)
  intro v
  have hh := hnon (∑ i, v i • Yau.realVec i)
  simp only [map_sum,map_smul,sum_apply,smul_apply,Finset.mul_sum,smul_eq_mul] at hh
  rw [hraw]
  simp only [dotProduct,Matrix.mulVec,Matrix.neg_apply,secondFDerivMatrix,
    Pi.star_apply,star_trivial,Finset.mul_sum]
  change 0≤∑ i,∑ j,v i*(-(spatialDD phi p (Yau.realVec i) (Yau.realVec j))*v j)
  have he : (∑ i,∑ j,v i*(-(spatialDD phi p (Yau.realVec i) (Yau.realVec j))*v j))=
      -(∑ i,∑ j,v i*(v j*spatialDD phi p (Yau.realVec j) (Yau.realVec i))) := by
    rw [Finset.sum_comm]
    simp only [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

theorem perron_localMax_hessian_nonpos {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hp : ContDiffAt ℝ 2 phi p) (hm : IsLocalMax phi p) :
    (-(hessian phi p : Mat n)).PosSemidef := by
  apply perron_spatial_localMax_hessian_nonpos hp
  have hpath : Tendsto (fun x : Space n => (x,p.2)) (𝓝 p.1) (𝓝 p) := by
    simpa only [id_eq,Prod.eta] using (continuous_id.prodMk continuous_const).tendsto p.1
  filter_upwards [hpath hm] with x hx
  exact hx

theorem perron_touch_classical_jets {n : ℕ} {phi s : Point n → ℝ} {p : Point n}
    (hp : ContDiffAt ℝ 2 phi p) (hs : ContDiffAt ℝ 2 s p) (ht : touchAbove phi s p) :
    timeD Set.univ phi p=timeD Set.univ s p ∧
      ((hessian phi p : Mat n)-(hessian s p : Mat n)).PosSemidef := by
  have hm : IsLocalMax (fun q => s q-phi q) p := by
    filter_upwards [ht.2] with q hq
    change s q-phi q ≤ s p-phi p
    linarith [ht.1]
  constructor
  · have hh := perron_localMax_timeD_zero (hs.sub hp) hm
    rw [perron_timeD_sub hs hp] at hh
    linarith
  · have hh := perron_localMax_hessian_nonpos (hs.sub hp) hm
    rwa [perron_hessian_sub hs hp,AddSubgroup.coe_sub,neg_sub] at hh

end Yau.LeafProofs.L05Aux
