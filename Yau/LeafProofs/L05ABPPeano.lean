import Yau.LeafProofs.L05ABPLasryConvexity
import Yau.LeafProofs.L05ABPGeometry
import Yau.LeafProofs.L01

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def jointPeanoJet {n : ℕ} (u : Point n → ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) : Prop :=
  (∀ v w, B v w = B w v) ∧
    (fun y => u y-u z-l (y-z)-(1/2 : ℝ)*B (y-z) (y-z))
      =o[𝓝 z] (fun y => ‖y-z‖^2)

def abpEuclideanEquiv (n : ℕ) :
    Point n ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (Point n))) :=
  (Module.finBasis ℝ (Point n)).equivFun.toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (Module.finrank ℝ (Point n)) => ℝ)).symm

theorem peano_transport {n : ℕ} {F : Point n → ℝ} {z : Point n}
    (h : L01Aux.Peano2At (F ∘ (abpEuclideanEquiv n).symm) (abpEuclideanEquiv n z)) :
    ∃ l B, jointPeanoJet F z l B := by
  let e := abpEuclideanEquiv n
  change L01Aux.Peano2At (F ∘ e.symm) (e z) at h
  obtain ⟨l,B,hB,hrem⟩ := h
  refine ⟨l.comp e.toContinuousLinearMap,B.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap,?_,?_⟩
  · intro v w
    exact hB (e v) (e w)
  · have hr := hrem.comp_tendsto (e.continuous.tendsto z)
    simp only [Function.comp_def,e.symm_apply_apply] at hr
    have ho : (fun y => ‖e (y-z)‖^2) =O[𝓝 z] (fun y => ‖y-z‖^2) := by
      simpa only [Pi.pow_apply] using (e.isBigO_sub (𝓝 z) z).norm_norm.pow 2
    change (fun y => F y-F z-l (e y-e z)-(1/2 : ℝ)*B (e y-e z) (e y-e z))
      =o[𝓝 z] (fun y => ‖e y-e z‖^2) at hr
    have hr' := hr.trans_isBigO (by simpa only [map_sub] using ho)
    change (fun y => F y-F z-l (e (y-z))-(1/2 : ℝ)*B (e (y-z)) (e (y-z)))
      =o[𝓝 z] (fun y => ‖y-z‖^2)
    simpa only [map_sub] using hr'

theorem convex_ae_jointPeano {n : ℕ} {F : Point n → ℝ}
    (hF : ConvexOn ℝ Set.univ F) :
    ∀ᵐ z ∂(volume : Measure (Point n)), ∃ l B, jointPeanoJet F z l B := by
  let L05ABPPeano_pointHaar : (volume : Measure (Point n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let e := abpEuclideanEquiv n
  have hFE : ConvexOn ℝ Set.univ (F ∘ e.symm) := by
    convert! hF.comp_linearMap e.symm.toLinearMap using 1
  have hae := L01Aux.ae_second_peano_on_open Set.univ (F ∘ e.symm) isOpen_univ hFE
  rw [Measure.restrict_univ] at hae
  let L05ABPPeano_mappedHaar : (Measure.map e (volume : Measure (Point n))).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map volume
  have hac : Measure.map e (volume : Measure (Point n)) ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have haemap := hae.filter_mono hac.ae_le
  have hep := ae_of_ae_map e.continuous.measurable.aemeasurable haemap
  filter_upwards [hep] with z hz
  exact peano_transport hz

def spaceInnerBilin (n : ℕ) : Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (innerₗ (Space n)) 1 (by
    intro v w
    simpa using norm_inner_le_norm (𝕜 := ℝ) v w)

def jointInnerBilin (n : ℕ) : Point n →L[ℝ] Point n →L[ℝ] ℝ :=
  (spaceInnerBilin n).bilinearComp (ContinuousLinearMap.fst ℝ (Space n) ℝ)
    (ContinuousLinearMap.fst ℝ (Space n) ℝ)+
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ (Space n) ℝ)
    (ContinuousLinearMap.snd ℝ (Space n) ℝ)

theorem jointInnerBilin_apply {n : ℕ} (z w : Point n) :
    jointInnerBilin n z w = inner ℝ z.1 w.1+z.2*w.2 := rfl

theorem jointInnerBilin_symm {n : ℕ} (z w : Point n) : jointInnerBilin n z w = jointInnerBilin n w z := by
  rw [jointInnerBilin_apply,jointInnerBilin_apply,real_inner_comm z.1 w.1,mul_comm z.2 w.2]

theorem qnorm2_expand {n : ℕ} (z y : Point n) :
    qnorm2 y = qnorm2 z+2*jointInnerBilin n z (y-z)+qnorm2 (y-z) := by
  simp only [jointInnerBilin_apply,qnorm2,Prod.fst_sub,Prod.snd_sub,norm_sub_sq_real,
    inner_sub_right,real_inner_self_eq_norm_sq]
  rw [real_inner_comm y.1 z.1]
  ring

theorem jointSemiconvex_ae_peano {n : ℕ} {K : ℝ} {w : Point n → ℝ}
    (hw : jointSemiconvex K w) :
    ∀ᵐ z ∂(volume : Measure (Point n)), ∃ l B, jointPeanoJet w z l B := by
  have hae := convex_ae_jointPeano hw
  filter_upwards [hae] with z hz
  obtain ⟨l,B,hB,hrem⟩ := hz
  refine ⟨l-K • jointInnerBilin n z,B-K • jointInnerBilin n,?_,?_⟩
  · intro v q
    simp only [sub_apply,smul_apply,smul_eq_mul]
    rw [hB v q,jointInnerBilin_symm v q]
  · have he : (fun y => w y-w z-(l-K • jointInnerBilin n z) (y-z)-
        (1/2 : ℝ)*(B-K • jointInnerBilin n) (y-z) (y-z)) =
        (fun y => (w y+(K/2)*qnorm2 y)-(w z+(K/2)*qnorm2 z)-l (y-z)-
          (1/2 : ℝ)*B (y-z) (y-z)) := by
      funext y
      rw [qnorm2_expand z y]
      simp only [sub_apply,smul_apply,smul_eq_mul,jointInnerBilin_apply,qnorm2,
        real_inner_self_eq_norm_sq]
      ring
    rw [he]
    exact hrem

def peanoPolynomial {n : ℕ} (c : ℝ) (z : Point n) (l : Point n →L[ℝ] ℝ)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (eta : ℝ) (y : Point n) : ℝ :=
  c+l (y-z)+(1/2 : ℝ)*B (y-z) (y-z)+eta*qnorm2 (y-z)

theorem qnorm2_smooth (n : ℕ) : ContDiff ℝ ∞ (qnorm2 (n := n)) := by
  have he : qnorm2 (n := n) = fun z => jointInnerBilin n z z := by
    funext z
    simp only [qnorm2,jointInnerBilin_apply,real_inner_self_eq_norm_sq]
    ring
  rw [he]
  fun_prop

theorem peanoPolynomial_smooth {n : ℕ} (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (eta : ℝ) :
    ContDiff ℝ ∞ (peanoPolynomial c z l B eta) := by
  unfold peanoPolynomial
  have hq := qnorm2_smooth n
  fun_prop

theorem jointPeanoJet_upper_test {n : ℕ} {w : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (h : jointPeanoJet w z l B) {eta : ℝ} (heta : 0 < eta) :
    touchAbove (peanoPolynomial (w z) z l B eta) w z := by
  refine ⟨by simp [peanoPolynomial,qnorm2],?_⟩
  filter_upwards [h.2.bound heta] with y hy
  have hn : ‖y-z‖^2 ≤ qnorm2 (y-z) := norm_sq_le_qnorm2 (y-z)
  have hab := (le_abs_self (w y-w z-l (y-z)-(1/2 : ℝ)*B (y-z) (y-z))).trans hy
  simp only [Real.norm_eq_abs,abs_pow,abs_norm] at hab
  have hm := mul_le_mul_of_nonneg_left hn heta.le
  dsimp only [peanoPolynomial]
  linarith

theorem jointPeanoJet_hasFDerivAt {n : ℕ} {w : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (h : jointPeanoJet w z l B) : HasFDerivAt w l z := by
  let R := fun y => w y-w z-l (y-z)-(1/2 : ℝ)*B (y-z) (y-z)
  have hR : HasFDerivAt R (0 : Point n →L[ℝ] ℝ) z :=
    h.2.isBigO.hasFDerivAt (by norm_num : 1 < (2:ℕ))
  have hs : HasFDerivAt (fun y : Point n => y-z) (ContinuousLinearMap.id ℝ (Point n)) z :=
    (hasFDerivAt_id z).sub_const z
  have hQ : HasFDerivAt (fun y => (1/2 : ℝ)*B (y-z) (y-z)) (0 : Point n →L[ℝ] ℝ) z := by
    simpa using (B.hasFDerivAt_of_bilinear hs hs).const_mul (1/2 : ℝ)
  have hP := ((l.hasFDerivAt.comp z hs).add_const (w z)).add hQ
  convert hR.add hP using 1
  · funext y
    dsimp [R]
    ring
  · simp

theorem jointPeanoJet_spatialD {n : ℕ} {w : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (h : jointPeanoJet w z l B) :
    spatialD w z = l.comp (ContinuousLinearMap.inl ℝ (Space n) ℝ) := by
  rw [spatialD_eq_joint (jointPeanoJet_hasFDerivAt h).differentiableAt,
    (jointPeanoJet_hasFDerivAt h).fderiv]

theorem jointPeanoJet_timeD {n : ℕ} {w : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (h : jointPeanoJet w z l B) : timeD Set.univ w z = l (0,1) := by
  have hp : HasDerivAt (fun t : ℝ => (z.1,t)) ((0,1) : Point n) z.2 := by
    simpa using (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hd := (jointPeanoJet_hasFDerivAt h).comp_hasDerivAt z.2 hp
  simpa [timeD,Function.comp_def] using hd.deriv

theorem symmetric_quadratic_hasFDerivAt {n : ℕ}
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (z y : Point n) :
    HasFDerivAt (fun q => (1/2 : ℝ)*B (q-z) (q-z)) (B (y-z)) y := by
  have hs := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const z
  convert! (B.hasFDerivAt_of_bilinear hs hs).const_mul (1/2 : ℝ) using 1
  apply ContinuousLinearMap.ext
  intro v
  change B (y-z) v = (1/2 : ℝ)*(B (y-z) v+B v (y-z))
  rw [hB v (y-z)]
  ring

theorem peanoPolynomial_hasFDerivAt {n : ℕ} (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (eta : ℝ) (y : Point n) :
    HasFDerivAt (peanoPolynomial c z l B eta)
      (l+B (y-z)+(2*eta) • jointInnerBilin n (y-z)) y := by
  have hs := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const z
  have hq := (symmetric_quadratic_hasFDerivAt (jointInnerBilin n)
    (jointInnerBilin_symm) z y).const_mul (2*eta)
  have hl := (l.hasFDerivAt.comp y hs).const_add c
  have hb := symmetric_quadratic_hasFDerivAt B hB z y
  convert! (hl.add hb).add hq using 1
  · funext q
    simp only [peanoPolynomial,jointInnerBilin_apply,qnorm2,real_inner_self_eq_norm_sq,
      Pi.add_apply,Function.comp_def,id_eq]
    ring

theorem peanoPolynomial_spatialDD {n : ℕ} (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (eta : ℝ) (y : Point n) :
    spatialDD (peanoPolynomial c z l B eta) y =
      (B+(2*eta) • jointInnerBilin n).bilinearComp
        (ContinuousLinearMap.inl ℝ (Space n) ℝ) (ContinuousLinearMap.inl ℝ (Space n) ℝ) := by
  let i := ContinuousLinearMap.inl ℝ (Space n) ℝ
  let M := B+(2*eta) • jointInnerBilin n
  have hp : HasFDerivAt (fun x : Space n => ((x,y.2) : Point n)-z) i y.1 := by
    simpa only [i,ContinuousLinearMap.inl_apply,Prod.mk_add_mk,zero_add,add_zero] using
      ((i.hasFDerivAt (x := y.1)).add_const ((0,y.2) : Point n)).sub_const z
  have hd : HasFDerivAt (fun x : Space n => l+M ((x,y.2)-z)) (M.comp i) y.1 :=
    (M.hasFDerivAt.comp y.1 hp).const_add l
  have hc : HasFDerivAt (fun x : Space n => (l+M ((x,y.2)-z)).comp i)
      (M.bilinearComp i i) y.1 := by
    convert! hd.clm_comp (hasFDerivAt_const i y.1) using 1
    ext v w
    simp [ContinuousLinearMap.bilinearComp_apply]
  have he : (fun x : Space n => spatialD (peanoPolynomial c z l B eta) (x,y.2)) =
      (fun x : Space n => (l+M ((x,y.2)-z)).comp i) := by
    funext x
    rw [spatialD_eq_joint (peanoPolynomial_hasFDerivAt c z l B hB eta (x,y.2)).differentiableAt,
      (peanoPolynomial_hasFDerivAt c z l B hB eta (x,y.2)).fderiv]
    ext v
    simp [M,i,add_assoc]
  change fderiv ℝ (fun x : Space n => spatialD (peanoPolynomial c z l B eta) (x,y.2)) y.1 = _
  rw [he]
  exact hc.fderiv

theorem peanoPolynomial_timeD {n : ℕ} (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (eta : ℝ) :
    timeD Set.univ (peanoPolynomial c z l B eta) z = l (0,1) := by
  have hp : HasDerivAt (fun t : ℝ => (z.1,t)) ((0,1) : Point n) z.2 := by
    simpa using (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hd := (peanoPolynomial_hasFDerivAt c z l B hB eta z).comp_hasDerivAt z.2 hp
  simpa [timeD,Function.comp_def] using hd.deriv

theorem peanoPolynomial_hessian {n : ℕ} (c : ℝ) (z : Point n)
    (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (eta : ℝ) (y : Point n) :
    hessian (peanoPolynomial c z l B eta) y =
      sym (fun i j => B (Yau.realVec i,0) (Yau.realVec j,0)+
        (2*eta)*inner ℝ (Yau.realVec i) (Yau.realVec j)) := by
  unfold hessian
  rw [peanoPolynomial_spatialDD c z l B hB eta y]
  congr 1
  funext i j
  simp [ContinuousLinearMap.bilinearComp_apply,jointInnerBilin_apply]

end Yau.LeafProofs.L05Aux
