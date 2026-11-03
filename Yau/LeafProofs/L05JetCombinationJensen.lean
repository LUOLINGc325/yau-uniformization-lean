import Yau.LeafProofs.L05JetCombinationTaylor
import Yau.LeafProofs.L04

open Filter MeasureTheory Asymptotics Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem jet_semiconvex_weighted {n : ℕ} {U V : Point n → ℝ} {K1 K2 a b : ℝ}
    (hU : jointSemiconvex K1 U) (hV : jointSemiconvex K2 V)
    (ha : 0≤a) (hb : 0≤b) :
    jointSemiconvex (a*K1+b*K2) (fun z => a*U z+b*V z) := by
  have h := (hU.smul ha).add (hV.smul hb)
  change ConvexOn ℝ univ (fun z => a*U z+b*V z+((a*K1+b*K2)/2)*qnorm2 z)
  convert! h using 1
  funext z
  change a*U z+b*V z+((a*K1+b*K2)/2)*qnorm2 z =
    a*(U z+(K1/2)*qnorm2 z)+b*(V z+(K2/2)*qnorm2 z)
  ring

theorem jet_quadratic_complement_convex {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : Point n ≃L[ℝ] E) (c : ℝ) (p : Point n) (l : Point n →L[ℝ] ℝ)
    (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB : ∀ x y, B x y=B y x)
    (sigma K : ℝ) :
    ∃ lam : ℝ, ConvexOn ℝ univ (fun x =>
      -peanoPolynomial c p l B sigma (e.symm x)-(K/2)*qnorm2 (e.symm x)+
        (lam/2)*‖x‖^2) := by
  let J := jointInnerBilin n
  let I : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.mkContinuous₂ (innerₗ E) 1 (by
    intro x y
    simpa using norm_inner_le_norm (𝕜 := ℝ) x y)
  have hI (x y : E) : I x y=inner ℝ x y := rfl
  have hJ (x : Point n) : J x x=qnorm2 x := by
    simp only [J,jointInnerBilin_apply,real_inner_self_eq_norm_sq,qnorm2]
    ring
  let D := B+(2*sigma+K) • J
  let lam : ℝ := ‖D‖*‖e.symm.toContinuousLinearMap‖^2+1
  let C := lam • I-D.bilinearComp e.symm.toContinuousLinearMap e.symm.toContinuousLinearMap
  have hSymD (x y : Point n) : D x y=D y x := by
    simp only [D,add_apply,smul_apply,smul_eq_mul,J]
    rw [hB x y,jointInnerBilin_symm x y]
  have hSymC (x y : E) : C x y=C y x := by
    simp only [C,sub_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hI]
    rw [real_inner_comm x y,hSymD]
  have hNonneg (x : E) : 0≤C x x := by
    have hDx : D (e.symm x) (e.symm x) ≤
        ‖D‖*‖e.symm.toContinuousLinearMap‖^2*‖x‖^2 := by
      calc
        _ ≤ ‖D (e.symm x) (e.symm x)‖ := le_abs_self _
        _ ≤ ‖D‖*‖e.symm x‖*‖e.symm x‖ := D.le_opNorm₂ _ _
        _ ≤ ‖D‖*(‖e.symm.toContinuousLinearMap‖*‖x‖)*
              (‖e.symm.toContinuousLinearMap‖*‖x‖) := by
          gcongr <;> exact e.symm.toContinuousLinearMap.le_opNorm x
        _ = _ := by ring
    change 0≤(lam • I-D.bilinearComp e.symm.toContinuousLinearMap e.symm.toContinuousLinearMap) x x
    simp only [sub_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.bilinearComp_apply,hI,
      real_inner_self_eq_norm_sq]
    dsimp only [lam]
    change D (e.symm.toContinuousLinearMap x) (e.symm.toContinuousLinearMap x) ≤ _ at hDx
    nlinarith [sq_nonneg ‖x‖]
  let d := -c+l p-(1/2 : ℝ)*B p p-sigma*J p p
  let lE := (-l+B p+(2*sigma) • J p).comp e.symm.toContinuousLinearMap
  have hConv := jet_convex_symmetric_quadratic C hSymC hNonneg d lE
  refine ⟨lam,?_⟩
  convert! hConv using 1
  funext x
  have hqx := hJ (e.symm x)
  have hqxp := hJ (e.symm x-p)
  dsimp only [peanoPolynomial,d,lE,C,D]
  rw [← hqx,← hqxp]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.bilinearComp_apply,map_sub,sub_apply,add_apply,smul_apply,
    neg_apply,smul_eq_mul,hI,real_inner_self_eq_norm_sq]
  rw [hB (e.symm x) p]
  have hJs := jointInnerBilin_symm (n := n) (e.symm x) p
  change J (e.symm x) p=J p (e.symm x) at hJs
  rw [hJs]
  ring

theorem jet_simultaneous_peano_contact
    {n : ℕ} {U V : Point n → ℝ} {K1 K2 a b : ℝ}
    (hU : jointSemiconvex K1 U) (hV : jointSemiconvex K2 V)
    (ha : 0<a) (hb : 0<b) (c : ℝ) (p : Point n) (l0 : Point n →L[ℝ] ℝ)
    (B0 : Point n →L[ℝ] Point n →L[ℝ] ℝ) (hB0 : ∀ v w, B0 v w=B0 w v)
    (sigma : ℝ) {r tau : ℝ} (hr : 0<r) (htau : 0<tau)
    (hgap : ∀ x ∈ Metric.sphere (abpEuclideanEquiv n p) r,
      peanoPolynomial c p l0 B0 sigma p-(a*U p+b*V p) <
      peanoPolynomial c p l0 B0 sigma ((abpEuclideanEquiv n).symm x)-
        (a*U ((abpEuclideanEquiv n).symm x)+b*V ((abpEuclideanEquiv n).symm x))) :
    ∃ (y : Point n) (ell l1 l2 : Point n →L[ℝ] ℝ)
      (B1 B2 : Point n →L[ℝ] Point n →L[ℝ] ℝ),
      dist (abpEuclideanEquiv n y) (abpEuclideanEquiv n p)<r ∧ ‖ell‖<tau ∧
      jointPeanoJet U y l1 B1 ∧ jointPeanoJet V y l2 B2 ∧
      IsLocalMax (fun z => a*U z+b*V z-peanoPolynomial c p l0 B0 sigma z+ell z) y := by
  let e := abpEuclideanEquiv n
  let K := a*K1+b*K2
  let W : Point n → ℝ := fun z => a*U z+b*V z
  let P := peanoPolynomial c p l0 B0 sigma
  let f := fun x => P (e.symm x)-W (e.symm x)
  have hW : jointSemiconvex K W := jet_semiconvex_weighted hU hV ha.le hb.le
  obtain ⟨lam,hComplement⟩ := jet_quadratic_complement_convex e c p l0 B0 hB0 sigma K
  have hPull : ConvexOn ℝ univ (fun x => W (e.symm x)+(K/2)*qnorm2 (e.symm x)) := by
    convert! hW.comp_linearMap e.symm.toLinearMap using 1
  have hSemi : ConvexOn ℝ univ (fun x => -f x+(lam/2)*‖x‖^2) := by
    convert! hPull.add hComplement using 1
    funext x
    change -(P (e.symm x)-W (e.symm x))+(lam/2)*‖x‖^2 =
      (W (e.symm x)+(K/2)*qnorm2 (e.symm x))+
        (-P (e.symm x)-(K/2)*qnorm2 (e.symm x)+(lam/2)*‖x‖^2)
    ring
  have hClosure : closure (Metric.ball (e p) r)=Metric.closedBall (e p) r :=
    closure_ball (e p) hr.ne'
  have hBoundary : ∀ x ∈ closure (Metric.ball (e p) r) \ Metric.ball (e p) r,
      f (e p)<f x := by
    intro x hx
    rw [hClosure] at hx
    have hsphere : x ∈ Metric.sphere (e p) r := by
      rw [Metric.mem_sphere]
      exact le_antisymm (Metric.mem_closedBall.mp hx.1) (not_lt.mp hx.2)
    simpa only [f,P,W,e,e.symm_apply_apply] using hgap x hsphere
  obtain ⟨delta0,hdelta0,hJensen⟩ := Yau.LeafProofs.jensen
    (Module.finrank ℝ (Point n)) f lam (e p) (2*r) (Metric.ball (e p) r)
    (by positivity) Metric.isOpen_ball (Metric.mem_ball_self hr)
    (by rw [hClosure]; exact isCompact_closedBall _ _)
    (by rw [hClosure]; exact Metric.closedBall_subset_ball (by linarith))
    (hSemi.subset (subset_univ _) (convex_ball _ _)) hBoundary
  let delta := min (delta0/2) (tau/(2*(1+‖e.toContinuousLinearMap‖)))
  have hdelta : 0<delta := lt_min (by positivity) (by positivity)
  have hdelta0le : delta≤delta0 := (min_le_left _ _).trans (by linarith)
  have hMass := hJensen delta hdelta hdelta0le
  let jetCombination_pointHaar : (volume : Measure (Point n)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let jetCombination_mappedHaar :
      (Measure.map e.symm (volume : Measure (EuclideanSpace ℝ
        (Fin (Module.finrank ℝ (Point n)))))).IsAddHaarMeasure :=
    e.symm.isAddHaarMeasure_map volume
  have hAC : Measure.map e.symm volume ≪ (volume : Measure (Point n)) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hAE : ∀ᵐ x ∂volume,
      (∃ l B, jointPeanoJet U (e.symm x) l B) ∧
        (∃ l B, jointPeanoJet V (e.symm x) l B) := by
    have h := ((jointSemiconvex_ae_peano hU).and (jointSemiconvex_ae_peano hV)).filter_mono hAC.ae_le
    exact ae_of_ae_map e.symm.continuous.measurable.aemeasurable h
  obtain ⟨x,hContact,hJets⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (ne_of_gt hMass) (ae_restrict_of_ae hAE)
  obtain ⟨hx,cSlope,hcSlope,hSlopeMax⟩ := hContact
  obtain ⟨⟨l1,B1,h1⟩,⟨l2,B2,h2⟩⟩ := hJets
  let ell := (innerSL ℝ cSlope).comp e.toContinuousLinearMap
  have hEll : ‖ell‖<tau := by
    have hNorm : ‖ell‖≤delta*‖e.toContinuousLinearMap‖ := by
      calc
        _ ≤ ‖innerSL ℝ cSlope‖*‖e.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖cSlope‖*‖e.toContinuousLinearMap‖ := by rw [innerSL_apply_norm]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcSlope (norm_nonneg _)
    have hDeltaBound : delta≤tau/(2*(1+‖e.toContinuousLinearMap‖)) := min_le_right _ _
    have hMul := (le_div_iff₀ (by positivity : 0<2*(1+‖e.toContinuousLinearMap‖))).mp hDeltaBound
    nlinarith [norm_nonneg e.toContinuousLinearMap]
  refine ⟨e.symm x,ell,l1,l2,B1,B2,?_,hEll,h1,h2,?_⟩
  · change dist (e (e.symm x)) (e p)<r
    simpa only [e.apply_symm_apply] using Metric.mem_ball.mp hx
  · have hNhd : {z : Point n | e z ∈ Metric.ball (e p) r} ∈ 𝓝 (e.symm x) := by
      exact e.continuous.continuousAt.preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (by simpa only [e.apply_symm_apply] using hx))
    filter_upwards [hNhd] with z hz
    have h := hSlopeMax (e z) (subset_closure hz)
    simp only [f,P,W,e.symm_apply_apply] at h
    change W z-P z+ell z≤W (e.symm x)-P (e.symm x)+ell (e.symm x)
    have hez : ell z=inner ℝ cSlope (e z) := rfl
    have hex : ell (e.symm x)=inner ℝ cSlope x := by
      change inner ℝ cSlope (e (e.symm x))=inner ℝ cSlope x
      rw [e.apply_symm_apply]
    rw [hez,hex]
    dsimp only [W,P]
    linarith

end Yau.LeafProofs.L05Aux
