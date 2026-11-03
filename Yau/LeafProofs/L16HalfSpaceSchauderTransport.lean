import Yau.LeafProofs.L16HalfSpaceC2Extension
import Yau.LeafProofs.L16

/-! Quantitative transport by the literal second order normal reflection.
The highest jets are derived on the negative face from the actual chain rules;
the closed-face Hölder estimates then glue through a spatial segment point. -/

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

/-- A segment joining opposite open faces meets the seam without increasing either
spatial distance to its endpoints. -/
theorem halfSpace_seam_point {n : ℕ} (e x y : Space n)
    (hx : 0 ≤ inner ℝ e x) (hy : inner ℝ e y < 0) :
    ∃ z : Space n, inner ℝ e z = 0 ∧ ‖x-z‖ ≤ ‖x-y‖ ∧ ‖z-y‖ ≤ ‖x-y‖ := by
  let a : ℝ := inner ℝ e x / (inner ℝ e x-inner ℝ e y)
  have hd : 0 < inner ℝ e x-inner ℝ e y := by linarith
  have ha0 : 0 ≤ a := div_nonneg hx hd.le
  have ha1 : a ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨x-a • (x-y),?_,?_,?_⟩
  · simp only [inner_sub_right,inner_smul_right]
    dsimp only [a]
    rw [div_mul_cancel₀ _ (ne_of_gt hd),sub_self]
  · have hEq : x-(x-a • (x-y)) = a • (x-y) := by module
    rw [hEq,norm_smul,Real.norm_eq_abs,abs_of_nonneg ha0]
    exact mul_le_of_le_one_left (norm_nonneg _) ha1
  · have hEq : x-a • (x-y)-y = (1-a) • (x-y) := by module
    rw [hEq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 1-a)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)

/-- Hölder estimates on two actual closed faces glue through their common seam.
The constant is independent of the slab and the target normed group. -/
theorem holderBound_closed_halfspaces {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α A B : ℝ} {I : Set ℝ} {e : Space n} {f : Point n → V}
    (hα : 0 ≤ α)
    (hp : HolderBound α ({x : Space n | 0 ≤ inner ℝ e x} ×ˢ I) f A)
    (hn : HolderBound α ({x : Space n | inner ℝ e x ≤ 0} ×ˢ I) f B) :
    HolderBound α (Set.univ ×ˢ I) f (A+B) := by
  have hW (p q : Point n) : 0 ≤ holderWeight α p q := by
    dsimp only [holderWeight]; positivity
  have hCross {p q : Point n} (hpx : 0 ≤ inner ℝ e p.1)
      (hqx : inner ℝ e q.1 < 0) (hpt : p.2 ∈ I) (hqt : q.2 ∈ I) :
      ‖f p-f q‖ ≤ (A+B)*holderWeight α p q := by
    obtain ⟨z,hz,hpz,hzq⟩ := halfSpace_seam_point e p.1 q.1 hpx hqx
    have hzp : (z,p.2) ∈ {x : Space n | 0 ≤ inner ℝ e x} ×ˢ I := ⟨by simp [hz],hpt⟩
    have hzn : (z,p.2) ∈ {x : Space n | inner ℝ e x ≤ 0} ×ˢ I := ⟨by simp [hz],hpt⟩
    have hw1 : holderWeight α p (z,p.2) ≤ holderWeight α p q := by
      exact add_le_add (Real.rpow_le_rpow (norm_nonneg _) hpz hα)
        (Real.rpow_le_rpow (abs_nonneg _) (by simp) (by linarith : 0 ≤ α/2))
    have hw2 : holderWeight α (z,p.2) q ≤ holderWeight α p q := by
      exact add_le_add (Real.rpow_le_rpow (norm_nonneg _) hzq hα) le_rfl
    calc
      ‖f p-f q‖ ≤ ‖f p-f (z,p.2)‖+‖f (z,p.2)-f q‖ := by simpa only [dist_eq_norm] using dist_triangle (f p) (f (z,p.2)) (f q)
      _ ≤ A*holderWeight α p (z,p.2)+B*holderWeight α (z,p.2) q :=
        add_le_add (hp.2.2 p ⟨hpx,hpt⟩ _ hzp) (hn.2.2 _ hzn q ⟨hqx.le,hqt⟩)
      _ ≤ A*holderWeight α p q+B*holderWeight α p q :=
        add_le_add (mul_le_mul_of_nonneg_left hw1 hp.1) (mul_le_mul_of_nonneg_left hw2 hn.1)
      _ = _ := by ring
  refine ⟨add_nonneg hp.1 hn.1,?_,?_⟩
  · intro p hpt
    by_cases hx : 0 ≤ inner ℝ e p.1
    · exact (hp.2.1 p ⟨hx,hpt.2⟩).trans (le_add_of_nonneg_right hn.1)
    · exact (hn.2.1 p ⟨(lt_of_not_ge hx).le,hpt.2⟩).trans (le_add_of_nonneg_left hp.1)
  · intro p hpt q hqt
    by_cases hx : 0 ≤ inner ℝ e p.1 <;> by_cases hy : 0 ≤ inner ℝ e q.1
    · exact (hp.2.2 p ⟨hx,hpt.2⟩ q ⟨hy,hqt.2⟩).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hn.1) (hW p q))
    · exact hCross hx (lt_of_not_ge hy) hpt.2 hqt.2
    · have hc := hCross hy (lt_of_not_ge hx) hqt.2 hpt.2
      simpa only [norm_sub_rev,holderWeight,abs_sub_comm] using hc
    · exact (hn.2.2 p ⟨(lt_of_not_ge hx).le,hpt.2⟩ q ⟨(lt_of_not_ge hy).le,hqt.2⟩).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hp.1) (hW p q))

/-- A spatial linear sampling of norm at most five costs at most five in the
parabolic Hölder bound, including its supremum term. -/
theorem holderBound_spatial_sample_five {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α K : ℝ} {S H : Set (Space n)} {I : Set ℝ} {f : Point n → V}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (L : Space n →L[ℝ] Space n)
    (hL : ‖L‖ ≤ 5) (hMap : Set.MapsTo L S H)
    (hf : HolderBound α (H ×ˢ I) f K) :
    HolderBound α (S ×ˢ I) (fun p => f (L p.1,p.2)) (5*K) := by
  have hMem (p : Point n) (hp : p ∈ S ×ˢ I) : (L p.1,p.2) ∈ H ×ˢ I :=
    ⟨hMap hp.1,hp.2⟩
  have hPow : (5:ℝ)^α ≤ 5 := Real.rpow_le_self_of_one_le (by norm_num) hα1
  refine ⟨mul_nonneg (by norm_num) hf.1,fun p hp => (hf.2.1 _ (hMem p hp)).trans (by linarith [hf.1]),?_⟩
  intro p hp q hq
  have hsp : ‖L p.1-L q.1‖^α ≤ 5*‖p.1-q.1‖^α := by
    rw [← map_sub]
    calc
      _ ≤ (5*‖p.1-q.1‖)^α := Real.rpow_le_rpow (norm_nonneg _)
        ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))) hα
      _ = (5:ℝ)^α*‖p.1-q.1‖^α := Real.mul_rpow (by norm_num) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hPow (Real.rpow_nonneg (norm_nonneg _) _)
  have hw : holderWeight α (L p.1,p.2) (L q.1,q.2) ≤ 5*holderWeight α p q := by
    dsimp only [holderWeight,Prod.fst,Prod.snd]
    nlinarith [Real.rpow_nonneg (abs_nonneg (p.2-q.2)) (α/2)]
  exact (hf.2.2 _ (hMem p hp) _ (hMem q hq)).trans
    ((mul_le_mul_of_nonneg_left hw hf.1).trans_eq (by ring))

private def transportGradientMap {n : ℕ} (L : Space n →L[ℝ] Space n) :
    (Space n →L[ℝ] ℝ) →L[ℝ] Space n →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (Space n) (Space n) ℝ).flip L

private def transportHessianMap {n : ℕ} (L : Space n →L[ℝ] Space n) :
    (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] ℝ where
  toFun A := (transportGradientMap L).comp (A.comp L)
  map_add' A B := by ext x y; simp [transportGradientMap]
  map_smul' c A := by ext x y; simp [transportGradientMap]
  cont := (continuous_id.clm_comp_const L).const_clm_comp (transportGradientMap L)

private theorem transportHessianMap_apply {n : ℕ} (L : Space n →L[ℝ] Space n)
    (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    transportHessianMap L A = (transportGradientMap L).comp (A.comp L) := rfl

private theorem transportGradientMap_bound {n : ℕ} {L : Space n →L[ℝ] Space n}
    (hL : ‖L‖ ≤ 5) (A : Space n →L[ℝ] ℝ) : ‖transportGradientMap L A‖ ≤ 5*‖A‖ := by
  exact (A.opNorm_comp_le L).trans
    ((mul_le_mul_of_nonneg_left hL (norm_nonneg A)).trans_eq (by ring))

private theorem transportHessianMap_bound {n : ℕ} {L : Space n →L[ℝ] Space n}
    (hL : ‖L‖ ≤ 5) (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    ‖transportHessianMap L A‖ ≤ 25*‖A‖ := by
  have hP : ‖transportGradientMap L‖ ≤ 5 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (transportGradientMap_bound hL)
  have hA : ‖A.comp L‖ ≤ 5*‖A‖ := (A.opNorm_comp_le L).trans
    ((mul_le_mul_of_nonneg_left hL (norm_nonneg A)).trans_eq (by ring))
  change ‖(transportGradientMap L).comp (A.comp L)‖ ≤ _
  calc
    _ ≤ ‖transportGradientMap L‖*‖A.comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 5*‖A.comp L‖ := mul_le_mul_of_nonneg_right hP (by positivity)
    _ ≤ 5*(5*‖A‖) := mul_le_mul_of_nonneg_left hA (by norm_num)
    _ = _ := by ring

/-- A uniform bound for all three normal sampling maps. -/
theorem normalSampleL_norm_le_five {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {j : ℝ} (hj : 0 ≤ j) (hj3 : j ≤ 3) : ‖normalSampleL e j‖ ≤ 5 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [normalSampleL_apply,normalSample]
  calc
    _ ≤ ‖x‖+‖((j+1)*inner ℝ e x) • e‖ := norm_sub_le _ _
    _ = ‖x‖+(j+1)*|inner ℝ e x| := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by linarith : 0 ≤ j+1),he,mul_one]
    _ ≤ ‖x‖+(j+1)*‖x‖ := by
      gcongr
      simpa only [he,one_mul] using abs_real_inner_le_norm e x
    _ ≤ 5*‖x‖ := by nlinarith [norm_nonneg x]

private theorem transport_three_norm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a b c : V) : ‖(6:ℝ) • a-(8:ℝ) • b+(3:ℝ) • c‖ ≤ 6*‖a‖+8*‖b‖+3*‖c‖ := by
  calc
    _ ≤ ‖(6:ℝ) • a-(8:ℝ) • b‖+‖(3:ℝ) • c‖ := norm_add_le _ _
    _ ≤ (‖(6:ℝ) • a‖+‖(8:ℝ) • b‖)+‖(3:ℝ) • c‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ = _ := by norm_num [norm_smul]

private theorem holderBound_transport_three {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {α A B C : ℝ} {Q : Set (Point n)} {f g h : Point n → V}
    (hf : HolderBound α Q f A) (hg : HolderBound α Q g B) (hh : HolderBound α Q h C) :
    HolderBound α Q (fun p => (6:ℝ) • f p-(8:ℝ) • g p+(3:ℝ) • h p) (6*A+8*B+3*C) := by
  refine ⟨by linarith [hf.1,hg.1,hh.1],?_,?_⟩
  · intro p hp
    exact (transport_three_norm_le _ _ _).trans (by
      linarith [hf.2.1 p hp,hg.2.1 p hp,hh.2.1 p hp])
  · intro p hp q hq
    have heq : ((6:ℝ) • f p-(8:ℝ) • g p+(3:ℝ) • h p)-((6:ℝ) • f q-(8:ℝ) • g q+(3:ℝ) • h q) =
        (6:ℝ) • (f p-f q)-(8:ℝ) • (g p-g q)+(3:ℝ) • (h p-h q) := by module
    dsimp only
    rw [heq]
    exact (transport_three_norm_le _ _ _).trans (by
      linarith [hf.2.2 p hp q hq,hg.2.2 p hp q hq,hh.2.2 p hp q hq])

private def transportValue {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (e : Space n) (f : Point n → V) (p : Point n) : V :=
  (6:ℝ) • f (normalSample e 1 p.1,p.2)-(8:ℝ) • f (normalSample e 2 p.1,p.2)+
    (3:ℝ) • f (normalSample e 3 p.1,p.2)

private def transportD {n : ℕ} (e : Space n) (J : Point n → Space n →L[ℝ] ℝ)
    (p : Point n) : Space n →L[ℝ] ℝ :=
  (6:ℝ) • transportGradientMap (normalSampleL e 1) (J (normalSample e 1 p.1,p.2))-
    (8:ℝ) • transportGradientMap (normalSampleL e 2) (J (normalSample e 2 p.1,p.2))+
    (3:ℝ) • transportGradientMap (normalSampleL e 3) (J (normalSample e 3 p.1,p.2))

private def transportDD {n : ℕ} (e : Space n)
    (J : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (p : Point n) : Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  (6:ℝ) • transportHessianMap (normalSampleL e 1) (J (normalSample e 1 p.1,p.2))-
    (8:ℝ) • transportHessianMap (normalSampleL e 2) (J (normalSample e 2 p.1,p.2))+
    (3:ℝ) • transportHessianMap (normalSampleL e 3) (J (normalSample e 3 p.1,p.2))

private theorem transport_sample_positive {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {x : Space n} (hx : inner ℝ e x < 0) {j : ℝ} (hj : 0 < j) :
    0 < inner ℝ e (normalSample e j x) := by
  rw [normalSample_normal he]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos hj) hx

private theorem transportValue_hasFDerivAt {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T : ℝ} {v : Point n → ℝ} {J : Point n → Space n →L[ℝ] ℝ}
    (hD : ∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
      HasFDerivAt (fun x => v (x,p.2)) (J p) p.1)
    {p : Point n} (hp : inner ℝ e p.1 < 0) (hpt : p.2 ∈ Set.Icc 0 T) :
    HasFDerivAt (fun x => transportValue e v (x,p.2)) (transportD e J p) p.1 := by
  have h (j : ℝ) (hj : 0 < j) :
      HasFDerivAt (fun x => v (normalSample e j x,p.2))
        (transportGradientMap (normalSampleL e j) (J (normalSample e j p.1,p.2))) p.1 := by
    have h0 : HasFDerivAt (fun x => v (x,p.2)) (J (normalSample e j p.1,p.2))
        (normalSampleL e j p.1) := by
      simpa only [normalSampleL_apply] using
        hD (normalSample e j p.1,p.2) ⟨transport_sample_positive he hp hj,hpt⟩
    simpa only [Function.comp_def,normalSampleL_apply,transportGradientMap,
      ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply] using
      h0.comp p.1 (normalSampleL e j).hasFDerivAt
  exact ((h 1 (by norm_num)).const_smul (6:ℝ) |>.sub
    ((h 2 (by norm_num)).const_smul (8:ℝ))).add ((h 3 (by norm_num)).const_smul (3:ℝ))

private theorem transportD_hasFDerivAt {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T : ℝ} {J : Point n → Space n →L[ℝ] ℝ}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hD : ∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
      HasFDerivAt (fun x => J (x,p.2)) (H p) p.1)
    {p : Point n} (hp : inner ℝ e p.1 < 0) (hpt : p.2 ∈ Set.Icc 0 T) :
    HasFDerivAt (fun x => transportD e J (x,p.2)) (transportDD e H p) p.1 := by
  have h (j : ℝ) (hj : 0 < j) :
      HasFDerivAt (fun x => transportGradientMap (normalSampleL e j)
        (J (normalSample e j x,p.2)))
        (transportHessianMap (normalSampleL e j) (H (normalSample e j p.1,p.2))) p.1 := by
    have h0 : HasFDerivAt (fun x => J (x,p.2)) (H (normalSample e j p.1,p.2))
        (normalSampleL e j p.1) := by
      simpa only [normalSampleL_apply] using
        hD (normalSample e j p.1,p.2) ⟨transport_sample_positive he hp hj,hpt⟩
    simpa only [Function.comp_def,normalSampleL_apply,transportHessianMap_apply] using
      (transportGradientMap (normalSampleL e j)).hasFDerivAt.comp p.1
        (h0.comp p.1 (normalSampleL e j).hasFDerivAt)
  exact ((h 1 (by norm_num)).const_smul (6:ℝ) |>.sub
    ((h 2 (by norm_num)).const_smul (8:ℝ))).add ((h 3 (by norm_num)).const_smul (3:ℝ))

private theorem transportValue_boundary {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (e : Space n) (f : Point n → V)
    {p : Point n} (hp : inner ℝ e p.1 = 0) : f p = transportValue e f p := by
  simp only [transportValue,normalSample_boundary e _ hp,Prod.eta]
  module

private theorem transportD_boundary {n : ℕ} (e : Space n) (J : Point n → Space n →L[ℝ] ℝ)
    {p : Point n} (hp : inner ℝ e p.1 = 0) : J p = transportD e J p := by
  ext z
  simp only [transportD,normalSample_boundary e _ hp,Prod.eta]
  simp only [transportGradientMap,add_apply,sub_apply,smul_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
    normalSampleL_apply,normalSample,map_sub,map_smul]
  module

private theorem transportDD_boundary {n : ℕ} (e : Space n)
    (J : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ)
    {p : Point n} (hp : inner ℝ e p.1 = 0) : J p = transportDD e J p := by
  ext z w
  simp only [transportDD,normalSample_boundary e _ hp,Prod.eta]
  simp only [transportHessianMap_apply,transportGradientMap,add_apply,sub_apply,smul_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
    normalSampleL_apply,normalSample,map_sub,map_smul,smul_eq_mul]
  ring

private theorem spatialD_transport_neg {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T : ℝ} {v : Point n → ℝ} {J : Point n → Space n →L[ℝ] ℝ}
    (hD : ∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
      HasFDerivAt (fun x => v (x,p.2)) (J p) p.1)
    {p : Point n} (hp : inner ℝ e p.1 < 0) (hpt : p.2 ∈ Set.Icc 0 T) :
    spatialD (halfSpaceSecondOrderExtension e v) p = transportD e J p := by
  have hEq : (fun x => halfSpaceSecondOrderExtension e v (x,p.2)) =ᶠ[𝓝 p.1]
      (fun x => transportValue e v (x,p.2)) := by
    filter_upwards [(isOpen_lt (innerSL ℝ e).continuous continuous_const).mem_nhds hp] with x hx
    change inner ℝ e x < 0 at hx
    simp only [halfSpaceSecondOrderExtension,ite_eq_right (not_le_of_gt hx),
      transportValue,smul_eq_mul]
  exact ((transportValue_hasFDerivAt he hD hp hpt).congr_of_eventuallyEq hEq).fderiv

private theorem spatialDD_transport_neg {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T : ℝ} {v : Point n → ℝ} {J : Point n → Space n →L[ℝ] ℝ}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hD : ∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
      HasFDerivAt (fun x => v (x,p.2)) (J p) p.1)
    (hDD : ∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
      HasFDerivAt (fun x => J (x,p.2)) (H p) p.1)
    {p : Point n} (hp : inner ℝ e p.1 < 0) (hpt : p.2 ∈ Set.Icc 0 T) :
    spatialDD (halfSpaceSecondOrderExtension e v) p = transportDD e H p := by
  have hEq : (fun x => fderiv ℝ (fun y => halfSpaceSecondOrderExtension e v (y,p.2)) x)
      =ᶠ[𝓝 p.1] (fun x => transportD e J (x,p.2)) := by
    filter_upwards [(isOpen_lt (innerSL ℝ e).continuous continuous_const).mem_nhds hp] with x hx
    exact spatialD_transport_neg he hD (p := (x,p.2)) hx hpt
  exact ((transportD_hasFDerivAt he hDD hp hpt).congr_of_eventuallyEq hEq).fderiv

private theorem timeD_transport_neg {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T : ℝ} (hT : 0 < T) {v J : Point n → ℝ}
    (ht : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      HasDerivWithinAt (fun t => v (p.1,t)) (J p) (Set.Icc 0 T) p.2)
    {p : Point n} (hp : inner ℝ e p.1 < 0) (hpt : p.2 ∈ Set.Icc 0 T) :
    timeD (cylinder Set.univ 0 T) (halfSpaceSecondOrderExtension e v) p =
      transportValue e J p := by
  have hs (j : ℝ) (hj : 0 < j) :
      HasDerivWithinAt (fun t => v (normalSample e j p.1,t))
        (J (normalSample e j p.1,p.2)) (Set.Icc 0 T) p.2 :=
    ht (normalSample e j p.1,p.2) ⟨(transport_sample_positive he hp hj).le,hpt⟩
  have hneg := ((hs 1 (by norm_num)).const_smul (6:ℝ) |>.sub
    ((hs 2 (by norm_num)).const_smul (8:ℝ))).add ((hs 3 (by norm_num)).const_smul (3:ℝ))
  have hU : HasDerivWithinAt (fun t => halfSpaceSecondOrderExtension e v (p.1,t))
      (transportValue e J p) (Set.Icc 0 T) p.2 := by
    apply hneg.congr <;> intros <;>
      simp only [halfSpaceSecondOrderExtension,ite_eq_right (not_le_of_gt hp),Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  unfold timeD
  have hFiber : {t | (p.1,t) ∈ cylinder (Set.univ : Set (Space n)) 0 T} = Set.Icc 0 T := by
    ext t; simp [Yau.Parabolic.cylinder]
  rw [hFiber]
  exact hU.derivWithin (uniqueDiffOn_Icc hT p.2 hpt)

private theorem transport_sample_mem {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T : ℝ} {p : Point n} (hp : inner ℝ e p.1 ≤ 0) (hpt : p.2 ∈ Set.Icc 0 T)
    {j : ℝ} (hj : 0 ≤ j) :
    (normalSample e j p.1,p.2) ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T := by
  refine ⟨?_,hpt⟩
  change 0 ≤ inner ℝ e (normalSample e j p.1)
  rw [normalSample_normal he]
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hj) hp

private theorem holderBound_transport_sample {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {e : Space n} (he : ‖e‖ = 1) {α K T : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {f : Point n → V}
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f K)
    (j : ℝ) (hj : 0 ≤ j) (hj3 : j ≤ 3) :
    HolderBound α (cylinder {x | inner ℝ e x ≤ 0} 0 T)
      (fun p => f (normalSample e j p.1,p.2)) (5*K) := by
  have hm : Set.MapsTo (normalSampleL e j) {x : Space n | inner ℝ e x ≤ 0}
      {x | 0 ≤ inner ℝ e x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq,normalSampleL_apply,normalSample_normal he]
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hj) hx
  simpa only [normalSampleL_apply,Yau.Parabolic.cylinder] using holderBound_spatial_sample_five hα hα1
    (normalSampleL e j) (normalSampleL_norm_le_five he hj hj3) hm hf

private theorem holderBound_transportValue {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {e : Space n} (he : ‖e‖ = 1)
    {α K T : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {f : Point n → V}
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f K) :
    HolderBound α (cylinder {x | inner ℝ e x ≤ 0} 0 T) (transportValue e f) (85*K) := by
  have h := holderBound_transport_three
    (holderBound_transport_sample he hα hα1 hf 1 (by norm_num) (by norm_num))
    (holderBound_transport_sample he hα hα1 hf 2 (by norm_num) (by norm_num))
    (holderBound_transport_sample he hα hα1 hf 3 (by norm_num) (by norm_num))
  convert h using 1 <;> first | rfl | ring

private theorem holderBound_transportDD {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {α K T : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {J : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) J K) :
    HolderBound α (cylinder {x | inner ℝ e x ≤ 0} 0 T) (transportDD e J) (2125*K) := by
  have hs (j : ℝ) (hj : 0 ≤ j) (hj3 : j ≤ 3) :
      HolderBound α (cylinder {x | inner ℝ e x ≤ 0} 0 T)
        (fun p => transportHessianMap (normalSampleL e j) (J (normalSample e j p.1,p.2)))
        (25*(5*K)) := by
    have hF := holderBound_transport_sample he hα hα1 hf j hj hj3
    have hL := normalSampleL_norm_le_five he hj hj3
    refine ⟨mul_nonneg (by norm_num) hF.1,?_,?_⟩
    · intro p hp
      exact (transportHessianMap_bound hL _).trans
        (mul_le_mul_of_nonneg_left (hF.2.1 p hp) (by norm_num))
    · intro p hp q hq
      change ‖transportHessianMap (normalSampleL e j) (J (normalSample e j p.1,p.2))-
        transportHessianMap (normalSampleL e j) (J (normalSample e j q.1,q.2))‖ ≤ _
      have heq : transportHessianMap (normalSampleL e j) (J (normalSample e j p.1,p.2))-
          transportHessianMap (normalSampleL e j) (J (normalSample e j q.1,q.2)) =
          transportHessianMap (normalSampleL e j)
            (J (normalSample e j p.1,p.2)-J (normalSample e j q.1,q.2)) := by
        ext x y; rfl
      rw [heq]
      exact (transportHessianMap_bound hL _).trans
        ((mul_le_mul_of_nonneg_left (hF.2.2 p hp q hq) (by norm_num : (0:ℝ) ≤ 25)).trans_eq (by ring))

  have h := holderBound_transport_three (hs 1 (by norm_num) (by norm_num))
    (hs 2 (by norm_num) (by norm_num)) (hs 3 (by norm_num) (by norm_num))
  convert h using 1 <;> first | rfl | ring

private theorem transportValue_sup {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {e : Space n} (he : ‖e‖ = 1) {K T : ℝ} {f : Point n → V}
    (hf : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, ‖f p‖ ≤ K)
    {p : Point n} (hp : inner ℝ e p.1 ≤ 0) (hpt : p.2 ∈ Set.Icc 0 T) :
    ‖transportValue e f p‖ ≤ 17*K := by
  have h1 := hf _ (transport_sample_mem he hp hpt (by norm_num : (0:ℝ) ≤ 1))
  have h2 := hf _ (transport_sample_mem he hp hpt (by norm_num : (0:ℝ) ≤ 2))
  have h3 := hf _ (transport_sample_mem he hp hpt (by norm_num : (0:ℝ) ≤ 3))
  exact (transport_three_norm_le _ _ _).trans (by linarith)

private theorem transportD_sup {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {K T : ℝ} {J : Point n → Space n →L[ℝ] ℝ}
    (hf : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, ‖J p‖ ≤ K)
    {p : Point n} (hp : inner ℝ e p.1 ≤ 0) (hpt : p.2 ∈ Set.Icc 0 T) :
    ‖transportD e J p‖ ≤ 85*K := by
  have hs (j : ℝ) (hj : 0 ≤ j) (hj3 : j ≤ 3) :
      ‖transportGradientMap (normalSampleL e j) (J (normalSample e j p.1,p.2))‖ ≤ 5*K :=
    (transportGradientMap_bound (normalSampleL_norm_le_five he hj hj3) _).trans
      (mul_le_mul_of_nonneg_left (hf _ (transport_sample_mem he hp hpt hj)) (by norm_num))
  exact (transport_three_norm_le _ _ _).trans (by
    linarith [hs 1 (by norm_num) (by norm_num),hs 2 (by norm_num) (by norm_num),hs 3 (by norm_num) (by norm_num)])

/-- The literal three-reflection extension transports genuine one-sided parabolic
Schauder bounds to the whole slab. The universal constant precedes all geometric,
time, function, jet and budget data. No Hölder bound on the lower jets is needed. -/
theorem halfSpaceSecondOrderExtension_schauder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n) (T : ℝ) (v : Point n → ℝ)
      (J₁ : Point n → Space n →L[ℝ] ℝ)
      (J₂ : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ) (Jt : Point n → ℝ) (K : ℝ),
      ‖e‖ = 1 → 0 < T →
      ContinuousOn v (cylinder {x | 0 ≤ inner ℝ e x} 0 T) →
      ContinuousOn J₁ (cylinder {x | 0 ≤ inner ℝ e x} 0 T) →
      ContinuousOn J₂ (cylinder {x | 0 ≤ inner ℝ e x} 0 T) →
      ContinuousOn Jt (cylinder {x | 0 ≤ inner ℝ e x} 0 T) →
      (∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
        HasFDerivAt (fun x => v (x,p.2)) (J₁ p) p.1) →
      (∀ p ∈ cylinder {x | 0 < inner ℝ e x} 0 T,
        HasFDerivAt (fun x => J₁ (x,p.2)) (J₂ p) p.1) →
      (∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
        HasDerivWithinAt (fun t => v (p.1,t)) (Jt p) (Set.Icc 0 T) p.2) →
      0 ≤ K →
      (∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, |v p| ≤ K ∧ ‖J₁ p‖ ≤ K) →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) J₂ K →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) Jt K →
      SchauderBound α (cylinder Set.univ 0 T) (halfSpaceSecondOrderExtension e v) (C*K) := by
  refine ⟨10000,by norm_num,?_⟩
  intro e T v J₁ J₂ Jt K he hT hv hJ₁ hJ₂ hJt hD hDD ht hK hLow hHigh hTime
  let U := halfSpaceSecondOrderExtension e v
  obtain ⟨hC2,hV,hDp,hDDp,hTp⟩ :=
    halfSpaceSecondOrderExtension_jets he hT v J₁ J₂ Jt hv hJ₁ hJ₂ hJt hD hDD ht
  have hDn : Set.EqOn (spatialD U) (transportD e J₁)
      (cylinder {x | inner ℝ e x ≤ 0} 0 T) := by
    intro p hp
    by_cases hx : inner ℝ e p.1 < 0
    · exact spatialD_transport_neg he hD hx hp.2
    · have hz : inner ℝ e p.1 = 0 := le_antisymm hp.1 (le_of_not_gt hx)
      exact (hDp ⟨by simp [hz],hp.2⟩).trans (transportD_boundary e J₁ hz)
  have hDDn : Set.EqOn (spatialDD U) (transportDD e J₂)
      (cylinder {x | inner ℝ e x ≤ 0} 0 T) := by
    intro p hp
    by_cases hx : inner ℝ e p.1 < 0
    · exact spatialDD_transport_neg he hD hDD hx hp.2
    · have hz : inner ℝ e p.1 = 0 := le_antisymm hp.1 (le_of_not_gt hx)
      exact (hDDp ⟨by simp [hz],hp.2⟩).trans (transportDD_boundary e J₂ hz)
  have hTn : Set.EqOn (timeD (cylinder Set.univ 0 T) U) (transportValue e Jt)
      (cylinder {x | inner ℝ e x ≤ 0} 0 T) := by
    intro p hp
    by_cases hx : inner ℝ e p.1 < 0
    · exact timeD_transport_neg he hT ht hx hp.2
    · have hz : inner ℝ e p.1 = 0 := le_antisymm hp.1 (le_of_not_gt hx)
      exact (hTp ⟨by simp [hz],hp.2⟩).trans (transportValue_boundary e Jt hz)
  have hHP : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (spatialDD U) K :=
    holderBound_congr_on hHigh (fun p hp => (hDDp hp).symm)
  have hHN : HolderBound α (cylinder {x | inner ℝ e x ≤ 0} 0 T) (spatialDD U) (2125*K) :=
    holderBound_congr_on (holderBound_transportDD he hα.le hα1.le hHigh) (fun p hp => (hDDn hp).symm)
  have hTP : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
      (timeD (cylinder Set.univ 0 T) U) K :=
    holderBound_congr_on hTime (fun p hp => (hTp hp).symm)
  have hTN : HolderBound α (cylinder {x | inner ℝ e x ≤ 0} 0 T)
      (timeD (cylinder Set.univ 0 T) U) (85*K) :=
    holderBound_congr_on (holderBound_transportValue he hα.le hα1.le hTime) (fun p hp => (hTn hp).symm)
  have hHWhole : HolderBound α (cylinder Set.univ 0 T) (spatialDD U) (K+2125*K) :=
    holderBound_closed_halfspaces hα.le hHP hHN
  have hTWhole : HolderBound α (cylinder Set.univ 0 T)
      (timeD (cylinder Set.univ 0 T) U) (K+85*K) :=
    holderBound_closed_halfspaces hα.le hTP hTN
  refine ⟨hC2,mul_nonneg (by norm_num) hK,?_,
    holderBound_mono_const hHWhole (by nlinarith),holderBound_mono_const hTWhole (by nlinarith)⟩
  intro p hp
  by_cases hx : 0 ≤ inner ℝ e p.1
  · obtain ⟨h0,h1⟩ := hLow p ⟨hx,hp.2⟩
    rw [hV ⟨hx,hp.2⟩,hDp ⟨hx,hp.2⟩]
    exact ⟨h0.trans (by nlinarith),h1.trans (by nlinarith)⟩
  · have hn : inner ℝ e p.1 ≤ 0 := (lt_of_not_ge hx).le
    have h0 : |transportValue e v p| ≤ 17*K := by
      simpa only [Real.norm_eq_abs] using transportValue_sup (f := v) (K := K) he
        (fun q hq => by simpa only [Real.norm_eq_abs] using (hLow q hq).1) hn hp.2
    have h1 := transportD_sup he (fun q hq => (hLow q hq).2) hn hp.2
    have hU : U p = transportValue e v p := by
      simp only [U,halfSpaceSecondOrderExtension,ite_eq_right hx,transportValue,smul_eq_mul]
    change |U p| ≤ 10000*K ∧ ‖spatialD U p‖ ≤ 10000*K
    rw [hU,hDn ⟨hn,hp.2⟩]
    exact ⟨h0.trans (by nlinarith),h1.trans (by nlinarith)⟩

private theorem transportDD_sup {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {K T : ℝ} {J : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hf : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, ‖J p‖ ≤ K)
    {p : Point n} (hp : inner ℝ e p.1 ≤ 0) (hpt : p.2 ∈ Set.Icc 0 T) :
    ‖transportDD e J p‖ ≤ 425*K := by
  have hs (j : ℝ) (hj : 0 ≤ j) (hj3 : j ≤ 3) :
      ‖transportHessianMap (normalSampleL e j) (J (normalSample e j p.1,p.2))‖ ≤ 25*K :=
    (transportHessianMap_bound (normalSampleL_norm_le_five he hj hj3) _).trans
      (mul_le_mul_of_nonneg_left (hf _ (transport_sample_mem he hp hpt hj)) (by norm_num))
  have h := transport_three_norm_le
    (transportHessianMap (normalSampleL e 1) (J (normalSample e 1 p.1,p.2)))
    (transportHessianMap (normalSampleL e 2) (J (normalSample e 2 p.1,p.2)))
    (transportHessianMap (normalSampleL e 3) (J (normalSample e 3 p.1,p.2)))
  exact h.trans (by
    linarith [hs 1 (by norm_num) (by norm_num),hs 2 (by norm_num) (by norm_num),hs 3 (by norm_num) (by norm_num)])

/-- The same literal second-order reflection preserves bounded raw parabolic
jets before any Holder seminorm is known. This is the interpolation input
needed for genuine boundary data on a curved domain. -/
theorem halfSpaceSecondOrderExtension_raw_bounds {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    {T K : ℝ} (hT : 0 < T) (hK : 0 ≤ K) {v : Point n → ℝ}
    (hv : C2 (cylinder {x | 0 ≤ inner ℝ e x} 0 T) v)
    (hBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
      |v p| ≤ K ∧ ‖spatialD v p‖ ≤ K ∧ ‖spatialDD v p‖ ≤ K ∧
        |timeD (cylinder {x | 0 ≤ inner ℝ e x} 0 T) v p| ≤ K) :
    let U := halfSpaceSecondOrderExtension e v
    C2 (cylinder Set.univ 0 T) U ∧
      Set.EqOn U v (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      Set.EqOn (spatialD U) (spatialD v) (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      ∀ p ∈ cylinder Set.univ 0 T, |U p| ≤ 500*K ∧ ‖spatialD U p‖ ≤ 500*K ∧
        ‖spatialDD U p‖ ≤ 500*K ∧ |timeD (cylinder Set.univ 0 T) U p| ≤ 500*K := by
  have hD (p : Point n) (hp : p ∈ cylinder {x | 0 < inner ℝ e x} 0 T) :
      HasFDerivAt (fun x => v (x,p.2)) (spatialD v p) p.1 :=
    ((hv.2.2.2.2.1 p ⟨(show 0 < inner ℝ e p.1 from hp.1).le,hp.2⟩).differentiableAt (by norm_num)).hasFDerivAt
  have hDD (p : Point n) (hp : p ∈ cylinder {x | 0 < inner ℝ e x} 0 T) :
      HasFDerivAt (fun x => spatialD v (x,p.2)) (spatialDD v p) p.1 :=
    (((hv.2.2.2.2.1 p ⟨(show 0 < inner ℝ e p.1 from hp.1).le,hp.2⟩).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have ht (p : Point n) (hp : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T) :
      HasDerivWithinAt (fun t => v (p.1,t))
        (timeD (cylinder {x | 0 ≤ inner ℝ e x} 0 T) v p) (Set.Icc 0 T) p.2 := by
    have hh := hv.2.2.2.2.2 p hp
    have hFiber : {t | (p.1,t) ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T} = Set.Icc 0 T := by
      ext t
      simp only [Yau.Parabolic.cylinder,Set.mem_prod,Set.mem_ofPred_eq,hp.1,true_and]
    simpa only [timeD,hFiber] using hh.hasDerivWithinAt
  obtain ⟨hU,hEq,hDp,hDDp,hTp⟩ := halfSpaceSecondOrderExtension_jets he hT v (spatialD v)
    (spatialDD v) (timeD (cylinder {x | 0 ≤ inner ℝ e x} 0 T) v)
    hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hD hDD ht
  refine ⟨hU,hEq,hDp,?_⟩
  intro p hp
  by_cases hn : 0 ≤ inner ℝ e p.1
  · have hbp := hBound p ⟨hn,hp.2⟩
    rw [hEq ⟨hn,hp.2⟩,hDp ⟨hn,hp.2⟩,hDDp ⟨hn,hp.2⟩,hTp ⟨hn,hp.2⟩]
    exact ⟨by nlinarith [hbp.1],by nlinarith [hbp.2.1],by nlinarith [hbp.2.2.1],by nlinarith [hbp.2.2.2]⟩
  · have hn' : inner ℝ e p.1 < 0 := lt_of_not_ge hn
    have h0 : |halfSpaceSecondOrderExtension e v p| ≤ 17*K := by
      have h := transportValue_sup (f := v) (K := K) he (fun q hq => by
        simpa only [Real.norm_eq_abs] using (hBound q hq).1) hn'.le hp.2
      simpa only [halfSpaceSecondOrderExtension,ite_eq_right hn,transportValue,smul_eq_mul,Real.norm_eq_abs] using h
    have h1 : ‖spatialD (halfSpaceSecondOrderExtension e v) p‖ ≤ 85*K := by
      rw [spatialD_transport_neg he hD hn' hp.2]
      exact transportD_sup he (fun q hq => (hBound q hq).2.1) hn'.le hp.2
    have h2 : ‖spatialDD (halfSpaceSecondOrderExtension e v) p‖ ≤ 425*K := by
      rw [spatialDD_transport_neg he hD hDD hn' hp.2]
      exact transportDD_sup he (fun q hq => (hBound q hq).2.2.1) hn'.le hp.2
    have h3 : |timeD (cylinder Set.univ 0 T) (halfSpaceSecondOrderExtension e v) p| ≤ 17*K := by
      rw [timeD_transport_neg he hT ht hn' hp.2]
      simpa only [Real.norm_eq_abs] using transportValue_sup
        (f := timeD (cylinder {x | 0 ≤ inner ℝ e x} 0 T) v) (K := K) he
        (fun q hq => by simpa only [Real.norm_eq_abs] using (hBound q hq).2.2.2) hn'.le hp.2
    exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end Yau.LeafProofs.L16Aux
