import Yau.LeafProofs.L21MixedFrameRows
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open scoped ContDiff Topology
noncomputable section
set_option maxHeartbeats 500000
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem mixedFrame_realVec_norm (a : Yau.RIdx n) : ‖Yau.realVec a‖ = 1 := by
  by_cases h : a.2 = 0 <;> simp [Yau.realVec,h,norm_smul]

theorem mixedFrame_wirt_norm (t : Fin 2) :
    ‖wirtRealCoefficient t‖ ≤ 1 ∧ ‖wirtBarRealCoefficient t‖ ≤ 1 := by
  fin_cases t <;> norm_num [wirtRealCoefficient,wirtBarRealCoefficient,norm_div]

theorem mixedFrame_fderiv_star_norm (f : X n → ℂ) (x : X n) :
    ‖fderiv ℝ (fun y => star (f y)) x‖ = ‖fderiv ℝ f x‖ := by
  rw [fderiv_star]
  exact ContinuousLinearMap.opNorm_ext _ _ (fun v => by simp)

theorem mixedFrame_iterated_star_norm (f : X n → ℂ) (x : X n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => star (f y)) x‖ = ‖iteratedFDeriv ℝ k f x‖ := by
  let S : ℂ ≃ₗᵢ[ℝ] ℂ := { (starL' ℝ : ℂ ≃L[ℝ] ℂ).toLinearEquiv with norm_map' := norm_star }
  exact S.norm_iteratedFDeriv_comp_left f x k

theorem mixedFrame_jet_fderiv {O : Set (X n)} {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : JetBound 2 1 A O) {x : X n} (hx : x ∈ O) (i k : Fin n) :
    ‖A x i k‖ ≤ 1 ∧ ‖fderiv ℝ (fun y => A y i k) x‖ ≤ 1 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => A y i k)) x‖ ≤ 1 := by
  refine ⟨?_,?_,?_⟩
  · simpa only [norm_iteratedFDeriv_zero] using hA 0 (by omega) x hx i k
  · simpa only [norm_iteratedFDeriv_one] using hA 1 (by omega) x hx i k
  · have h := hA 2 (by omega) x hx i k
    rwa [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] at h

theorem mixedFrameDerivativeSize_nonneg (A : X n → Matrix (Fin n) (Fin n) ℂ) (x : X n) :
    0 ≤ mixedFrameDerivativeSize A x := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem mixedFrameDerivativeSize_entry (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (x : X n) (i k : Fin n) : ‖fderiv ℝ (fun y => A y i k) x‖ ≤ mixedFrameDerivativeSize A x := by
  unfold mixedFrameDerivativeSize
  exact (Finset.single_le_sum (f := fun k => ‖fderiv ℝ (fun y => A y i k) x‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans
    (Finset.single_le_sum (f := fun i => ∑ k, ‖fderiv ℝ (fun y => A y i k) x‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ i))

theorem mixedFrameDerivativeSize_le {O : Set (X n)} {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : JetBound 2 1 A O) {x : X n} (hx : x ∈ O) : mixedFrameDerivativeSize A x ≤ (n : ℝ)^2 := by
  calc
    _ ≤ ∑ _i : Fin n, ∑ _k : Fin n, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => (mixedFrame_jet_fderiv hA hx i k).2.1))
    _ = _ := by simp; ring

theorem mixedFrame_row_norm {A : X n → Matrix (Fin n) (Fin n) ℂ}
    {x : X n} (hA : ∀ i k, ‖A x i k‖ ≤ 1) (i : Fin n) (a : Yau.RIdx n) :
    ‖dbarRealCoefficient A i a x‖ ≤ 2 := by
  have hConst : ‖(if a.1=i then wirtBarRealCoefficient a.2 else 0)‖ ≤ 1 := by
    by_cases ha : a.1=i
    · simpa only [ite_eq_left ha] using (mixedFrame_wirt_norm a.2).2
    · simp only [ite_eq_right ha,norm_zero]; norm_num
  exact (norm_add_le _ _).trans (by
    have hm := mul_le_mul (hA i a.1) (mixedFrame_wirt_norm a.2).1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [norm_mul] using (show _ ≤ (2 : ℝ) by linarith only [hConst,hm]))

theorem mixedFrame_row_fderiv_norm {A : X n → Matrix (Fin n) (Fin n) ℂ}
    {x : X n} (hA : ∀ i k, DifferentiableAt ℝ (fun y => A y i k) x)
    (i : Fin n) (a : Yau.RIdx n) :
    ‖fderiv ℝ (dbarRealCoefficient A i a) x‖ ≤ ‖fderiv ℝ (fun y => A y i a.1) x‖ := by
  change ‖fderiv ℝ (fun y => (if a.1=i then wirtBarRealCoefficient a.2 else 0)+A y i a.1*wirtRealCoefficient a.2) x‖ ≤ _
  rw [fderiv_fun_add (differentiableAt_const _) ((hA i a.1).mul_const _),fderiv_const_apply,zero_add,
    fderiv_mul_const (hA i a.1)]
  simpa only [norm_smul,one_mul] using mul_le_mul_of_nonneg_right (mixedFrame_wirt_norm a.2).1 (norm_nonneg _)

theorem mixedFrame_rowApply_norm (p : Yau.RIdx n → X n → ℂ) (f : X n → ℂ) (x : X n)
    {P : ℝ} (hP : ∀ a, ‖p a x‖ ≤ P) :
    ‖rowApply Yau.realVec p f x‖ ≤ (2*(n : ℝ)*P)*‖fderiv ℝ f x‖ := by
  calc
    _ ≤ ∑ a : Yau.RIdx n, ‖p a x * fderiv ℝ f x (Yau.realVec a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Yau.RIdx n, P*‖fderiv ℝ f x‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_left ((fderiv ℝ f x).le_opNorm _) (norm_nonneg _)).trans
      rw [mixedFrame_realVec_norm,mul_one]
      exact mul_le_mul_of_nonneg_right (hP a) (norm_nonneg _)
    _ = _ := by simp [Yau.RIdx]; ring

theorem mixedFrame_rowApply_fderiv_norm (p : Yau.RIdx n → X n → ℂ) (f : X n → ℂ) (x : X n)
    (hp : ∀ a, DifferentiableAt ℝ (p a) x) (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    {P Q U V : ℝ} (hP : ∀ a, ‖p a x‖ ≤ P) (hQ : ∀ a, ‖fderiv ℝ (p a) x‖ ≤ Q)
    (hU : ‖fderiv ℝ f x‖ ≤ U) (hV : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ V)
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) :
    ‖fderiv ℝ (rowApply Yau.realVec p f) x‖ ≤ 2*(n : ℝ)*(Q*U+P*V) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [fderiv_rowApply _ _ hp hf]
  calc
    _ ≤ ∑ a : Yau.RIdx n, (‖fderiv ℝ (p a) x w * fderiv ℝ f x (Yau.realVec a)‖+
        ‖p a x * fderiv ℝ (fderiv ℝ f) x w (Yau.realVec a)‖) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => norm_add_le _ _))
    _ ≤ ∑ _a : Yau.RIdx n, (Q*U+P*V)*‖w‖ := by
      apply Finset.sum_le_sum
      intro a _
      have h1 : ‖fderiv ℝ (p a) x w‖ ≤ Q*‖w‖ :=
        ((fderiv ℝ (p a) x).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hQ a) (norm_nonneg _))
      have h2 : ‖fderiv ℝ f x (Yau.realVec a)‖ ≤ U := by
        simpa only [mixedFrame_realVec_norm,mul_one] using ((fderiv ℝ f x).le_opNorm (Yau.realVec a)).trans
          (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
      have h3 : ‖fderiv ℝ (fderiv ℝ f) x w (Yau.realVec a)‖ ≤ V*‖w‖ := by
        simpa only [mixedFrame_realVec_norm,mul_one] using
          (((fderiv ℝ (fderiv ℝ f) x w).le_opNorm (Yau.realVec a)).trans
            (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) x).le_opNorm w).trans
              (mul_le_mul_of_nonneg_right hV (norm_nonneg _))) (norm_nonneg _)))
      simp only [norm_mul]
      calc
        _ ≤ (Q*‖w‖)*U+P*(V*‖w‖) := add_le_add
          (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
          (mul_le_mul (hP a) h3 (norm_nonneg _) hP0)
        _ = _ := by ring
    _ = _ := by simp [Yau.RIdx]; ring

theorem mixedFrame_coordinate_fderiv {W : X n → MixedFrameVector n} {x : X n}
    (hW : DifferentiableAt ℝ W x) (k : Fin n) (v : X n) :
    fderiv ℝ (fun y => (W y).1 k) x v = (fderiv ℝ W x v).1 k ∧
      fderiv ℝ (fun y => (W y).2 k) x v = (fderiv ℝ W x v).2 k := by
  constructor
  · rw [fderiv_apply hW.fst k,fderiv.fst hW]; rfl
  · rw [fderiv_apply hW.snd k,fderiv.snd hW]; rfl

theorem mixedFrame_pair_fderiv_norm {W : X n → MixedFrameVector n} {x : X n}
    (hW : DifferentiableAt ℝ W x) {C : ℝ} (hC : 0 ≤ C)
    (h1 : ∀ k, ‖fderiv ℝ (fun y => (W y).1 k) x‖ ≤ C)
    (h2 : ∀ k, ‖fderiv ℝ (fun y => (W y).2 k) x‖ ≤ C) :
    ‖fderiv ℝ W x‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  change max ‖(fderiv ℝ W x v).1‖ ‖(fderiv ℝ W x v).2‖ ≤ C*‖v‖
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))).mpr
    intro k
    rw [← (mixedFrame_coordinate_fderiv hW k v).1]
    exact ((fderiv ℝ (fun y => (W y).1 k) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h1 k) (norm_nonneg v))
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))).mpr
    intro k
    rw [← (mixedFrame_coordinate_fderiv hW k v).2]
    exact ((fderiv ℝ (fun y => (W y).2 k) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h2 k) (norm_nonneg v))

def mixedFrameBracketConstant (n : ℕ) : ℝ := 1+6*(n : ℝ)

theorem mixedFrame_actual_row_bounds {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hJet : JetBound 2 1 A O) {x : X n} (hx : x ∈ O)
    (r : Fin n) {f : X n → ℂ} (hf : ContDiffAt ℝ ∞ f x)
    (hD : ‖fderiv ℝ f x‖ ≤ 1) (hDD : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ 1) :
    (‖dbarA A r f x‖ ≤ 4*(n : ℝ)*‖fderiv ℝ f x‖) ∧
    (‖conjugateD A r f x‖ ≤ 4*(n : ℝ)*‖fderiv ℝ f x‖) ∧
    (‖fderiv ℝ (dbarA A r f) x‖ ≤ 6*(n : ℝ)) ∧
    (‖fderiv ℝ (conjugateD A r f) x‖ ≤ 6*(n : ℝ)) := by
  have hAD (i k : Fin n) := ((hA i k).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hp (a : Yau.RIdx n) :=
    ((dbarRealCoefficient_smoothOn hA r a).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hq (a : Yau.RIdx n) := (hp a).star
  have hP (a : Yau.RIdx n) := mixedFrame_row_norm (fun i k => (mixedFrame_jet_fderiv hJet hx i k).1) r a
  have hQ (a : Yau.RIdx n) := (mixedFrame_row_fderiv_norm hAD r a).trans (mixedFrame_jet_fderiv hJet hx r a.1).2.1
  have hPQ (a : Yau.RIdx n) : ‖star (dbarRealCoefficient A r a x)‖ ≤ 2 := by simpa only [norm_star] using hP a
  have hQQ (a : Yau.RIdx n) : ‖fderiv ℝ (fun y => star (dbarRealCoefficient A r a y)) x‖ ≤ 1 := by
    rw [mixedFrame_fderiv_star_norm]; exact hQ a
  have hdf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hEq : dbarA A r f = rowApply Yau.realVec (dbarRealCoefficient A r) f :=
    funext (dbarA_eq_real_rows A r f)
  rw [hEq]
  refine ⟨?_,?_,?_,?_⟩
  · convert mixedFrame_rowApply_norm (dbarRealCoefficient A r) f x hP using 1
    ring
  · change ‖rowApply Yau.realVec (fun a y => star (dbarRealCoefficient A r a y)) f x‖ ≤ _
    convert mixedFrame_rowApply_norm (fun a y => star (dbarRealCoefficient A r a y)) f x hPQ using 1
    ring
  · convert mixedFrame_rowApply_fderiv_norm (dbarRealCoefficient A r) f x
      hp hdf hP hQ hD hDD (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    ring
  · change ‖fderiv ℝ (rowApply Yau.realVec (fun a y => star (dbarRealCoefficient A r a y)) f) x‖ ≤ _
    convert mixedFrame_rowApply_fderiv_norm (fun a y => star (dbarRealCoefficient A r a y)) f x
      hq hdf hPQ hQQ hD hDD (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1
    ring

theorem mixedFrameBracketData_bounds {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hJet : JetBound 2 1 A O) {x : X n} (hx : x ∈ O) (i j : Fin n) :
    ‖mixedFrameBracketData A i j x‖ ≤ mixedFrameBracketConstant n*mixedFrameDerivativeSize A x ∧
      ‖fderiv ℝ (mixedFrameBracketData A i j) x‖ ≤ mixedFrameBracketConstant n := by
  have hB0 : 0 ≤ mixedFrameBracketConstant n := by unfold mixedFrameBracketConstant; positivity
  have hVal (r s k : Fin n) := (hA s k).contDiffAt (hO.mem_nhds hx)
  have hOrd (k : Fin n) := mixedFrame_actual_row_bounds hO hA hJet hx j (hVal j i k)
    (mixedFrame_jet_fderiv hJet hx i k).2.1 (mixedFrame_jet_fderiv hJet hx i k).2.2
  have hStar (k : Fin n) :
      ‖fderiv ℝ (fun y => star (A y j k)) x‖ ≤ 1 ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => star (A y j k))) x‖ ≤ 1 := by
    constructor
    · rw [mixedFrame_fderiv_star_norm]; exact (mixedFrame_jet_fderiv hJet hx j k).2.1
    · rw [← norm_iteratedFDeriv_one (fderiv ℝ (fun y => star (A y j k))),
        norm_iteratedFDeriv_fderiv,mixedFrame_iterated_star_norm]
      exact hJet 2 (by omega) x hx j k
  have hConj (k : Fin n) := mixedFrame_actual_row_bounds hO hA hJet hx i (f := fun y => star (A y j k))
    ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffAt x (hVal i j k)) (hStar k).1 (hStar k).2
  have hCB : 4*(n : ℝ) ≤ mixedFrameBracketConstant n := by unfold mixedFrameBracketConstant; have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith
  have hDB : 6*(n : ℝ) ≤ mixedFrameBracketConstant n := by unfold mixedFrameBracketConstant; linarith
  constructor
  · change max ‖fun k => mixedFrameAntiholomorphicBracket A i j k x‖
      ‖fun k => mixedFrameHolomorphicBracket A i j k x‖ ≤ _
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB0 (mixedFrameDerivativeSize_nonneg A x))).mpr
      intro k
      exact (hConj k).1.trans ((mul_le_mul_of_nonneg_left (by
        rw [mixedFrame_fderiv_star_norm]; exact mixedFrameDerivativeSize_entry A x j k) (by positivity)).trans
          (mul_le_mul_of_nonneg_right hCB (mixedFrameDerivativeSize_nonneg A x)))
    · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB0 (mixedFrameDerivativeSize_nonneg A x))).mpr
      intro k
      change ‖-conjugateD A j (fun y => A y i k) x‖ ≤ _
      rw [norm_neg]
      exact (hOrd k).2.1.trans ((mul_le_mul_of_nonneg_left (mixedFrameDerivativeSize_entry A x i k) (by positivity)).trans
        (mul_le_mul_of_nonneg_right hCB (mixedFrameDerivativeSize_nonneg A x)))
  · apply mixedFrame_pair_fderiv_norm
      (((mixedFrameBracketData_smooth hO hA i j).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)) hB0
    · intro k
      exact (hConj k).2.2.1.trans hDB
    · intro k
      change ‖fderiv ℝ (fun y => -conjugateD A j (fun z => A z i k) y) x‖ ≤ _
      rw [fderiv_fun_neg]; simp only [norm_neg]
      exact (hOrd k).2.2.2.trans hDB

theorem mixedFrame_slot_fderiv_norm {a : X n → ℂ} {x : X n}
    (ha : DifferentiableAt ℝ a x) (P : MixedFrameVector n →L[ℝ] MixedFrameVector n) :
    ‖fderiv ℝ (fun y => a y • P) x‖ ≤ ‖fderiv ℝ a x‖*‖P‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro w
  rw [fderiv_smul_const ha P]
  change ‖fderiv ℝ a x w • P‖ ≤ _
  rw [norm_smul]
  exact ((mul_le_mul_of_nonneg_right ((fderiv ℝ a x).le_opNorm w) (norm_nonneg P))).trans_eq (by ring)

theorem mixedFrameOperator_fderiv_norm {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hJet : JetBound 2 1 A O) {x : X n} (hx : x ∈ O) :
    ‖fderiv ℝ (fun y => mixedFrameOperator (A y)) x‖ ≤ 2*(n : ℝ)^2 := by
  have hAD (i k : Fin n) := ((hA i k).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  let term (i k : Fin n) (y : X n) := star (A y i k) • mixedFrameSlot0 i k+A y i k • mixedFrameSlot1 i k
  have hterm (i k : Fin n) : DifferentiableAt ℝ (term i k) x :=
    ((hAD i k).star.smul_const _).add ((hAD i k).smul_const _)
  have hsum (i : Fin n) : DifferentiableAt ℝ (fun y => ∑ k, term i k y) x :=
    DifferentiableAt.fun_sum (fun k _ => hterm i k)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have hbound (i k : Fin n) : ‖fderiv ℝ (term i k) x w‖ ≤ 2*‖w‖ := by
    have hval : fderiv ℝ (term i k) x w =
        fderiv ℝ (fun y => star (A y i k)) x w • mixedFrameSlot0 i k+
        fderiv ℝ (fun y => A y i k) x w • mixedFrameSlot1 i k := by
      dsimp only [term]
      rw [fderiv_fun_add ((hAD i k).star.smul_const (mixedFrameSlot0 i k))
        ((hAD i k).smul_const (mixedFrameSlot1 i k))]
      change fderiv ℝ (fun y => star (A y i k) • mixedFrameSlot0 i k) x w+
        fderiv ℝ (fun y => A y i k • mixedFrameSlot1 i k) x w = _
      rw [fderiv_smul_const (hAD i k).star (mixedFrameSlot0 i k),
        fderiv_smul_const (hAD i k) (mixedFrameSlot1 i k)]
      rfl
    have hD : ‖fderiv ℝ (fun y => A y i k) x w‖ ≤ ‖w‖ := by
      simpa only [one_mul] using ((fderiv ℝ (fun y => A y i k) x).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right (mixedFrame_jet_fderiv hJet hx i k).2.1 (norm_nonneg _))
    have hS : ‖fderiv ℝ (fun y => star (A y i k)) x w‖ ≤ ‖w‖ := by
      have hSnorm : ‖fderiv ℝ (fun y => star (A y i k)) x‖ ≤ 1 := by
        rw [mixedFrame_fderiv_star_norm]; exact (mixedFrame_jet_fderiv hJet hx i k).2.1
      simpa only [one_mul] using ((fderiv ℝ (fun y => star (A y i k)) x).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right hSnorm (norm_nonneg _))
    rw [hval]
    calc
      _ ≤ ‖fderiv ℝ (fun y => star (A y i k)) x w • mixedFrameSlot0 i k‖+
          ‖fderiv ℝ (fun y => A y i k) x w • mixedFrameSlot1 i k‖ := norm_add_le _ _
      _ ≤ ‖w‖*1+‖w‖*1 := by
        simp only [norm_smul]
        exact add_le_add (mul_le_mul hS (mixedFrameSlot0_norm i k) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul hD (mixedFrameSlot1_norm i k) (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  change ‖fderiv ℝ (fun y => ContinuousLinearMap.id ℝ (MixedFrameVector n)+∑ i, ∑ k, term i k y) x w‖ ≤ _
  rw [fderiv_fun_add (differentiableAt_const (ContinuousLinearMap.id ℝ (MixedFrameVector n)))
      (DifferentiableAt.fun_sum (fun i _ => hsum i)),fderiv_const_apply,zero_add,
    fderiv_fun_sum (fun i _ => hsum i)]
  simp only [_root_.sum_apply]
  calc
    _ ≤ ∑ i, ‖fderiv ℝ (fun y => ∑ k, term i k y) x w‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ k, ‖fderiv ℝ (term i k) x w‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [fderiv_fun_sum (fun k _ => hterm i k)]
      simp only [_root_.sum_apply]
      exact norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ∑ _k : Fin n, 2*‖w‖ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hbound i k))
    _ = _ := by simp; ring

theorem mixedFrameCoefficientVector_norm {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hSmall : JetBound 0 (mixedFrameEpsilon n) A O) (hJet : JetBound 2 1 A O)
    {x : X n} (hx : x ∈ O) (i j : Fin n) :
    ‖mixedFrameCoefficientVector A i j x‖ ≤ (2*mixedFrameBracketConstant n)*mixedFrameDerivativeSize A x := by
  have hEntry (r k : Fin n) : ‖A x r k‖ ≤ mixedFrameEpsilon n := by
    simpa only [norm_iteratedFDeriv_zero] using hSmall 0 (by omega) x hx r k
  calc
    _ ≤ 2*‖mixedFrameOperator (A x) (mixedFrameCoefficientVector A i j x)‖ := mixedFrameOperator_lower hEntry _
    _ = 2*‖mixedFrameBracketData A i j x‖ := by rw [mixedFrameCoefficientVector_equation hEntry]
    _ ≤ 2*(mixedFrameBracketConstant n*mixedFrameDerivativeSize A x) := mul_le_mul_of_nonneg_left
      (mixedFrameBracketData_bounds hO hA hJet hx i j).1 (by norm_num)
    _ = _ := by ring

def mixedFrameC1Constant (n : ℕ) : ℝ :=
  2*(mixedFrameBracketConstant n+(2*(n : ℝ)^2)*((2*mixedFrameBracketConstant n)*(n : ℝ)^2))

theorem mixedFrameCoefficientVector_fderiv_norm {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hSmall : JetBound 0 (mixedFrameEpsilon n) A O) (hJet : JetBound 2 1 A O)
    {x : X n} (hx : x ∈ O) (i j : Fin n) :
    ‖fderiv ℝ (mixedFrameCoefficientVector A i j) x‖ ≤ mixedFrameC1Constant n := by
  have hB0 : 0 ≤ mixedFrameBracketConstant n := by unfold mixedFrameBracketConstant; positivity
  have hEntry (y : X n) (hy : y ∈ O) (r k : Fin n) : ‖A y r k‖ ≤ mixedFrameEpsilon n := by
    simpa only [norm_iteratedFDeriv_zero] using hSmall 0 (by omega) y hy r k
  have hF := ((mixedFrameOperator_smooth hA).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hWsmooth : ContDiffOn ℝ ∞ (mixedFrameCoefficientVector A i j) O :=
    (mixedFrameOperator_inverse_smooth hO hA hSmall).clm_apply (mixedFrameBracketData_smooth hO hA i j)
  have hW := (hWsmooth.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have heq : (fun y => mixedFrameOperator (A y) (mixedFrameCoefficientVector A i j y)) =ᶠ[𝓝 x]
      mixedFrameBracketData A i j := by
    filter_upwards [show ∀ᶠ y in 𝓝 x, y ∈ O from hO.mem_nhds hx] with y hy
    exact mixedFrameCoefficientVector_equation (hEntry y hy) i j
  have hDeq := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_clm_apply hF hW] at hDeq
  have hV := (mixedFrameCoefficientVector_norm hO hA hSmall hJet hx i j).trans
    (mul_le_mul_of_nonneg_left (mixedFrameDerivativeSize_le hJet hx) (mul_nonneg (by norm_num) hB0))
  have hDF := mixedFrameOperator_fderiv_norm hO hA hJet hx
  have hDB := (mixedFrameBracketData_bounds hO hA hJet hx i j).2
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold mixedFrameC1Constant; positivity)
  intro w
  have hEval := congrArg (fun L : X n →L[ℝ] MixedFrameVector n => L w) hDeq
  change mixedFrameOperator (A x) (fderiv ℝ (mixedFrameCoefficientVector A i j) x w)+
      fderiv ℝ (fun y => mixedFrameOperator (A y)) x w (mixedFrameCoefficientVector A i j x) =
        fderiv ℝ (mixedFrameBracketData A i j) x w at hEval
  have hFval : mixedFrameOperator (A x) (fderiv ℝ (mixedFrameCoefficientVector A i j) x w) =
      fderiv ℝ (mixedFrameBracketData A i j) x w-
        fderiv ℝ (fun y => mixedFrameOperator (A y)) x w (mixedFrameCoefficientVector A i j x) :=
    eq_sub_of_add_eq hEval
  have h1 : ‖fderiv ℝ (mixedFrameBracketData A i j) x w‖ ≤ mixedFrameBracketConstant n*‖w‖ :=
    ((fderiv ℝ (mixedFrameBracketData A i j) x).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hDB (norm_nonneg _))
  have h2 : ‖fderiv ℝ (fun y => mixedFrameOperator (A y)) x w (mixedFrameCoefficientVector A i j x)‖ ≤
      ((2*(n : ℝ)^2)*‖w‖)*((2*mixedFrameBracketConstant n)*(n : ℝ)^2) := by
    calc
      _ ≤ ‖fderiv ℝ (fun y => mixedFrameOperator (A y)) x w‖*‖mixedFrameCoefficientVector A i j x‖ :=
        (fderiv ℝ (fun y => mixedFrameOperator (A y)) x w).le_opNorm _
      _ ≤ _ := mul_le_mul
        (((fderiv ℝ (fun y => mixedFrameOperator (A y)) x).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right hDF (norm_nonneg _))) hV (norm_nonneg _) (by positivity)
  calc
    _ ≤ 2*‖mixedFrameOperator (A x) (fderiv ℝ (mixedFrameCoefficientVector A i j) x w)‖ :=
      mixedFrameOperator_lower (hEntry x hx) _
    _ ≤ 2*(‖fderiv ℝ (mixedFrameBracketData A i j) x w‖+
        ‖fderiv ℝ (fun y => mixedFrameOperator (A y)) x w (mixedFrameCoefficientVector A i j x)‖) := by
      rw [hFval]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ 2*(mixedFrameBracketConstant n*‖w‖+((2*(n : ℝ)^2)*‖w‖)*((2*mixedFrameBracketConstant n)*(n : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
    _ = _ := by unfold mixedFrameC1Constant; ring

theorem mixedFrame_coefficients_norm {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hSmall : JetBound 0 (mixedFrameEpsilon n) A O) (hJet : JetBound 2 1 A O)
    {x : X n} (hx : x ∈ O) (i j k : Fin n) :
    ‖mixedFrameC A i j k x‖ ≤ (2*mixedFrameBracketConstant n)*mixedFrameDerivativeSize A x ∧
      ‖mixedFrameD A i j k x‖ ≤ (2*mixedFrameBracketConstant n)*mixedFrameDerivativeSize A x := by
  have hW := mixedFrameCoefficientVector_norm hO hA hSmall hJet hx i j
  constructor
  · exact ((norm_le_pi_norm (mixedFrameCoefficientVector A i j x).1 k).trans (le_max_left _ _)).trans hW
  · exact ((norm_le_pi_norm (mixedFrameCoefficientVector A i j x).2 k).trans (le_max_right _ _)).trans hW

theorem mixedFrame_coefficients_fderiv_norm {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hSmall : JetBound 0 (mixedFrameEpsilon n) A O) (hJet : JetBound 2 1 A O)
    {x : X n} (hx : x ∈ O) (i j k : Fin n) :
    ‖fderiv ℝ (mixedFrameC A i j k) x‖ ≤ mixedFrameC1Constant n ∧
      ‖fderiv ℝ (mixedFrameD A i j k) x‖ ≤ mixedFrameC1Constant n := by
  have hWsmooth : ContDiffOn ℝ ∞ (mixedFrameCoefficientVector A i j) O :=
    (mixedFrameOperator_inverse_smooth hO hA hSmall).clm_apply (mixedFrameBracketData_smooth hO hA i j)
  have hW := (hWsmooth.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hBound := mixedFrameCoefficientVector_fderiv_norm hO hA hSmall hJet hx i j
  have hC0 : 0 ≤ mixedFrameC1Constant n := by unfold mixedFrameC1Constant mixedFrameBracketConstant; positivity
  constructor <;> apply ContinuousLinearMap.opNorm_le_bound _ hC0 <;> intro w
  · change ‖fderiv ℝ (fun y => (mixedFrameCoefficientVector A i j y).1 k) x w‖ ≤ _
    rw [(mixedFrame_coordinate_fderiv hW k w).1]
    exact ((norm_le_pi_norm (fderiv ℝ (mixedFrameCoefficientVector A i j) x w).1 k).trans
      (le_max_left _ _)).trans (((fderiv ℝ (mixedFrameCoefficientVector A i j) x).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right hBound (norm_nonneg _)))
  · change ‖fderiv ℝ (fun y => (mixedFrameCoefficientVector A i j y).2 k) x w‖ ≤ _
    rw [(mixedFrame_coordinate_fderiv hW k w).2]
    exact ((norm_le_pi_norm (fderiv ℝ (mixedFrameCoefficientVector A i j) x w).2 k).trans
      (le_max_right _ _)).trans (((fderiv ℝ (mixedFrameCoefficientVector A i j) x).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right hBound (norm_nonneg _)))

end Yau.LeafProofs.L21Aux
