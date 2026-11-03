import Yau.Proofs.V02CircleTaylor

/-! A bound on the genuine third Fréchet derivative supplies the scalar
cubic Taylor remainder on every ray, with no uniformity assumption about a
family of functions. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

def realRay (z : ℂ) : ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight z

theorem iteratedDeriv_realRay {J : ℂ → ℝ} {r t : ℝ} {m k : ℕ}
    (hJ : ContDiffOn ℝ m J (Metric.ball (0 : ℂ) r)) (hk : k ≤ m)
    (z : ℂ) (ht : t • z ∈ Metric.ball (0 : ℂ) r) :
    iteratedDeriv k (fun t : ℝ => J (t • z)) t =
      iteratedFDeriv ℝ k J (t • z) (fun _ => z) := by
  let L := realRay z
  let U := L ⁻¹' Metric.ball (0 : ℂ) r
  have hU : IsOpen U := Metric.isOpen_ball.preimage L.continuous
  have htU : t ∈ U := ht
  have hcomp : ContDiffOn ℝ m (J ∘ L) U :=
    hJ.comp L.contDiff.contDiffOn (fun _ hu => hu)
  have hck : ContDiffAt ℝ k (J ∘ L) t :=
    (hcomp.contDiffAt (hU.mem_nhds htU)).of_le (by exact_mod_cast hk)
  have hjk : ContDiffAt ℝ k J (L t) :=
    (hJ.contDiffAt (Metric.isOpen_ball.mem_nhds ht)).of_le (by exact_mod_cast hk)
  have he := L.iteratedFDerivWithin_comp_right hJ Metric.isOpen_ball.uniqueDiffOn
    hU.uniqueDiffOn ht (i := k) (by exact_mod_cast hk)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hck htU,
    iteratedFDerivWithin_eq_iteratedFDeriv Metric.isOpen_ball.uniqueDiffOn hjk ht] at he
  change iteratedFDeriv ℝ k (J ∘ L) t (fun _ => 1) = _
  rw [he]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, L, realRay,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul]

theorem thirdTaylor_remainder {J : ℂ → ℝ} {r M : ℝ}
    (hJ : ContDiffOn ℝ 3 J (Metric.ball (0 : ℂ) r))
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) r, ‖iteratedFDeriv ℝ 3 J z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ < r) :
    |J z - J 0 - fderiv ℝ J 0 z -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ J) 0 z z| ≤ (M / 2) * ‖z‖ ^ 3 := by
  have hr : 0 < r := (norm_nonneg z).trans_lt hz
  have hm (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      t • z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz
  have hpath : ContDiffOn ℝ 3 (fun t : ℝ => J (t • z)) (Set.Icc (0 : ℝ) 1) :=
    hJ.comp (contDiff_id.smul contDiff_const).contDiffOn hm
  have hlocal (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 3 (fun t : ℝ => J (t • z)) t :=
    (hJ.contDiffAt (Metric.isOpen_ball.mem_nhds (hm t ht))).comp t
      (contDiffAt_id.smul contDiffAt_const)
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin 3 (fun t : ℝ => J (t • z)) (Set.Icc (0 : ℝ) 1) t‖ ≤
        M * ‖z‖ ^ 3 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hlocal t ht) ht, iteratedDeriv_realRay hJ le_rfl z (hm t ht)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 3 J (t • z)‖ * ∏ _i : Fin 3, ‖z‖ :=
        (iteratedFDeriv ℝ 3 J (t • z)).le_opNorm (fun _ => z)
      _ ≤ _ := by simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        mul_le_mul_of_nonneg_right (hM _ (hm t ht)) (pow_nonneg (norm_nonneg z) 3)
  have hTaylor := taylor_mean_remainder_bound (f := fun t : ℝ => J (t • z))
    (a := 0) (b := 1) (n := 2) (x := 1) (by norm_num) hpath (by norm_num) hd
  have h₁ : iteratedDerivWithin 1 (fun t : ℝ => J (t • z)) (Set.Icc (0 : ℝ) 1) 0 =
      fderiv ℝ J 0 z := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      ((hlocal 0 (by norm_num)).of_le (by norm_num)) (by norm_num),
      iteratedDeriv_realRay hJ (by norm_num) z (hm 0 (by norm_num))]
    simp only [zero_smul, iteratedFDeriv_one_apply]
  have h₂ : iteratedDerivWithin 2 (fun t : ℝ => J (t • z)) (Set.Icc (0 : ℝ) 1) 0 =
      fderiv ℝ (fderiv ℝ J) 0 z z := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      ((hlocal 0 (by norm_num)).of_le (by norm_num)) (by norm_num),
      iteratedDeriv_realRay hJ (by norm_num) z (hm 0 (by norm_num))]
    simp only [zero_smul, iteratedFDeriv_two_apply]
  have heval : taylorWithinEval (fun t : ℝ => J (t • z)) 2 (Set.Icc (0 : ℝ) 1) 0 1 =
      J 0 + fderiv ℝ J 0 z + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ J) 0 z z := by
    rw [taylorWithinEval_succ (fun t : ℝ => J (t • z)) 1 (Set.Icc 0 1) 0 1,
      taylorWithinEval_succ (fun t : ℝ => J (t • z)) 0 (Set.Icc 0 1) 0 1,
      taylor_within_zero_eval, h₁, h₂]
    norm_num
  rw [heval] at hTaylor
  norm_num only [one_smul, sub_zero, one_pow, Nat.factorial_two, Nat.cast_ofNat,
    Real.norm_eq_abs] at hTaylor
  convert hTaylor using 1 <;> ring

/-- A bound on the actual third derivative yields the exact scalar circle
estimate used by the whole-functional realization contract. -/
theorem parameterCircleTaylor {J : ℂ → ℝ} {r M : ℝ}
    (hJ : ContDiffOn ℝ 3 J (Metric.ball (0 : ℂ) r))
    (hM : ∀ z ∈ Metric.ball (0 : ℂ) r, ‖iteratedFDeriv ℝ 3 J z‖ ≤ M)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) :
    |circleAverage (fun θ => J ((ρ : ℂ) * circlePoint θ)) - J 0 -
      ρ ^ 2 * V03Proof.mixedReal J| ≤ (M / 2) * ρ ^ 3 := by
  have hr := hρ.trans hρr
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by simpa using hr
  have hJ0 : ContDiffAt ℝ 2 J 0 :=
    (hJ.contDiffAt (Metric.isOpen_ball.mem_nhds h0)).of_le (by norm_num)
  have hnorm (θ : ℝ) : ‖(ρ : ℂ) * circlePoint θ‖ = ρ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      V03Proof.circlePoint_norm, mul_one]
  have hm (θ : ℝ) : (ρ : ℂ) * circlePoint θ ∈ Metric.ball (0 : ℂ) r := by
    simpa only [Metric.mem_ball, dist_zero_right, hnorm θ] using hρr
  have hc : Continuous (fun θ => J ((ρ : ℂ) * circlePoint θ)) :=
    hJ.continuousOn.comp_continuous (by unfold circlePoint; fun_prop) hm
  apply parameterCircleTaylor_of_pointwise hJ0 hc
  intro θ
  have h := thirdTaylor_remainder hJ hM (z := (ρ : ℂ) * circlePoint θ)
    (by simpa only [hnorm θ] using hρr)
  simpa only [hnorm θ] using h

end Yau.Blueprint.V02Proof
