import Yau.LeafProofs.L23LocalDistanceSupportCalculus

/-! A joint smooth distance-square upper support gives the required genuine
moving cutoff lower support, with its quantitative differential bounds. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix
namespace Yau.LeafProofs.L23Aux
open L12Aux L18Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}

def distanceSupportProfile (R u : ℝ) : ℝ := (1-u/R^2)^2

theorem distanceSupportProfile_contDiff (R : ℝ) :
    ContDiff ℝ ∞ (distanceSupportProfile R) :=
  (contDiff_const.sub (contDiff_id.div_const (R^2))).pow 2

theorem distanceSupportProfile_hasDerivAt (R u : ℝ) :
    HasDerivAt (distanceSupportProfile R) (-2*(1-u/R^2)/R^2) u := by
  have hd := (((hasDerivAt_const u (1 : ℝ)).sub
    ((hasDerivAt_id u).div_const (R^2))).pow 2)
  simp only [Pi.sub_apply, Pi.div_apply, id_eq, Nat.cast_ofNat, pow_one, Nat.reduceSub] at hd
  convert hd using 1
  · rfl
  · ring

theorem distanceSupportProfile_deriv (R u : ℝ) :
    deriv (distanceSupportProfile R) u = -2*(1-u/R^2)/R^2 :=
  (distanceSupportProfile_hasDerivAt R u).deriv

theorem distanceSupportProfile_secondDeriv (R u : ℝ) :
    deriv (deriv (distanceSupportProfile R)) u = 2/(R^2)^2 := by
  have heq : deriv (distanceSupportProfile R) = fun s => -2*(1-s/R^2)/R^2 :=
    funext (distanceSupportProfile_deriv R)
  rw [heq]
  have hd := (((hasDerivAt_const u (1 : ℝ)).sub
    ((hasDerivAt_id u).div_const (R^2))).const_mul (-2) |>.div_const (R^2))
  simp only [Pi.sub_apply, Pi.div_apply, id_eq, Pi.mul_apply] at hd
  convert hd.deriv using 1 <;> ring

theorem distanceSupport_jointC2_continuousAt {E : M.Carrier → ℝ → ℝ}
    {y : M.Carrier} {t : ℝ}
    (hE : ContDiffAt ℝ 2
      (fun z : ComplexVector n × ℝ => E (chartInv y z.1) z.2) (chartPt y y,t)) :
    ContinuousAt (fun p : M.Carrier × ℝ => E p.1 p.2) (y,t) := by
  have hmap : ContinuousAt
      (fun p : M.Carrier × ℝ => (chartPt y p.1,p.2)) (y,t) :=
    ((continuousAt_extChartAt (I := ComplexModel n) y).comp continuousAt_fst).prodMk continuousAt_snd
  have hc := hE.continuousAt.comp
    (f := fun p : M.Carrier × ℝ => (chartPt y p.1,p.2)) hmap
  apply hc.congr
  filter_upwards [continuousAt_fst.preimage_mem_nhds (extChartAt_source_mem_nhds (I := ComplexModel n) y)] with p hp
  exact congrArg (fun z => E z p.2) ((extChartAt (ComplexModel n) y).left_inv hp)

theorem distanceSupport_profile_gradient_bound {D S : ℝ} (hS : 0 < S)
    (hD : 0 ≤ D) (hDS : D ≤ S) :
    (-2*(1-D/S)/S)^2 * (4*D) ≤ (16/S)*(1-D/S)^2 := by
  calc
    _ = ((16/S)*(1-D/S)^2) * (D/S) := by ring
    _ ≤ (16/S)*(1-D/S)^2 := mul_le_of_le_one_right
      (mul_nonneg (div_nonneg (by norm_num) hS.le) (sq_nonneg _))
      ((div_le_one hS).mpr hDS)

theorem distanceSupport_profile_flow_bound {D S P σ m K : ℝ}
    (hS : 0 < S) (hD : 0 ≤ D) (hDS : D ≤ S)
    (hσ : 0 ≤ σ) (hm : 0 ≤ m) (hK : 0 ≤ K)
    (hP : -σ*m-(4/3 : ℝ)*σ*m*K*D ≤ P) :
    (-2*(1-D/S)/S)*P - (σ/2)*(2/S^2)*(4*D) ≤
      σ*(2*m/S+(8/3 : ℝ)*m*K) := by
  let A := 1-D/S
  have hratio : D/S ≤ 1 := (div_le_one hS).mpr hDS
  have hratio0 : 0 ≤ D/S := div_nonneg hD hS.le
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hA1 : A ≤ 1 := by dsimp [A]; linarith
  have hAQ : A*(D/S) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hA1 hratio0).trans (by simpa using hratio)
  have hB : 0 ≤ 2*σ*m/S := div_nonneg (by positivity) hS.le
  have hC : 0 ≤ (8/3 : ℝ)*σ*m*K := by positivity
  have hfirst := mul_le_mul_of_nonneg_left hA1 hB
  have hsecond := mul_le_mul_of_nonneg_left hAQ hC
  have hneg : -2*A/S ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hS.le
  calc
    _ ≤ (-2*A/S)*P := sub_le_self _ (by positivity)
    _ ≤ (-2*A/S)*(-σ*m-(4/3 : ℝ)*σ*m*K*D) := mul_le_mul_of_nonpos_left hP hneg
    _ = (2*σ*m/S)*A + ((8/3 : ℝ)*σ*m*K)*(A*(D/S)) := by ring
    _ ≤ 2*σ*m/S + (8/3 : ℝ)*σ*m*K := by nlinarith only [hfirst, hsecond]
    _ = _ := by ring

theorem exists_timeDistanceCutoff_lowerSupport_of_upperSupport
    (h : ℝ → HermitianField M) (q y : M.Carrier) (R K σ t : ℝ)
    (hR : 0 < R) (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hh : MetricSmooth (h t))
    (E : M.Carrier → ℝ → ℝ)
    (hE : ContDiffAt ℝ 2
      (fun z : ComplexVector n × ℝ => E (chartInv y z.1) z.2) (chartPt y y,t))
    (hval : E y t = inducedDistance (h t) q y ^ 2)
    (hupper : ∀ᶠ z in 𝓝 (y,t), inducedDistance (h z.2) q z.1 ^ 2 ≤ E z.1 z.2)
    (hgrad : realGradPair (h t) (fun z => E z t) (fun z => E z t) y =
      4 * inducedDistance (h t) q y ^ 2)
    (hlap : realLap (h t) (fun z => E z t) y ≤
      2*(2*n : ℕ)+(2/3 : ℝ)*(2*n : ℕ)*K*inducedDistance (h t) q y ^ 2)
    (hdt : -σ*(2*n : ℕ)*K*inducedDistance (h t) q y ^ 2 ≤ deriv (E y) t)
    (hy : inducedDistance (h t) q y < R) :
    ∃ ψ : M.Carrier → ℝ → ℝ,
      ContDiffAt ℝ 2
        (fun z : ComplexVector n × ℝ => ψ (chartInv y z.1) z.2) (chartPt y y,t) ∧
      ψ y t = timeDistanceCutoff h q R y t ∧
      (∀ᶠ z in 𝓝 (y,t), ψ z.1 z.2 ≤ timeDistanceCutoff h q R z.1 z.2) ∧
      realGradPair (h t) (fun z => ψ z t) (fun z => ψ z t) y ≤
        (16/R^2)*timeDistanceCutoff h q R y t ∧
      flowOp h σ ψ y t ≤ σ*(2*(2*n : ℕ)/R^2+(8/3 : ℝ)*(2*n : ℕ)*K) := by
  let d := inducedDistance (h t) q y
  have hd : 0 ≤ d := inducedDistance_nonneg (h t) hh q y
  have hR2 : 0 < R^2 := sq_pos_of_pos hR
  have hdR : d^2 < R^2 := (sq_lt_sq₀ hd hR.le).mpr hy
  have ha : 0 < 1-d^2/R^2 := sub_pos.mpr ((div_lt_one hR2).mpr hdR)
  let ψ : M.Carrier → ℝ → ℝ := fun z s => distanceSupportProfile R (E z s)
  have hψval : ψ y t = timeDistanceCutoff h q R y t := by
    dsimp [ψ, distanceSupportProfile, timeDistanceCutoff]
    rw [hval, max_eq_right ha.le]
  have hnear : ∀ᶠ z in 𝓝 (y,t), E z.1 z.2 < R^2 :=
    (distanceSupport_jointC2_continuousAt hE).eventually
      (Iio_mem_nhds (by change E y t < R^2; rw [hval]; exact hdR))
  have hψupper : ∀ᶠ z in 𝓝 (y,t), ψ z.1 z.2 ≤ timeDistanceCutoff h q R z.1 z.2 := by
    filter_upwards [hnear, hupper] with z hz hDz
    have hA : 0 < 1-E z.1 z.2/R^2 := sub_pos.mpr ((div_lt_one hR2).mpr hz)
    have hle : 1-E z.1 z.2/R^2 ≤ 1-inducedDistance (h z.2) q z.1 ^ 2/R^2 :=
      sub_le_sub_left ((div_le_div_iff_of_pos_right hR2).mpr hDz) 1
    have hB : 0 ≤ 1-inducedDistance (h z.2) q z.1 ^ 2/R^2 := hA.le.trans hle
    dsimp only [ψ, distanceSupportProfile, timeDistanceCutoff]
    rw [max_eq_right hB]
    exact (sq_le_sq₀ hA.le hB).mpr hle
  have hprofile : ContDiffAt ℝ 2 (distanceSupportProfile R) (E y t) :=
    (distanceSupportProfile_contDiff R).contDiffAt.of_le (by simp)
  have hv : inChart y (fun z => E z t) (chartPt y y) = E y t :=
    congrArg (fun z => E z t) ((extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y))
  have hprofile' : ContDiffAt ℝ 2 (distanceSupportProfile R)
      (inChart y (fun z => E z t) (chartPt y y)) := hv.symm ▸ hprofile
  have hg := distanceSupport_chartGrad_scalar_comp (h t) y
    ((distanceSupport_jointC2_space hE).differentiableAt (by norm_num))
    (hprofile'.differentiableAt (by norm_num))
  rw [hv, hval, distanceSupportProfile_deriv] at hg
  change realGradPair (h t) (fun z => ψ z t) (fun z => ψ z t) y =
    (-2*(1-d^2/R^2)/R^2)^2 * realGradPair (h t) (fun z => E z t) (fun z => E z t) y at hg
  have hη : timeDistanceCutoff h q R y t = (1-d^2/R^2)^2 := by
    dsimp [timeDistanceCutoff, d]
    rw [max_eq_right ha.le]
  have hP : -σ*(2*n : ℕ)-(4/3 : ℝ)*σ*(2*n : ℕ)*K*d^2 ≤ flowOp h σ E y t := by
    have H := mul_le_mul_of_nonneg_left hlap (show 0 ≤ σ/2 by positivity)
    dsimp only [flowOp]
    dsimp only [d] at *
    nlinarith only [H, hdt]
  have hop := distanceSupport_flowOp_scalar_comp h σ hE hprofile
  change flowOp h σ ψ y t = _ at hop
  rw [hval, distanceSupportProfile_deriv, distanceSupportProfile_secondDeriv, hgrad] at hop
  refine ⟨ψ, ((contDiffAt_const.sub (hE.div_const (R^2))).pow 2), hψval, hψupper, ?_, ?_⟩
  · rw [hg, hgrad, hη]
    exact distanceSupport_profile_gradient_bound hR2 (sq_nonneg d) hdR.le
  · rw [hop]
    exact distanceSupport_profile_flow_bound hR2 (sq_nonneg d) hdR.le hσ
      (Nat.cast_nonneg _) hK hP

end Yau.LeafProofs.L23Aux
