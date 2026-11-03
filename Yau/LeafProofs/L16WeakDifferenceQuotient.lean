import Yau.LeafProofs.L16EnergyLimit
import Mathlib.Analysis.Convex.Integral

open MeasureTheory Filter
open scoped Topology ContDiff Convolution
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem sq_integral_Ioc_zero_one_le_integral_sq {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ s in Set.Ioc (0 : ℝ) 1, g s)^2 ≤ ∫ s in Set.Ioc (0 : ℝ) 1, (g s)^2 := by
  let : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  have hConv : ConvexOn ℝ Set.univ (fun t : ℝ => t^2) := (by norm_num : Even (2 : ℕ)).convexOn_pow
  exact hConv.map_integral_le (continuous_id.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    (hg.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    ((hg.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)

theorem smooth_translation_sub_eq_integral {n : ℕ} {w : Point n → ℝ}
    (hw : ContDiff ℝ 1 w) (p v : Point n) :
    w (p+v)-w p = ∫ s in Set.Ioc (0 : ℝ) 1, fderiv ℝ w (p+s • v) v := by
  have hDeriv (s : ℝ) : HasDerivAt (fun t : ℝ => w (p+t • v)) (fderiv ℝ w (p+s • v) v) s := by
    have hLine : HasDerivAt (fun t : ℝ => p+t • v) v s := by
      convert! ((hasDerivAt_id s).smul_const v).const_add p using 1
      simp only [one_smul]
    exact (hw.differentiable one_ne_zero (p+s • v)).hasFDerivAt.comp_hasDerivAt s hLine
  have hCont : Continuous (fun s : ℝ => fderiv ℝ w (p+s • v) v) :=
    ((hw.continuous_fderiv one_ne_zero).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hDeriv s) (hCont.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  simpa only [zero_smul,one_smul,add_zero] using h.symm

theorem integrable_translation_path {n : ℕ} {g : Point n → ℝ}
    (hg : Continuous g) (hgi : Integrable g volume) (v : Point n) :
    Integrable (fun q : ℝ × Point n => g (q.2+q.1 • v))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod volume) := by
  let : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  have hCont : Continuous (fun q : ℝ × Point n => g (q.2+q.1 • v)) :=
    hg.comp (continuous_snd.add (continuous_fst.smul continuous_const))
  apply (integrable_prod_iff hCont.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (fun s => hgi.comp_add_right (s • v)),?_⟩
  have hEq : (fun s : ℝ => ∫ p, ‖g (p+s • v)‖) = fun _ => ∫ p, ‖g p‖ := by
    funext s
    exact integral_add_right_eq_self (μ := volume) (fun p : Point n => ‖g p‖) (s • v)
  rw [hEq]
  exact integrable_const _

theorem integral_sq_translation_average_le {n : ℕ} {g : Point n → ℝ}
    (hg : Continuous g) (hgi : Integrable g volume) (hg2 : Integrable (fun p => (g p)^2) volume)
    (v : Point n) :
    Integrable (fun p => (∫ s in Set.Ioc (0 : ℝ) 1, g (p+s • v))^2) volume ∧
      (∫ p, (∫ s in Set.Ioc (0 : ℝ) 1, g (p+s • v))^2) ≤ ∫ p, (g p)^2 := by
  let : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  have hJ := integrable_translation_path hg hgi v
  have hJ2 := integrable_translation_path (g := fun p => (g p)^2) (hg.pow 2) hg2 v
  have hI := hJ.integral_prod_right
  have hI2 := hJ2.integral_prod_right
  have hBound (p : Point n) : (∫ s in Set.Ioc (0 : ℝ) 1, g (p+s • v))^2 ≤
      ∫ s in Set.Ioc (0 : ℝ) 1, (g (p+s • v))^2 :=
    sq_integral_Ioc_zero_one_le_integral_sq (hg.comp (continuous_const.add (continuous_id.smul continuous_const)))
  have hAvg : Integrable (fun p => (∫ s in Set.Ioc (0 : ℝ) 1, g (p+s • v))^2) volume :=
    hI2.mono' (hI.aestronglyMeasurable.pow 2) (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hBound p)
  refine ⟨hAvg,(integral_mono hAvg hI2 hBound).trans_eq ?_⟩
  rw [← integral_prod_symm _ hJ2,integral_prod _ hJ2]
  simp_rw [integral_add_right_eq_self (fun p : Point n => (g p)^2)]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,smul_eq_mul,one_mul]

theorem smooth_translation_sub_L2_bound {n : ℕ} {w : Point n → ℝ}
    (hw : ContDiff ℝ 1 w) (hcw : HasCompactSupport w) (v : Point n) :
    Integrable (fun p => (w (p+v)-w p)^2) volume ∧
      (∫ p, (w (p+v)-w p)^2) ≤ ∫ p, (fderiv ℝ w p v)^2 := by
  let g : Point n → ℝ := fun p => fderiv ℝ w p v
  have hg : Continuous g := (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcg : HasCompactSupport g := hcw.fderiv_apply ℝ v
  have hcg2 : HasCompactSupport (fun p => (g p)^2) := by
    have h : HasCompactSupport (fun p => g p*g p) := hcg.mul_right
    simpa only [pow_two] using h
  have h := integral_sq_translation_average_le hg (hg.integrable_of_hasCompactSupport hcg)
    ((hg.pow 2).integrable_of_hasCompactSupport hcg2) v
  simp only [g] at h
  simp_rw [← smooth_translation_sub_eq_integral hw] at h
  exact h

theorem memLp_translation_sub {n : ℕ} {u : Point n → ℝ} (hu : MemLp u 2 volume) (v : Point n) :
    MemLp (fun p => u (p+v)-u p) 2 volume := by
  have hTrans : MemLp (fun p => u (p+v)) 2 volume :=
    hu.comp_measurePreserving (measurePreserving_add_right volume v)
  exact hTrans.sub hu

theorem L2_tendsto_translation_sub {n : ℕ} {f : ℕ → Point n → ℝ} {u : Point n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 volume) (hu : MemLp u 2 volume)
    (hLim : Tendsto (fun k => ∫ p, (f k p-u p)^2) atTop (𝓝 0)) (v : Point n) :
    Tendsto (fun k => ∫ p, ((f k (p+v)-f k p)-(u (p+v)-u p))^2) atTop (𝓝 0) := by
  have hBound (k : ℕ) : (∫ p, ((f k (p+v)-f k p)-(u (p+v)-u p))^2) ≤
      4*(∫ p, (f k p-u p)^2) := by
    have hE : MemLp (fun p => f k p-u p) 2 volume := (hf k).sub hu
    have hE2 : Integrable (fun p => (f k p-u p)^2) volume := by
      have h := (memLp_two_iff_integrable_sq_norm hE.aestronglyMeasurable).mp hE
      simpa only [Real.norm_eq_abs,sq_abs] using h
    have hT2 : Integrable (fun p => (f k (p+v)-u (p+v))^2) volume := hE2.comp_add_right v
    have hD : MemLp (fun p => (f k (p+v)-f k p)-(u (p+v)-u p)) 2 volume :=
      (memLp_translation_sub (hf k) v).sub (memLp_translation_sub hu v)
    have hD2 : Integrable (fun p => ((f k (p+v)-f k p)-(u (p+v)-u p))^2) volume := by
      have h := (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).mp hD
      simpa only [Real.norm_eq_abs,sq_abs] using h
    calc
      _ ≤ ∫ p, 2*(f k (p+v)-u (p+v))^2+2*(f k p-u p)^2 := by
        apply integral_mono hD2 ((hT2.const_mul 2).add (hE2.const_mul 2))
        intro p
        dsimp only [Pi.add_apply]
        nlinarith [sq_nonneg ((f k (p+v)-u (p+v))+(f k p-u p))]
      _ = _ := by
        rw [integral_add (hT2.const_mul 2) (hE2.const_mul 2),integral_const_mul,integral_const_mul]
        have hEq := integral_add_right_eq_self (μ := volume) (fun p : Point n => (f k p-u p)^2) v
        rw [hEq]
        ring
  exact squeeze_zero (fun k => integral_nonneg (fun p => sq_nonneg _)) hBound
    (by simpa only [mul_zero] using hLim.const_mul 4)

theorem integral_sq_translation_sub_tendsto {n : ℕ} {f : ℕ → Point n → ℝ} {u : Point n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 volume) (hu : MemLp u 2 volume)
    (hLim : Tendsto (fun k => ∫ p, (f k p-u p)^2) atTop (𝓝 0)) (v : Point n) :
    Tendsto (fun k => ∫ p, (f k (p+v)-f k p)^2) atTop (𝓝 (∫ p, (u (p+v)-u p)^2)) := by
  have hE := L2_tendsto_translation_sub hf hu hLim v
  have hENorm : Tendsto (fun k => ∫ p, ‖(f k (p+v)-f k p)-(u (p+v)-u p)‖^2) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hE
  have h := tendsto_integral_weighted_mul_of_L2 (fun k => memLp_translation_sub (hf k) v)
    (fun k => memLp_translation_sub (hf k) v) (memLp_translation_sub hu v) (memLp_translation_sub hu v)
    (memLp_top_const_enorm (c := (1 : ℝ)) (by simp)) hENorm hENorm
  simpa only [one_mul,pow_two] using h

theorem weakGradient_translation_sub_L2_bound {n : ℕ}
    {w : Point n → ℝ} {H : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 volume) (hcw : HasCompactSupport w)
    (hGrad : WeakGradient Set.univ Set.univ w H) (i : Yau.RIdx n)
    (hHi : MemLp (fun p => H p i) 2 volume) (hcHi : HasCompactSupport (fun p => H p i)) (h : ℝ) :
    (∫ p, (w (p+(h • Yau.realVec i,0))-w p)^2) ≤ h^2*(∫ p, (H p i)^2) := by
  let ε : ℕ → ℝ := fun k => (1/2 : ℝ)^k
  have hε (k : ℕ) : 0 < ε k := pow_pos (by norm_num) k
  have hε1 (k : ℕ) : ε k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let wk : ℕ → Point n → ℝ := fun k => jointMollify (ε k) w
  have hw1 := Yau.LeafProofs.L03.memLp_two_compact_integrable volume w hw hcw
  have hwk (k : ℕ) : MemLp (wk k) 2 volume := jointMollify_memLp (hε k) hw hcw
  have hwSmooth (k : ℕ) : ContDiff ℝ ∞ (wk k) := jointMollify_smooth (hε k) hw1
  have hcwk (k : ℕ) : HasCompactSupport (wk k) :=
    (jointMollifierScaled_compact (hε k)).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcw
  have hD (k : ℕ) (p : Point n) : fderiv ℝ (wk k) p (h • Yau.realVec i,0) =
      h*jointMollify (ε k) (fun q => H q i) p := by
    have hv : (h • Yau.realVec i,(0 : ℝ)) = h • (Yau.realVec i,(0 : ℝ)) := by
      simp only [Prod.smul_mk,smul_zero]
    rw [hv,map_smul,smul_eq_mul]
    congr 1
    exact (d_eq_joint_fderiv ((hwSmooth k).differentiable (by simp) p) i).symm.trans
      (weakGradient_jointMollify_spatial (hε k) hw1 hGrad p i)
  have hBound (k : ℕ) : (∫ p, (wk k (p+(h • Yau.realVec i,0))-wk k p)^2) ≤
      h^2*(∫ p, (H p i)^2) := by
    have hB := (smooth_translation_sub_L2_bound ((hwSmooth k).of_le (by simp)) (hcwk k)
      (h • Yau.realVec i,0)).2
    simp_rw [hD k,mul_pow] at hB
    rw [integral_const_mul] at hB
    have hC : (∫ p, (jointMollify (ε k) (fun q => H q i) p)^2) ≤ ∫ p, (H p i)^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using jointMollify_L2_contract (hε k) hHi hcHi
    exact hB.trans (mul_le_mul_of_nonneg_left hC (sq_nonneg h))
  have hNormLim := jointMollify_L2_tendsto hε hε1 hεlim hw hcw
  have hRawLim : Tendsto (fun k => ∫ p, (wk k p-w p)^2) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hNormLim
  exact le_of_tendsto (integral_sq_translation_sub_tendsto hwk hw hRawLim (h • Yau.realVec i,0))
    (Filter.Eventually.of_forall hBound)

theorem weakGradient_spatialDifferenceQuotient_L2_bound {n : ℕ}
    {w : Point n → ℝ} {H : Point n → Yau.RIdx n → ℝ}
    (hw : MemLp w 2 volume) (hcw : HasCompactSupport w)
    (hGrad : WeakGradient Set.univ Set.univ w H) (i : Yau.RIdx n)
    (hHi : MemLp (fun p => H p i) 2 volume) (hcHi : HasCompactSupport (fun p => H p i))
    {h : ℝ} (hh : h ≠ 0) :
    MemLp (spatialDifferenceQuotient w (Yau.realVec i) h) 2 volume ∧
      (∫ p, (spatialDifferenceQuotient w (Yau.realVec i) h p)^2) ≤ ∫ p, (H p i)^2 := by
  have hEq (p : Point n) : spatialDifferenceQuotient w (Yau.realVec i) h p =
      h⁻¹*(w (p+(h • Yau.realVec i,0))-w p) := by
    simp only [spatialDifferenceQuotient,smul_eq_mul,Prod.add_def,add_zero]
  have hDQ : MemLp (spatialDifferenceQuotient w (Yau.realVec i) h) 2 volume := by
    convert! (memLp_translation_sub hw (h • Yau.realVec i,0)).const_mul h⁻¹ using 1
    ext p
    exact hEq p
  refine ⟨hDQ,?_⟩
  have hB := mul_le_mul_of_nonneg_left
    (weakGradient_translation_sub_L2_bound hw hcw hGrad i hHi hcHi h) (sq_nonneg h⁻¹)
  have hInt : (∫ p, (spatialDifferenceQuotient w (Yau.realVec i) h p)^2) =
      (h⁻¹)^2*(∫ p, (w (p+(h • Yau.realVec i,0))-w p)^2) := by
    simp_rw [hEq,mul_pow]
    rw [integral_const_mul]
  rw [hInt]
  simpa only [← mul_assoc,← mul_pow,inv_mul_cancel₀ hh,one_pow,one_mul] using hB

theorem localEnergy_cutoff_spatialDifferenceQuotient_L2_bound {n : ℕ}
    {O : Set (Space n)} {l r : ℝ} (hO : IsOpen O)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G) {η : Point n → ℝ}
    (hη : Test (O ×ˢ Set.Ioo l r) η) (i : Yau.RIdx n) {h : ℝ} (hh : h ≠ 0) :
    MemLp (spatialDifferenceQuotient (fun p => η p*u p) (Yau.realVec i) h) 2 volume ∧
      (∫ p, (spatialDifferenceQuotient (fun q => η q*u q) (Yau.realVec i) h p)^2) ≤
        ∫ p, (η p*G p i+u p*d (fun x => η (x,p.2)) p.1 i)^2 := by
  obtain ⟨hw,hH,hGrad⟩ := localEnergy_cutoff_weakH1 hO hE hη
  exact weakGradient_spatialDifferenceQuotient_L2_bound hw hη.2.1.mul_right hGrad i (hH i)
    (hη.2.1.mul_right.add (test_spatialDerivative hη i).2.1.mul_left) hh

end Yau.LeafProofs.L16Aux
