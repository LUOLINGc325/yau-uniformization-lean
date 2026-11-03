import Yau.LeafProofs.L05ABPBuffer
import Yau.LeafProofs.L05ABPSourceLimit

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem viscosity_abp_interior_power {n : ℕ} {ell L : ℝ}
    (hell : 0<ell) (hL : ell≤L) {v g : Point n → ℝ}
    (hv : ContinuousOn v (unitClosed n)) (hg : ContinuousOn g (unitClosed n))
    (hboundary : ∀ z∈parabolicBoundary n, v z≤0)
    (hsub : viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) g v)
    {z0 : Point n} (hz0 : z0∈unitOpen n) :
    abpKappa n*(max (v z0) 0)^(2*n+1)≤
      ((ell/2)⁻¹)^(2*n)*∫ z in unitOpen n, (max (g z) 0)^(2*n+1) := by
  obtain ⟨f,hf,heq,M,hM,hb⟩ := abp_bounded_uniform_extension hv
  have hD : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have hucv := hD.uniformContinuousOn_of_continuous hv
  have hucg := hD.uniformContinuousOn_of_continuous hg
  have hx : 0<1-‖z0.1‖ := by
    have hh : ‖z0.1‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz0.1
    linarith
  have ha : 0<z0.2+1 := by linarith [hz0.2.1]
  have ht : 0< -z0.2 := by linarith [hz0.2.2]
  have herr (eta : ℝ) (heta : 0<eta) :
      abpKappa n*(max (v z0-3*eta) 0)^(2*n+1)≤
        ((ell/2)⁻¹)^(2*n)*∫ z in unitOpen n, (max (g z+eta) 0)^(2*n+1) := by
    obtain ⟨rv,hrv,hvmod⟩ := Metric.uniformContinuousOn_iff.mp hucv eta heta
    obtain ⟨rg,hrg,hgmod⟩ := Metric.uniformContinuousOn_iff.mp hucg eta heta
    let A := min (1/4) (min rv (min rg (min (1-‖z0.1‖) (min (z0.2+1) (-z0.2)))))
    have hA : 0<A := by dsimp only [A]; positivity
    obtain ⟨rho,hrho,hra⟩ := exists_between hA
    have hrs : rho<1/4 ∧ rho<rv ∧ rho<rg ∧ rho<1-‖z0.1‖ ∧ rho<z0.2+1 ∧ rho< -z0.2 := by
      simpa only [A,lt_min_iff] using hra
    obtain ⟨e0,he0,happ⟩ := lasryLions_uniformApprox hf hM hb eta heta
    have hE : 0 < min e0 (rho^2/(64*M)) := by positivity
    obtain ⟨epsilon,hepsilon,heps⟩ := exists_between hE
    have heps0 : epsilon<e0 := heps.trans_le (min_le_left _ _)
    have heps1 : 64*M*epsilon<rho^2 := by
      have hh := (lt_div_iff₀ (by positivity : 0<64*M)).mp (heps.trans_le (min_le_right _ _))
      nlinarith
    have hmodv : ∀ z∈unitClosed n, ∀ q∈unitClosed n, dist z q≤rho → |v z-v q|≤eta := by
      intro z hz q hq hdist
      have hh := hvmod z hz q hq (hdist.trans_lt hrs.2.1)
      exact (show |v z-v q|<eta by simpa only [Real.dist_eq] using hh).le
    have hmodg : ∀ z∈unitClosed n, ∀ q∈unitClosed n, dist q z<rho → |g q-g z|≤eta := by
      intro z hz q hq hdist
      have hh := hgmod q hq z hz (hdist.trans hrs.2.2.1)
      exact (show |g q-g z|<eta by simpa only [Real.dist_eq] using hh).le
    have happ' : ∀ z∈unitClosed n,
        |spatialInfRegularize (epsilon/2) (supRegularize epsilon f) z-v z|≤eta := by
      intro z hz
      rw [←heq hz]
      exact (happ epsilon hepsilon heps0 z).le
    have hzbuf : z0∈abpClosed n (1-rho) (-1+rho) (-rho) := by
      refine ⟨?_,?_,?_⟩
      · simpa only [Metric.mem_closedBall,dist_zero_right] using
          (show ‖z0.1‖≤1-rho by linarith [hrs.2.2.2.1])
      · linarith [hrs.2.2.2.2.1]
      · linarith [hrs.2.2.2.2.2]
    have hi := lasryLions_buffer_abp_power hf.continuous hM.le hb hepsilon hell hL hrho hrs.1
      heps1 heta.le heq hg hboundary hsub hmodv hmodg happ' hzbuf
    have hlow := (abs_le.mp (happ' z0 (unitOpen_subset_unitClosed hz0))).1
    have hmax : max (v z0-3*eta) 0≤
        max (spatialInfRegularize (epsilon/2) (supRegularize epsilon f) z0-2*eta) 0 :=
      max_le_max (by linarith) le_rfl
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right _ _) hmax _) (abpKappa_pos n).le).trans hi
  let eta : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have heta (j : ℕ) : 0<eta j := by dsimp only [eta]; positivity
  have he0 : Tendsto eta atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hleft : Tendsto (fun j => abpKappa n*(max (v z0-3*eta j) 0)^(2*n+1))
      atTop (𝓝 (abpKappa n*(max (v z0) 0)^(2*n+1))) := by
    have ht := (((tendsto_const_nhds (x := v z0)).sub (he0.const_mul 3)).max
      (tendsto_const_nhds (x := (0:ℝ)))).pow (2*n+1)
    simpa only [mul_zero,sub_zero] using ht.const_mul (abpKappa n)
  have hright := (abp_source_shift_integral_tendsto hg).const_mul (((ell/2)⁻¹)^(2*n))
  exact le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall (fun j => herr (eta j) (heta j)))

theorem viscosity_abp_interior {n : ℕ} {ell L : ℝ}
    (hell : 0<ell) (hL : ell≤L) {v g : Point n → ℝ}
    (hv : ContinuousOn v (unitClosed n)) (hg : ContinuousOn g (unitClosed n))
    (hboundary : ∀ z∈parabolicBoundary n, v z≤0)
    (hsub : viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) g v)
    {z0 : Point n} (hz0 : z0∈unitOpen n) :
    v z0≤abpC n ell*(∫ z in unitOpen n, (max (g z) 0)^(2*n+1))^(1/((2*n+1 : ℕ):ℝ)) := by
  let I := ∫ z in unitOpen n, (max (g z) 0)^(2*n+1)
  let A := (abpKappa n)⁻¹*((ell/2)⁻¹)^(2*n)
  have hi := viscosity_abp_interior_power hell hL hv hg hboundary hsub hz0
  have hi' : (max (v z0) 0)^(2*n+1)≤A*I := by
    have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (abpKappa_pos n).le)
    rw [←mul_assoc,inv_mul_cancel₀ (abpKappa_pos n).ne',one_mul] at hh
    simpa only [A,I,mul_assoc] using hh
  have hI : 0≤I := integral_nonneg (fun z => pow_nonneg (le_max_right _ _) _)
  have hA : 0≤A := mul_nonneg (inv_nonneg.mpr (abpKappa_pos n).le)
    (pow_nonneg (inv_nonneg.mpr (by positivity : 0≤ell/2)) _)
  have hroot := abp_root_of_power (by omega : 0<2*n+1) (le_max_right _ _) hA hI hi'
  have hcoef : 1+A=abpC n ell := by
    dsimp only [A,abpC]
    congr 2
    congr 1
    field_simp
  rw [hcoef] at hroot
  exact (le_max_left _ _).trans hroot

end Yau.LeafProofs.L05Aux
