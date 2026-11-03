import Yau.Proofs.C05LeviTimeDerivative
import Yau.Proofs.C05FlowRegularity
import Yau.Proofs.F04Source

/-! The actual Ricci time derivative is the Levi Hessian of the actual scalar
curvature. This follows from the original rho identity, in one fixed chart. -/

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder

namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux Set Filter
variable {n : ℕ} {X : KahlerManifold n}

theorem ricci_hasDerivAt_scalar_levi (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (a b : Fin n) :
    HasDerivAt (fun s => ricci (h s) x a b) (levi (scalarCurvature (h t)) x a b) t := by
  let z := chartPt x x
  let F : ComplexVector n × ℝ → ℝ := fun p => ρ (chartInv x p.1) p.2
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hO : IsOpen (chartTarget x ×ˢ Ioi (0 : ℝ)) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi
  have hF : ContDiffOn ℝ ∞ F (chartTarget x ×ˢ Ioi 0) :=
    (hf.2.2.2.1 x).mono (prod_mono_right Ioi_subset_Ici_self)
  have hFat (w : ComplexVector n) (hw : w ∈ chartTarget x) :
      ContDiffAt ℝ ∞ F (w, t) := hF.contDiffAt (hO.mem_nhds ⟨hw, ht⟩)
  have he : (fun w => directionalDerivative (0, 1) F (w, t)) =ᶠ[𝓝 z]
      inChart x (scalarCurvature (h t)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz]
      with w hw
    have hd := right_hasDerivAt ((hFat w hw).differentiableAt (by simp))
    exact hd.unique (rho_hasDerivAt X o h U P ρ hf (chartInv x w) ht)
  have hlevi := hasDerivAt_leviC_spaceTime ((hFat z hz).of_le (by norm_num)) a b
  rw [leviC_congr_nhds he] at hlevi
  change HasDerivAt (fun s => levi (fun y => ρ y s) x a b)
    (levi (scalarCurvature (h t)) x a b) t at hlevi
  have hsum := (hasDerivAt_const t (ricci X.metric.form x a b)).add hlevi
  have hricci : (fun s => ricci (h s) x a b) =ᶠ[𝓝 t]
      (fun s => ricci X.metric.form x a b + levi (fun y => ρ y s) x a b) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact congrArg (fun A => A a b) (Yau.F04Proof.ricci_flow_identity o h U P ρ hf x s hs.le)
  simpa only [zero_add] using hsum.congr_of_eventuallyEq hricci

theorem ricci_time_derivative_matrix (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    Matrix.of (fun a b => deriv (fun s => ricci (h s) x a b) t) =
      levi (scalarCurvature (h t)) x := by
  ext a b
  exact (ricci_hasDerivAt_scalar_levi o h U P ρ hf x ht a b).deriv

theorem tensorHarnack_scalar_levi (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    (levi (scalarCurvature (h t)) x +
      ricci (h t) x * (gMat (h t) x)⁻¹ * ricci (h t) x +
        ((t⁻¹ : ℝ) : ℂ) • ricci (h t) x).PosSemidef := by
  have hm := hH.2.2.2.1 x t ht
  rwa [ricci_time_derivative_matrix o h U P ρ hf x ht] at hm

end Yau.Proofs.C05Aux
