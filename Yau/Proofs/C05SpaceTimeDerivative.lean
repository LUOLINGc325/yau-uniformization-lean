import Yau.Proofs.C05LeviTimeDerivative
import Yau.Blueprint.Nodes
import Yau.Proofs.C04Scaling

/-! Joint time differentiation and the actual spatial Levi matrix commute on
an open time interval, in each fixed chart. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Set Filter
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_timeDeriv {u : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hu : SmoothSpaceTime u I) : SmoothSpaceTime (timeDeriv u) I := by
  intro x
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv x p.1) p.2
  have hO : IsOpen (chartTarget x ×ˢ I) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod hI
  have hc : ContDiffOn ℝ ∞ F (chartTarget x ×ˢ I) := hu x
  have he : ∀ p ∈ chartTarget x ×ˢ I,
      timeDeriv u (chartInv x p.1) p.2 = fderiv ℝ F p (0, 1) := by
    intro p hp
    have hd := (hc.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
    exact (right_hasDerivAt hd).deriv
  have hdc : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (0, 1)) (chartTarget x ×ˢ I) :=
    (hc.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  exact hdc.congr he

theorem hasDerivAt_levi_of_smoothSpaceTime {u : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hu : SmoothSpaceTime u I) (x : M.Carrier) {t : ℝ} (ht : t ∈ I)
    (a b : Fin n) :
    HasDerivAt (fun s => levi (fun y => u y s) x a b)
      (levi (fun y => timeDeriv u y t) x a b) t := by
  let z := chartPt x x
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv x p.1) p.2
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hO : IsOpen (chartTarget x ×ˢ I) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod hI
  have hF : ContDiffOn ℝ ∞ F (chartTarget x ×ˢ I) := hu x
  have hFat (w : ComplexVector n) (hw : w ∈ chartTarget x) :
      ContDiffAt ℝ ∞ F (w, t) := hF.contDiffAt (hO.mem_nhds ⟨hw, ht⟩)
  have he : (fun w => directionalDerivative (0, 1) F (w, t)) =ᶠ[𝓝 z]
      inChart x (fun y => timeDeriv u y t) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz]
      with w hw
    exact (right_hasDerivAt ((hFat w hw).differentiableAt (by simp))).deriv.symm
  have hlevi := hasDerivAt_leviC_spaceTime ((hFat z hz).of_le (by norm_num)) a b
  rw [Yau.Proofs.C04Aux.leviC_congr_nhds he] at hlevi
  exact hlevi

end Yau.Proofs.C05Aux
