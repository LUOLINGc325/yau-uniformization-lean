import Yau.Proofs.F01LeviChartNaturality
import Yau.Proofs.F01SpatialLeviJetLimit

/-! Local second jets in one retained chart determine the native Levi
limit. Ambient value extensions need smoothness only near the queried
point, and finitely many non-smooth sequence members are harmless. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem local_holomorphic_chart_second_data
    (f : M.Carrier → ℝ) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source)
    (hf : ContDiffAt ℝ 2 (inChart (e z) f) (chartPt (e z) (e z))) :
    ContDiffAt ℝ 2 (fun w => f (e w)) z ∧
      leviC (fun w => f (e w)) z =
        (linearMatrix (coordinateDifferential e (e z) z))ᴴ *
          levi f (e z) * linearMatrix (coordinateDifferential e (e z) z) := by
  let a := e z
  let T : ComplexVector n → ComplexVector n := fun w => chartPt a (e w)
  have ha : e z ∈ (extChartAt (ComplexModel n) a).source := mem_extChartAt_source a
  have hzD : z ∈ forwardChartDomain e a := ⟨hz, ha⟩
  have hT : ContDiffAt ℂ 2 T z := ((forwardChart_contDiffOn e he a).contDiffAt
    ((forwardChartDomain_isOpen e a).mem_nhds hzD)).of_le (by simp)
  have hfa : ContDiffAt ℝ 2 (inChart a f) (T z) := hf
  have hgerm : (fun w => f (e w)) =ᶠ[𝓝 z] (inChart a f ∘ T) := by
    filter_upwards [(forwardChartDomain_isOpen e a).mem_nhds hzD] with w hw
    exact (congrArg f ((extChartAt (ComplexModel n) a).left_inv hw.2)).symm
  refine ⟨(hfa.comp z (hT.restrict_scalars ℝ)).congr_of_eventuallyEq hgerm, ?_⟩
  rw [Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq hgerm, leviC_comp hT hfa,
    ← coordinateDifferential_eq_fderiv e he a hz ha]
  rfl

theorem eventual_spatial_levi_limit_of_second_jets
    (f : ℕ → ComplexVector n → ℝ) (u : ComplexVector n → ℝ) (z : ComplexVector n)
    (hf : ∀ᶠ m in atTop, ContDiffAt ℝ 2 (f m) z) (hu : ContDiffAt ℝ 2 u z)
    (hJet : Tendsto (fun m => iteratedFDeriv ℝ 2 (f m) z) atTop
      (𝓝 (iteratedFDeriv ℝ 2 u z))) :
    Tendsto (fun m => leviC (f m) z) atTop (𝓝 (leviC u z)) := by
  classical
  let g : ℕ → ComplexVector n → ℝ := fun m => if ContDiffAt ℝ 2 (f m) z then f m else u
  have hg (m : ℕ) : ContDiffAt ℝ 2 (g m) z := by
    dsimp only [g]
    split_ifs with hm
    · exact hm
    · exact hu
  have heq : ∀ᶠ m in atTop, g m = f m := hf.mono (fun m hm => by simp only [g, if_pos hm])
  have hgJet : Tendsto (fun m => iteratedFDeriv ℝ 2 (g m) z) atTop
      (𝓝 (iteratedFDeriv ℝ 2 u z)) :=
    hJet.congr' (heq.mono (fun m hm => congrArg (fun q => iteratedFDeriv ℝ 2 q z) hm.symm))
  have hLevi : Tendsto (fun m => leviC (g m) z) atTop (𝓝 (leviC u z)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact spatial_levi_entry_limit_of_second_jets g u z hg hu hgJet i j
  exact hLevi.congr' (heq.mono (fun m hm => congrArg (fun q => leviC q z) hm))

theorem native_levi_limit_of_local_chart_second_jets
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source)
    (f : ℕ → M.Carrier → ℝ) (u : M.Carrier → ℝ)
    (hf : ∀ᶠ m in atTop, ContDiffAt ℝ 2 (inChart (e z) (f m)) (chartPt (e z) (e z)))
    (hu : ContDiffAt ℝ 2 (inChart (e z) u) (chartPt (e z) (e z)))
    (hJet : Tendsto (fun m => iteratedFDeriv ℝ 2 (fun w => f m (e w)) z) atTop
      (𝓝 (iteratedFDeriv ℝ 2 (fun w => u (e w)) z))) :
    Tendsto (fun m => levi (f m) (e z)) atTop (𝓝 (levi u (e z))) := by
  have hChart := eventual_spatial_levi_limit_of_second_jets
    (fun m w => f m (e w)) (fun w => u (e w)) z
    (hf.mono (fun m hm => (local_holomorphic_chart_second_data (f m) e he hz hm).1))
    (local_holomorphic_chart_second_data u e he hz hu).1 hJet
  let J := linearMatrix (coordinateDifferential e (e z) z)
  have hDet : J.det ≠ 0 := linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e he hei (e z) hz (mem_extChartAt_source (e z)))
  have hInv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J (isUnit_iff_ne_zero.mpr hDet)
  have hStar : (J⁻¹)ᴴ * Jᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hInv, Matrix.conjTranspose_one]
  have hRecover (q : M.Carrier → ℝ)
      (hq : ContDiffAt ℝ 2 (inChart (e z) q) (chartPt (e z) (e z))) :
      (J⁻¹)ᴴ * leviC (fun w => q (e w)) z * J⁻¹ = levi q (e z) := by
    rw [(local_holomorphic_chart_second_data q e he hz hq).2]
    change (J⁻¹)ᴴ * (Jᴴ * levi q (e z) * J) * J⁻¹ = _
    calc
      _ = ((J⁻¹)ᴴ * Jᴴ) * levi q (e z) * (J * J⁻¹) := by noncomm_ring
      _ = _ := by rw [hStar, hInv]; simp
  have hLimit : Tendsto (fun m => (J⁻¹)ᴴ * leviC (fun w => f m (e w)) z * J⁻¹) atTop
      (𝓝 ((J⁻¹)ᴴ * leviC (fun w => u (e w)) z * J⁻¹)) :=
    (tendsto_const_nhds.mul hChart).mul tendsto_const_nhds
  rw [hRecover u hu] at hLimit
  exact hLimit.congr' (hf.mono (fun m hm => hRecover (f m) hm))

end Yau.NodeProofs.F01Aux
