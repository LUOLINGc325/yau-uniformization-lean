import Yau.LeafProofs.L17AtlasCutoffs
import Yau.LeafProofs.L17SmallTranslation

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapPatchAux
open L17Aux L17SmallTranslationAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

structure BootstrapPatch (P : UniformChartPartition g) (x : M.Carrier) where
  center : P.centers
  coord : ComplexVector n
  radius : ℝ
  bump : ComplexVector n → ℝ
  bound : ℝ
  center_eq : P.charts.chart center coord=x
  coord_mem : coord∈ball (0 : ComplexVector n) (P.radius/4)
  radius_pos : 0<radius
  bump_smooth : ContDiff ℝ ∞ bump
  bump_range : ∀ z,bump z∈Icc (0:ℝ) 1
  bump_one : ∀ z∈closedBall coord radius,bump z=1
  bump_support : tsupport bump⊆closedBall coord (2*radius)
  collar_mem : closedBall coord (3*radius)⊆ball (0 : ComplexVector n) (P.radius/4)
  bound_ge_one : 1 ≤ bound
  low_jet_bound : ∀ j ≤ 3,∀ z,‖iteratedFDeriv ℝ j bump z‖ ≤ bound
  derivative_bound : ∀ z,‖fderiv ℝ bump z‖ ≤ bound
  all_jet_bounds : ∀ k:ℕ,∃ C:ℝ,0 ≤ C ∧ ∀ j ≤ k,∀ z,‖iteratedFDeriv ℝ j bump z‖ ≤ C

theorem exists_bootstrapPatch (P : UniformChartPartition g) (x : M.Carrier) :
    Nonempty (BootstrapPatch P x) := by
  obtain ⟨p,hp,z0,hz0,hzx⟩ := P.covers x
  let r := (P.radius/4-‖z0‖)/8
  have hzNorm : ‖z0‖<P.radius/4 := by simpa only [mem_ball,dist_zero_right] using hz0
  have hr : 0<r := div_pos (sub_pos.mpr hzNorm) (by norm_num)
  let f : ContDiffBump z0 := ⟨r,2*r,hr,by linarith⟩
  let χ : ComplexVector n → ℝ := f
  have hχ : ContDiff ℝ ∞ χ := f.contDiff
  have hc : HasCompactSupport χ := f.hasCompactSupport
  obtain ⟨C,hC,hBound⟩ := hc.exists_bound_iteratedFDeriv hχ 3
  let L := max (1:ℝ) C
  have hL : 1 ≤ L := le_max_left _ _
  have hDf (z : ComplexVector n) : ‖fderiv ℝ χ z‖ ≤ L := by
    have h := hBound 1 (by omega) z
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (le_max_right _ _)
  have hCollar : closedBall z0 (3*r)⊆ball (0 : ComplexVector n) (P.radius/4) := by
    intro z hz
    have hDist : ‖z-z0‖ ≤ 3*r := mem_closedBall_iff_norm.mp hz
    have hNorm : ‖z‖ ≤ ‖z-z0‖+‖z0‖ := by
      calc
        ‖z‖=‖(z-z0)+z0‖ := by rw [sub_add_cancel]
        _ ≤ ‖z-z0‖+‖z0‖ := norm_add_le _ _
    rw [mem_ball,dist_zero_right]
    dsimp only [r] at hDist
    linarith
  refine ⟨{
    center := ⟨p,hp⟩
    coord := z0
    radius := r
    bump := χ
    bound := L
    center_eq := hzx
    coord_mem := hz0
    radius_pos := hr
    bump_smooth := hχ
    bump_range := fun z => ⟨f.nonneg,f.le_one⟩
    bump_one := fun z hz => f.one_of_mem_closedBall hz
    bump_support := ?_
    collar_mem := hCollar
    bound_ge_one := hL
    low_jet_bound := fun j hj z => (hBound j hj z).trans (le_max_right _ _)
    derivative_bound := hDf
    all_jet_bounds := fun k => hc.exists_bound_iteratedFDeriv hχ k }⟩
  change tsupport (f : ComplexVector n → ℝ)⊆closedBall z0 (2*r)
  simpa only [f.tsupport_eq] using (subset_rfl : closedBall z0 (2*r)⊆closedBall z0 (2*r))

namespace BootstrapPatch
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)

def scaledJetBudget : ℝ :=
  1+P.radius*D.bound+P.radius^2*D.bound+P.radius^3*D.bound

theorem scaledJetBudget_ge_one : 1 ≤ D.scaledJetBudget := by
  have hr := P.radius_pos.le
  have hB := zero_le_one.trans D.bound_ge_one
  have hs : 0 ≤ P.radius*D.bound+P.radius^2*D.bound+P.radius^3*D.bound := by positivity
  unfold scaledJetBudget
  linarith

def smallRadius : ℝ := min (smallTranslationRadius D.bound/2) (P.radius/(8*D.scaledJetBudget))

theorem smallRadius_pos : 0<D.smallRadius := by
  have hs := smallTranslationRadius_pos (zero_le_one.trans D.bound_ge_one)
  have hb := zero_lt_one.trans_le D.scaledJetBudget_ge_one
  unfold smallRadius
  exact lt_min (by positivity) (by have := P.radius_pos; positivity)

theorem smallRadius_le_translation : D.smallRadius ≤ smallTranslationRadius D.bound := by
  have hs := smallTranslationRadius_pos (zero_le_one.trans D.bound_ge_one)
  exact (min_le_left _ _).trans (by linarith)

theorem smallRadius_le_radius : D.smallRadius ≤ P.radius := by
  have hb := D.scaledJetBudget_ge_one
  have hbpos := zero_lt_one.trans_le hb
  apply (min_le_right _ _).trans
  apply (div_le_iff₀ (by positivity : 0<(8:ℝ)*D.scaledJetBudget)).mpr
  have hr := P.radius_pos.le
  nlinarith

theorem bump_support_source : tsupport D.bump⊆(P.charts.chart D.center).source := by
  intro z h
  have hClosed := D.bump_support h
  have h3 : z∈closedBall D.coord (3*D.radius) :=
    closedBall_subset_closedBall (by linarith [D.radius_pos]) hClosed
  have hR : z∈ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball (by linarith [P.radius_pos,P.radius_lt] : P.radius/4 ≤ P.charts.radius)) (D.collar_mem h3)
  exact P.charts.closedBall_source D.center (ball_subset_closedBall hR)

theorem bump_zero_outside_source {z : ComplexVector n}
    (hz : z∉(P.charts.chart D.center).source) : D.bump z=0 := by
  by_contra hn
  exact hz (D.bump_support_source (subset_closure hn))

theorem bump_hasCompactSupport : HasCompactSupport D.bump :=
  (isCompact_closedBall D.coord (2*D.radius)).of_isClosed_subset
    (isClosed_tsupport D.bump) D.bump_support

def supportSet : Set M.Carrier := (P.charts.chart D.center) '' tsupport D.bump

theorem supportSet_isCompact : IsCompact D.supportSet :=
  D.bump_hasCompactSupport.image_of_continuousOn
    ((P.charts.chart D.center).continuousOn.mono D.bump_support_source)

theorem supportSet_subset_target : D.supportSet⊆(P.charts.chart D.center).target := by
  rintro y ⟨z,hz,rfl⟩
  exact (P.charts.chart D.center).map_source (D.bump_support_source hz)

end BootstrapPatch
end Yau.LeafProofs.L17BootstrapPatchAux
