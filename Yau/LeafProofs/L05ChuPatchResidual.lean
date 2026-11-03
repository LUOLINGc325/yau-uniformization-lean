import Yau.LeafProofs.L05ChuPatchGeometry
import Yau.LeafProofs.L05ChuModulusTransport

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuPatchResidualDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuPatchResidualDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuPatchResidualHessianGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuPatchResidualHessianSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

set_option maxHeartbeats 2000000 in
theorem chu_residual_on_causal_patch {n : ℕ} {omega : ℝ → ℝ} (hm : Modulus omega)
    {ell L K M eta alpha beta fB gamma epsilon : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (he : 0 < eta) (hb : 0 < beta) (hg : 0 ≤ gamma) (hga : gamma ≤ alpha)
    (hgb : gamma ≤ beta) (heps : 0 < epsilon) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧
      ∀ (E U : Set (Sym n)) (F : Sym n → Point n → ℝ) (T : Sym n → Point n → Sym n)
        (S : Point n → Sym n) (f u : Point n → ℝ),
      Convex ℝ E → ∀ (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta),
      ChuH3 S K beta → ChuDerivativeModulus E F omega → HolderBound alpha (backward 1) f fB →
      SchauderBound eta (backward (3/4)) u M →
      (∀ p ∈ backward 1, S p+T (hessian u p) p ∈ E) →
      (∀ p ∈ backward 1, timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p) →
      ∀ p0 : Point n, ∀ hp0 : p0 ∈ backward (1/2),
      ∀ h : ℝ, 0 < h → h ≤ 1/32 → 4*h ≤ rho →
      ∀ p ∈ chuCausalPatch p0 h, ∀ q ∈ chuCausalPatch p0 h,
      |chuFrozenResidual hT F (S p0+T (hessian u p0) p0) p0
          (chu_backward_subset (by norm_num) (by norm_num) hp0) u p-
        chuFrozenResidual hT F (S p0+T (hessian u p0) p0) p0
          (chu_backward_subset (by norm_num) (by norm_num) hp0) u q| ≤
        epsilon*‖spatialDD u p-spatialDD u q‖+
          chuResidualSourceConstant n L K fB (chuHessianTransportConstant n*M)
            (chuAnchorModulusBound n K (chuHessianTransportConstant n*M) omega)*holderWeight gamma p q := by
  have hDim := chuHessianTransportConstant_pos n
  obtain ⟨rho,hrho,hrho1,hLocal⟩ := chu_local_residual_bound hm hell hL hK
    (mul_nonneg hDim.le hM) he hb hg hga hgb (div_pos heps hDim)
  refine ⟨rho,hrho,hrho1,?_⟩
  intro E U F T S f u hE hF hT hS hDF hf hCoarse hRange hPDE p0 hp0 h hh hh1 hhrho p hp q hq
  have hQ : backward (n := n) (3/4) ⊆ backward 1 := chu_backward_subset (by norm_num) (by norm_num)
  have hCenter : p0 ∈ backward (3/4) := chu_backward_subset (by norm_num) (by norm_num) hp0
  have hPatch := chuCausalPatch_subset_backward hh.le hh1 hp0
  have hHp := hessian_holderBound_of_spatialDD hCoarse.2.2.2.1
  have hpDist : parabolicDistance p p0 ≤ rho := (chuCausalPatch_distance_to_center hh.le hp).trans hhrho
  have hqDist : parabolicDistance q p0 ≤ rho := (chuCausalPatch_distance_to_center hh.le hq).trans hhrho
  have hpq : parabolicDistance p q ≤ 1 :=
    (chuCausalPatch_pair_distance hh.le hp hq).trans (by linarith only [hh1])
  have hR := hLocal E U F T S f u (backward (3/4)) hE hF hT hS hDF hf hQ hHp hRange hPDE
    p0 hCenter p (hPatch hp) q (hPatch hq) hpDist hqDist hpq
  have hNorm := mul_le_mul_of_nonneg_left (chu_hessian_difference_norm_le u p q) (div_nonneg heps.le hDim.le)
  have hCancel : (epsilon/chuHessianTransportConstant n)*
      (chuHessianTransportConstant n*‖spatialDD u p-spatialDD u q‖)=epsilon*‖spatialDD u p-spatialDD u q‖ := by
    field_simp [hDim.ne']
  rw [hCancel] at hNorm
  nlinarith only [hR,hNorm]

end Yau.LeafProofs.L05Aux
