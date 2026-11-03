import Yau.Proofs.F05BootstrapJetIdentification

/-! The original relative operator passes to a genuine compact jet limit.
The limiting jets are identified with the actual derivatives of the value
limit before any equation is asserted. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_equation_uniform_jets_limit (ν : Option (RIdx n)) {r s T α C : ℝ}
    (hr : 0 < r) (hsT : s < T) {v : ℕ → Point n → ℝ} {vLim : Point n → ℝ}
    {G : Point n → Space n →L[ℝ] ℝ}
    {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ} {J : Point n → ℝ}
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    {f : ℕ → Point n → ℝ} {fLim : Point n → ℝ}
    (hv : ∀ k, F05RelSchauder α (region ν r) (Icc s T) (v k) C)
    (hLim : TendstoUniformlyOn v vLim atTop (region ν r ×ˢ Icc s T))
    (hGLim : TendstoUniformlyOn (fun k => F05RelD (region ν r) (v k)) G atTop
      (region ν r ×ˢ Icc s T))
    (hHLim : TendstoUniformlyOn (fun k => F05RelDD (region ν r) (v k)) H atTop
      (region ν r ×ˢ Icc s T))
    (hJLim : TendstoUniformlyOn (fun k => F05RelT (Icc s T) (v k)) J atTop
      (region ν r ×ˢ Icc s T))
    (hfLim : ∀ z ∈ region ν r ×ˢ Icc s T, Tendsto (fun k => f k z) atTop (𝓝 (fLim z)))
    (hEq : ∀ k z, z ∈ region ν r ×ˢ Icc s T →
      F05RelOp (region ν r) (Icc s T) a b (v k) z = f k z) :
    ∀ z ∈ region ν r ×ˢ Icc s T,
      F05RelOp (region ν r) (Icc s T) a b vLim z = fLim z := by
  have hIdent := F05_relative_uniform_jets_identified ν hr hsT hv hLim hGLim hHLim hJLim
  intro z hz
  let E := Space n →L[ℝ] ℝ
  let F := Space n →L[ℝ] Space n →L[ℝ] ℝ
  let op : E × F × ℝ → ℝ := fun q =>
    q.2.2-(∑ j,∑ k,a z j k*q.2.1 (realVec j) (realVec k))-
      ∑ j,b z j*q.1 (realVec j)
  have hContinuous : Continuous op := by dsimp only [op]; fun_prop
  have hTuple := (hGLim.tendsto_at hz).prodMk_nhds
    ((hHLim.tendsto_at hz).prodMk_nhds (hJLim.tendsto_at hz))
  have hOp : Tendsto (fun k => F05RelOp (region ν r) (Icc s T) a b (v k) z)
      atTop (𝓝 (op (G z,H z,J z))) :=
    (hContinuous.tendsto (G z,H z,J z)).comp hTuple
  have hRight : Tendsto (fun k => F05RelOp (region ν r) (Icc s T) a b (v k) z)
      atTop (𝓝 (fLim z)) :=
    (hfLim z hz).congr' (Eventually.of_forall (fun k => (hEq k z hz).symm))
  have hValue := tendsto_nhds_unique hOp hRight
  rw [F05RelOp,(hIdent z hz).1,(hIdent z hz).2.1,(hIdent z hz).2.2]
  exact hValue

end Yau.Proofs.F05Aux
