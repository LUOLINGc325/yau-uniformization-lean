import Yau.Proofs.C03ShortLiftDistance
import Yau.Proofs.C03ShortLiftSheetTopology

/-! A single genuine holomorphic inverse sheet, its topology, and its intrinsic distance control. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}
local instance (hn : 1 ≤ n) : NormedAddCommGroup (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℝ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℂ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℂ (ComplexVector n))

theorem exists_short_holomorphic_inverse_sheet
    (k : HermitianField M) (hs : MetricSmooth k)
    (Phi : ComplexVector n → M.Carrier) (r c : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hPhi : IsLocalBiholomorphism Phi r)
    (hlo : ∀ z ∈ Metric.ball 0 r, HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat k Phi z))
    (ctarget : M.Carrier) (w0 : ComplexVector n) (delta L : ℝ)
    (hdelta : 0 < delta) (hL : 0 < L)
    (hW : Metric.ball w0 delta ⊆ chartTarget ctarget)
    (hp0 : Phi 0 = chartInv ctarget w0)
    (hG : ∀ q ∈ Metric.ball w0 delta, ∀ v : ComplexVector n,
      realMetricInChart k ctarget q v v ≤ L ^ 2 * ‖v‖ ^ 2)
    (hshort : L * delta < Real.sqrt (2 * c) * r) :
    ∃ sigma : ComplexVector n → ComplexVector n,
      sigma w0 = 0 ∧ ContDiffOn ℂ ∞ sigma (Metric.ball w0 delta) ∧
      MapsTo sigma (Metric.ball w0 delta) (Metric.ball 0 r) ∧
      (∀ w ∈ Metric.ball w0 delta, Phi (sigma w) = chartInv ctarget w) ∧
      (∀ w ∈ Metric.ball w0 delta,
        ‖sigma w‖ ≤ (Real.sqrt (2 * c))⁻¹ * (L * ‖w - w0‖)) ∧
      InjOn sigma (Metric.ball w0 delta) ∧ IsOpen (sigma '' Metric.ball w0 delta) ∧
      (∀ w ∈ Metric.ball w0 delta, sheetCoordinates Phi ctarget (sigma w) = w) ∧
      (∀ z ∈ sigma '' Metric.ball w0 delta, sigma (sheetCoordinates Phi ctarget z) = z) ∧
      ∀ (hn : 1 ≤ n) (ks : HermitianField (ComplexEuclideanManifold n hn)),
        MetricSmooth ks →
        (∀ z ∈ Metric.ball 0 r, ∀ u v : ComplexVector n,
          (ks z).toFun u v = (k (Phi z)).toFun
            (mfderiv (ComplexModel n) (ComplexModel n) Phi z u)
            (mfderiv (ComplexModel n) (ComplexModel n) Phi z v)) →
        ∀ w ∈ Metric.ball w0 delta, inducedDistance ks 0 (sigma w) ≤ L * ‖w - w0‖ := by
  obtain ⟨sigma, hsigma0, hsm, hmem, hright, hnorm⟩ :=
    exists_short_inverse_section k hs Phi r c hr hc hPhi hlo
      ctarget w0 delta L hdelta hL hW hp0 hG hshort
  obtain ⟨hinj, hopen, _, htheta, hsigmatheta⟩ :=
    inverse_sheet_topology hPhi ctarget (Metric.ball w0 delta) Metric.isOpen_ball
      ⟨w0, Metric.mem_ball_self hdelta⟩ hW sigma hsm.continuousOn hmem hright
  refine ⟨sigma, hsigma0, hsm, hmem, hright, hnorm, hinj, hopen, htheta, hsigmatheta, ?_⟩
  intro hn ks hks heq
  exact section_source_distance k hs Phi r hPhi ctarget w0 delta L hL hW hp0 hG
    sigma hsigma0 hsm hmem hright hn ks hks heq

end Yau.Proofs.C03Aux.ShortLift
