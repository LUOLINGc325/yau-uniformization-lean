import Yau.Proofs.U02GlobalCoordinates
import Yau.Proofs.U02Coordinates
import Yau.Proofs.U02Parameters

/-! The original U02 quantifier order: first choose the jet order and
decay exponents, then the arbitrary model constants, then the macro width.
The only predecessor used beyond the original geometric data is U01. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.NodeProofs
open Yau Blueprint U02Proof

theorem U02_of_originalU01 (hU01 : Blueprint.U01) : Blueprint.U02 := by
  intro n X o h U P rho r0 r1 sigma C Cb t0 Phi F f hf hw hc
  obtain ⟨c, gamma0, hcpos, hgamma0, hregime⟩ := hc.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨d, sigmap, gamma, gammap, nu, hd2, hsp, hsps, hsp1, hgamma, hgap,
      hgps, hgg0, hgp1, hnu, hnu1, hcg, hns, _hng, hd⟩ :=
    choose_decay_parameters hc.2.2.1 hcpos hgamma0
  obtain ⟨Tgamma, hreg⟩ := hregime gamma hgamma hgg0
  have hreg' : ∀ t t', Tgamma ≤ t → t ≤ t' → ∀ z : ComplexVector n,
      ‖z‖ ≤ Real.exp (-gamma * rho o t) →
      ‖F t t' z‖ ≤ Real.exp (-(c * gamma) * rho o t') := by
    intro t t' ht htt z hz
    simpa only [neg_mul] using hreg t t' ht htt z hz
  refine ⟨d, sigmap, gammap, hd2, hgamma.trans hgap, hgps, hsps, ?_⟩
  intro Cd Dg
  obtain ⟨h0, hh0, hh01, hwidth⟩ := choose_macro_width hnu 1 |Cd|
  refine ⟨h0, hh0, hh01, ?_⟩
  intro hm hhm hmh0 tk H Hinv G Ginv hp ht
  obtain ⟨hsmall, _hA, hpaid⟩ := hwidth hm hhm hmh0
  let R := min 1 r1
  have hR : 0 < R := lt_min zero_lt_one hc.1
  obtain ⟨psi, inverse, hglobal⟩ := global_coordinates_from_original_data (hU01 n n)
    hf hw hc hp ht hnu hnu1 hd (by linarith : 5 * nu ≤ sigma)
    hR (min_le_left _ _) (min_le_right _ _) hhm hsmall hpaid.le hsp hsp1 hsps
    hgamma (by linarith : gamma ≤ 1) hgap (mul_pos hcpos hgamma)
    (by linarith : 5 * nu ≤ c * gamma) hreg'
  refine ⟨psi, inverse, coordinatesToOpen hglobal, hglobal, rfl, rfl, ?_⟩
  exact imageDynamics_of_coordinates hglobal hp.2.1 (hgamma.trans hgap) hgps
    (fun k => hp.2.2.2.2.2.2.2.2.2 k)

end Yau.NodeProofs
