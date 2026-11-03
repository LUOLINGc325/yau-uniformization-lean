import Yau.Proofs.C05ScalarTimeSourceBoundsSmooth
import Yau.Proofs.C05RicciLeviJetBounds
import Yau.Proofs.C05RicciCubicJets

/-! The actual first-source jets through four and second-source jets through two. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05ScalarTimeSourceBoundsAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
open Yau.Proofs.C05RicciSquareJetsAux Yau.Proofs.C05RicciCubicJetsAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem source1_jet_bound (k : HermitianField M) (hk : MetricSmooth k) (hK : KahlerClosed k)
    (m : ℕ) (hm : m ≤ 4) (x : M.Carrier) {B : ℝ} (hB : 0 ≤ B)
    (hScalar : ∀ j ≤ 6, scalarJetNorm k (scalarCurvature k) j x ≤ B)
    (hRicci : ∀ j ≤ 4, realRicciJetNorm k j x ≤ B) :
    scalarJetNorm k (scalarTimeSource1 k) m x ≤ b1 n B := by
  have hs := scalarCurvature_smoothFn k hk hK
  have hl := scalarJetNorm_laplacian_le k hk hK (scalarCurvature k) hs m x
  have hl' := hl.trans (mul_le_mul_of_nonneg_left (hScalar (2+m) (by omega))
    (div_nonneg (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2)))
  have hr := scalarJetNorm_ricciNormSq_le_four k hk hK m hm x hB hRicci
  rw [source1_function]
  have H := scalarJetNorm_add_le k hk _ _ (laplacian_smoothFn k hk hK _ hs)
    (ricciNormSq_smoothFn k hk hK) m x
  unfold b1 realDimension
  exact H.trans (add_le_add hl' hr)

theorem source2_jet_bound (k : HermitianField M) (hk : MetricSmooth k) (hK : KahlerClosed k)
    (m : ℕ) (hm : m ≤ 2) (x : M.Carrier) {B : ℝ} (hB : 0 ≤ B)
    (hScalar : ∀ j ≤ 6, scalarJetNorm k (scalarCurvature k) j x ≤ B)
    (hRicci : ∀ j ≤ 4, realRicciJetNorm k j x ≤ B) :
    scalarJetNorm k (scalarTimeSource2 k) m x ≤ b2 n B := by
  let f := laplacian k (scalarTimeSource1 k)
  let g := ricciLeviPairing k (scalarCurvature k)
  let q := ricciCube k
  have hs := scalarCurvature_smoothFn k hk hK
  have hf : SmoothFn f := laplacian_smoothFn k hk hK _ (source1_smoothFn k hk hK)
  have hg : SmoothFn g := ricciLeviPairing_smoothFn k hk hK _ hs
  have hq : SmoothFn q := ricciCube_smoothFn k hk hK
  have HL := scalarJetNorm_laplacian_le k hk hK _ (source1_smoothFn k hk hK) m x
  have hl : scalarJetNorm k f m x ≤ Real.sqrt (realDimension n)/2 * b1 n B :=
    HL.trans (mul_le_mul_of_nonneg_left
      (source1_jet_bound k hk hK (2+m) (by omega) x hB hScalar hRicci)
      (div_nonneg (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2)))
  have HP := scalarJetNorm_ricciLeviPairing_le k hk hK _ hs m hm x hB hB
    (fun j hj => hRicci j (by omega)) (fun j hj => hScalar j (by omega))
  have hp : scalarJetNorm k g m x ≤ 4 * realDimension n * B^2 :=
    HP.trans_eq (by dsimp only [realDimension]; ring)
  have HC := scalarJetNorm_ricciCube_le k hk hK m hm x hB
    (fun j hj => hRicci j (by omega))
  have hc : scalarJetNorm k q m x ≤ 64 * (realDimension n + 1)^3 * B^3 := by
    simpa only [realDimension, Nat.cast_mul, Nat.cast_ofNat] using HC
  have Hinner := scalarJetNorm_add_le k hk f (fun y => 3*g y) hf
    (smoothFn_const_mul 3 hg) m x
  rw [scalarJetNorm_const_mul k hk g hg 3 m x] at Hinner
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 3)] at Hinner
  have Houter := scalarJetNorm_add_le k hk (fun y => f y + 3*g y) (fun y => 2*q y)
    (smoothFn_add hf (smoothFn_const_mul 3 hg)) (smoothFn_const_mul 2 hq) m x
  rw [scalarJetNorm_const_mul k hk q hq 2 m x] at Houter
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)] at Houter
  have hsum := Houter.trans (add_le_add Hinner (le_refl (2 * scalarJetNorm k q m x)))
  change scalarJetNorm k (fun y => f y + 3*g y + 2*q y) m x ≤ _
  unfold b2
  linarith

end Yau.Proofs.C05ScalarTimeSourceBoundsAux
