import Yau.LeafProofs.L05ChuCutoffSource

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuSourceAbsorptionDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuSourceAbsorptionDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuSourceAbsorptionHessianGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuSourceAbsorptionHessianSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

def chuFrozenCutoffAbsorptionBudget (n : ℕ) (A E0 E1 E2 C D D1 Ma MR MH epsilon : ℝ) : ℝ :=
  A+(2*D*E0)*MR+epsilon*(2*D*((4*E1+2*E2)*C)+(2*D*E0)*MH)+
    chuFrozenLowSourceBudget n Ma E0 E1 E2 C D D1

set_option maxHeartbeats 2200000 in
theorem chu_frozen_cutoff_source_pair {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) {O : Set (Space n)} {l r gamma epsilon A E0 E1 E2 C D D1 Ma MR MH : ℝ}
    (hO : IsOpen O) {phi : Space n → ℝ} (hphi : ContDiff ℝ 2 phi) (hSupport : tsupport phi ⊆ O)
    {u : Point n → ℝ} (hu : C2 (cylinder O l r) u) {theta : ℝ → ℝ}
    (heps : 0 ≤ epsilon) (hA : 0 ≤ A) (hMR : 0 ≤ MR) (hMH : 0 ≤ MH) (hMa : 0 ≤ Ma)
    (ha : ‖(chuFrozenSlope hT F A0 p0 hp0 : Mat n)‖ ≤ Ma)
    (h0 : HolderBound gamma (cylinder Set.univ l r) (fun p => phi p.1) E0)
    (hD : HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ phi p.1) E1)
    (hDD : HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ phi) p.1) E2)
    (hLow : HolderBound gamma (cylinder O l r) (fun p => (u p,spatialD u p)) C)
    (htheta : HolderBound gamma (cylinder Set.univ l r) (fun p : Point n => theta p.2) D)
    (hthetaD : HolderBound gamma (cylinder Set.univ l r) (fun p : Point n => deriv theta p.2) D1)
    (hUnitPhi : ∀ x, |phi x| ≤ 1) (hUnitTheta : ∀ t, |theta t| ≤ 1)
    (hR : ∀ p ∈ cylinder O l r, |chuFrozenResidual hT F A0 p0 hp0 u p| ≤ MR)
    (hH : ∀ p ∈ cylinder O l r, ‖spatialDD u p‖ ≤ MH)
    (hpair : ∀ p ∈ cylinder O l r, ∀ q ∈ cylinder O l r,
      |chuFrozenResidual hT F A0 p0 hp0 u p-chuFrozenResidual hT F A0 p0 hp0 u q| ≤
        epsilon*‖spatialDD u p-spatialDD u q‖+A*holderWeight gamma p q)
    {p q : Point n} (hp : p ∈ cylinder Set.univ l r) (hq : q ∈ cylinder Set.univ l r) :
    |chuFrozenCutoffSource hT F A0 p0 hp0 phi theta u p-chuFrozenCutoffSource hT F A0 p0 hp0 phi theta u q| ≤
      epsilon*‖spatialDD (fun s => theta s.2*(phi s.1*u s)) p-spatialDD (fun s => theta s.2*(phi s.1*u s)) q‖+
        chuFrozenCutoffAbsorptionBudget n A E0 E1 E2 C D D1 Ma MR MH epsilon*holderWeight gamma p q := by
  let P : Set (Point n) := cylinder Set.univ l r
  let Q : Set (Point n) := cylinder O l r
  let R := chuFrozenResidual hT F A0 p0 hp0 u
  let chi : Point n → ℝ := fun p => theta p.2*phi p.1
  let H := spatialDD u
  let w : Point n → ℝ := fun p => theta p.2*(phi p.1*u p)
  let J := spatialDD w
  let B := fun p : Point n => theta p.2 • chuSpatialHessianCommutator phi u p
  have hchi : HolderBound gamma P chi (2*D*E0) := L16Aux.holderBound_mul htheta h0
  have hunit (p : Point n) (hp : p ∈ P) : |chi p| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hUnitTheta p.2) (hUnitPhi p.1) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul 1)
  have hzero (p : Point n) (hp : p ∈ P) (hpQ : p ∉ Q) : chi p=0 := by
    have hpO : p.1 ∉ O := fun hx => hpQ ⟨hx,hp.2⟩
    have hphi0 : phi p.1=0 := image_eq_zero_of_notMem_tsupport (fun h => hpO (hSupport h))
    change theta p.2*phi p.1=0
    rw [hphi0,mul_zero]
  have hB : HolderBound gamma P B (2*D*((4*E1+2*E2)*C)) :=
    chuTimeHessianCommutator_holderBound hSupport hD hDD hLow htheta
  have hId (p : Point n) (hp : p ∈ P) : J p=chi p • H p+B p :=
    chu_time_space_cutoff_hessian_identity hO hphi hSupport hu theta hp
  have hWeighted := chu_weighted_cutoff_pair heps hA hMR hMH hchi hunit hzero hR hH hB hId hpair hp hq
  have hSource := chuFrozenLowSource_holderBound hMa ha hSupport h0 hD hDD hLow htheta hthetaD
  have hSourcePair := hSource.2.2 p hp q hq
  rw [Real.norm_eq_abs] at hSourcePair
  have he : chuFrozenCutoffSource hT F A0 p0 hp0 phi theta u p-chuFrozenCutoffSource hT F A0 p0 hp0 phi theta u q=
      (chi p*R p-chi q*R q)+
        (chuFrozenLowSource (chuFrozenSlope hT F A0 p0 hp0 : Mat n) phi theta u p-
          chuFrozenLowSource (chuFrozenSlope hT F A0 p0 hp0 : Mat n) phi theta u q) := by
    rw [chuFrozenCutoffSource_split,chuFrozenCutoffSource_split]
    ring
  rw [he]
  have ht := abs_add_le (chi p*R p-chi q*R q)
    (chuFrozenLowSource (chuFrozenSlope hT F A0 p0 hp0 : Mat n) phi theta u p-
      chuFrozenLowSource (chuFrozenSlope hT F A0 p0 hp0 : Mat n) phi theta u q)
  unfold chuFrozenCutoffAbsorptionBudget
  nlinarith only [ht,hWeighted,hSourcePair]

end Yau.LeafProofs.L05Aux
