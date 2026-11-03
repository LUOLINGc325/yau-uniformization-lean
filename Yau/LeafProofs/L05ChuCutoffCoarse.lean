import Yau.LeafProofs.L05ChuSourceAbsorption

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuCutoffCoarseDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuCutoffCoarseDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuCutoffCoarseHessianGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuCutoffCoarseHessianSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

theorem chu_cutoff_hessian_coarse_holder {n : ℕ} {O : Set (Space n)} {l r eta E0 E1 E2 C D MH : ℝ}
    (hO : IsOpen O) {phi : Space n → ℝ} (hphi : ContDiff ℝ 2 phi) (hSupport : tsupport phi ⊆ O)
    {u : Point n → ℝ} (hu : C2 (cylinder O l r) u) {theta : ℝ → ℝ}
    (h0 : HolderBound eta (cylinder Set.univ l r) (fun p => phi p.1) E0)
    (hD : HolderBound eta (cylinder Set.univ l r) (fun p => fderiv ℝ phi p.1) E1)
    (hDD : HolderBound eta (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ phi) p.1) E2)
    (hLow : HolderBound eta (cylinder O l r) (fun p => (u p,spatialD u p)) C)
    (hH : HolderBound eta (cylinder O l r) (spatialDD u) MH)
    (htheta : HolderBound eta (cylinder Set.univ l r) (fun p : Point n => theta p.2) D) :
    HolderBound eta (cylinder Set.univ l r)
      (spatialDD (fun p => theta p.2*(phi p.1*u p)))
      (4*D*E0*MH+2*D*((4*E1+2*E2)*C)) := by
  let P : Set (Point n) := cylinder Set.univ l r
  let U : Set (Point n) := O ×ˢ Set.univ
  let chi : Point n → ℝ := fun p => theta p.2*phi p.1
  have hUP : U ∩ P=cylinder O l r := by ext p; simp [U,P,cylinder]
  have hchi : HolderBound eta P chi (2*D*E0) := L16Aux.holderBound_mul htheta h0
  have hHlocal : HolderBound eta (U ∩ P) (spatialDD u) MH := by simpa only [hUP] using hH
  have hZero (p : Point n) (hp : p ∈ P) (hpU : p ∉ U) : chi p=0 := by
    have hphi0 : phi p.1=0 := image_eq_zero_of_notMem_tsupport (fun h => hpU ⟨hSupport h,Set.mem_univ _⟩)
    change theta p.2*phi p.1=0
    rw [hphi0,mul_zero]
  have hMain := L16Aux.holderBound_smul_cutoff_extension hchi hHlocal hZero
  have hComm := chuTimeHessianCommutator_holderBound hSupport hD hDD hLow htheta
  have hAll := L16Aux.holderBound_add hMain hComm
  have hFinal := L16Aux.holderBound_congr_on hAll (fun p hp =>
    (chu_time_space_cutoff_hessian_identity hO hphi hSupport hu theta hp).symm)
  convert! hFinal using 1
  ring

theorem chu_cutoff_source_coarse_holder {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) {O : Set (Space n)} {l r eta M E0 E1 E2 C D D1 MR : ℝ}
    {phi : Space n → ℝ} (hSupport : tsupport phi ⊆ O) {u : Point n → ℝ} {theta : ℝ → ℝ}
    (hM : 0 ≤ M) (ha : ‖(chuFrozenSlope hT F A0 p0 hp0 : Mat n)‖ ≤ M)
    (h0 : HolderBound eta (cylinder Set.univ l r) (fun p => phi p.1) E0)
    (hD : HolderBound eta (cylinder Set.univ l r) (fun p => fderiv ℝ phi p.1) E1)
    (hDD : HolderBound eta (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ phi) p.1) E2)
    (hLow : HolderBound eta (cylinder O l r) (fun p => (u p,spatialD u p)) C)
    (hR : HolderBound eta (cylinder O l r) (chuFrozenResidual hT F A0 p0 hp0 u) MR)
    (htheta : HolderBound eta (cylinder Set.univ l r) (fun p : Point n => theta p.2) D)
    (hthetaD : HolderBound eta (cylinder Set.univ l r) (fun p : Point n => deriv theta p.2) D1) :
    HolderBound eta (cylinder Set.univ l r) (chuFrozenCutoffSource hT F A0 p0 hp0 phi theta u)
      (4*D*E0*MR+(2*D*L16Aux.spatialCutoffCommutatorBudget n M E1 E2+4*D1*E0)*C) := by
  have hA : HolderBound eta (cylinder (n := n) Set.univ l r) (fun _ => (chuFrozenSlope hT F A0 p0 hp0 : Mat n)) M :=
    chu_holderBound_constant (chuFrozenSlope hT F A0 p0 hp0 : Mat n) hM ha
  have hb (i : RIdx n) : HolderBound eta (cylinder (n := n) Set.univ l r) (fun _ => (0:ℝ)) M :=
    chu_holderBound_constant 0 hM (by simpa only [norm_zero] using hM)
  exact L16Aux.localized_classical_source_holderBound hA hb h0 hD hDD hSupport hLow hR htheta hthetaD

end Yau.LeafProofs.L05Aux
