import Yau.LeafProofs.L05ChuCausalCutoff
import Yau.LeafProofs.L05ChuModulusTransport
import Yau.LeafProofs.L16CutoffFullHolderExtension

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuCutoffJetsDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuCutoffJetsDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuCutoffJetsHessianGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuCutoffJetsHessianSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

def chuSpatialHessianCommutator {n : ℕ} (phi : Space n → ℝ) (u : Point n → ℝ) (p : Point n) :
    Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  (fderiv ℝ phi p.1).smulRight (spatialD u p)+
    (spatialD u p).smulRight (fderiv ℝ phi p.1)+u p • fderiv ℝ (fderiv ℝ phi) p.1

theorem chu_spatial_cutoff_hessian_identity {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {phi : Space n → ℝ} (hphi : ContDiff ℝ 2 phi) (hSupport : tsupport phi ⊆ O)
    {u : Point n → ℝ} (hu : C2 (cylinder O l r) u) {p : Point n} (hp : p ∈ cylinder Set.univ l r) :
    spatialDD (fun q => phi q.1*u q) p=phi p.1 • spatialDD u p+chuSpatialHessianCommutator phi u p := by
  by_cases hpO : p.1 ∈ O
  · have hh := L16Aux.secondFDeriv_mul hphi.contDiffAt (hu.2.2.2.2.1 p ⟨hpO,hp.2⟩)
    change spatialDD (fun q => phi q.1*u q) p=
      ((phi p.1 • spatialDD u p+(fderiv ℝ phi p.1).smulRight (spatialD u p))+
        (spatialD u p).smulRight (fderiv ℝ phi p.1))+u p • fderiv ℝ (fderiv ℝ phi) p.1 at hh
    rw [hh]
    unfold chuSpatialHessianCommutator
    abel
  · have hOutside : p.1 ∉ tsupport phi := fun h => hpO (hSupport h)
    have hz := (L16Aux.spatial_cutoff_jets_zero_of_notMem_tsupport (cylinder Set.univ l r) phi u hOutside).2.2.1
    have h0 := image_eq_zero_of_notMem_tsupport hOutside
    have h1 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hOutside
    have h2 := fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (show p.1 ∉ tsupport (fderiv ℝ phi) from fun h => hOutside (tsupport_fderiv_subset ℝ h))
    simp only [hz,h0,h1,h2,chuSpatialHessianCommutator,zero_smul,smul_zero,
      ContinuousLinearMap.zero_smulRight,ContinuousLinearMap.smulRight_zero,add_zero]

theorem chu_time_space_cutoff_hessian_identity {n : ℕ} {O : Set (Space n)} {l r : ℝ}
    (hO : IsOpen O) {phi : Space n → ℝ} (hphi : ContDiff ℝ 2 phi) (hSupport : tsupport phi ⊆ O)
    {u : Point n → ℝ} (hu : C2 (cylinder O l r) u) (theta : ℝ → ℝ)
    {p : Point n} (hp : p ∈ cylinder Set.univ l r) :
    spatialDD (fun q => theta q.2*(phi q.1*u q)) p=
      (theta p.2*phi p.1) • spatialDD u p+theta p.2 • chuSpatialHessianCommutator phi u p := by
  have hC2 := L16Aux.c2_spatial_cutoff_extension hO hphi hSupport hu
  rw [L16Aux.spatialDD_time_mul hC2 theta hp,chu_spatial_cutoff_hessian_identity hO hphi hSupport hu hp,
    smul_add,smul_smul]

set_option maxHeartbeats 1600000 in
theorem chuSpatialHessianCommutator_holderBound {n : ℕ} {O : Set (Space n)} {l r gamma E1 E2 C : ℝ}
    {phi : Space n → ℝ} (hSupport : tsupport phi ⊆ O) {u : Point n → ℝ}
    (hD : HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ phi p.1) E1)
    (hDD : HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ phi) p.1) E2)
    (hLow : HolderBound gamma (cylinder O l r) (fun p => (u p,spatialD u p)) C) :
    HolderBound gamma (cylinder Set.univ l r) (chuSpatialHessianCommutator phi u) ((4*E1+2*E2)*C) := by
  let P : Set (Point n) := cylinder Set.univ l r
  let U : Set (Point n) := O ×ˢ Set.univ
  have hUP : U ∩ P=cylinder O l r := by ext p; simp [U,P,cylinder]
  have hu0 : HolderBound gamma (U ∩ P) u C := by
    simpa only [hUP] using L16Aux.holderBound_fst hLow
  have hu1 : HolderBound gamma (U ∩ P) (spatialD u) C := by
    simpa only [hUP] using L16Aux.holderBound_snd hLow
  have hDzero (p : Point n) (hp : p ∈ P) (hpU : p ∉ U) : fderiv ℝ phi p.1=0 := by
    apply fderiv_of_notMem_tsupport
    intro h
    exact hpU ⟨hSupport h,Set.mem_univ _⟩
  have hDDzero (p : Point n) (hp : p ∈ P) (hpU : p ∉ U) : fderiv ℝ (fderiv ℝ phi) p.1=0 := by
    apply fderiv_of_notMem_tsupport
    intro h
    exact hpU ⟨hSupport (tsupport_fderiv_subset ℝ h),Set.mem_univ _⟩
  have h1 := L16Aux.holderBound_tensor_cutoff_extension hD hu1 hDzero
  have h2 := L16Aux.holderBound_tensor_flip_cutoff_extension hD hu1 hDzero
  have h3 := L16Aux.holderBound_bilinear_cutoff_extension
    (fun (a : Space n →L[ℝ] Space n →L[ℝ] ℝ) (v : ℝ) => v • a)
    (fun x y z => smul_sub z x y) (fun x y z => sub_smul y z x) (fun z => smul_zero z)
    (fun a v => by rw [norm_smul,Real.norm_eq_abs,mul_comm]) hDD hu0 hDDzero
  have hh := L16Aux.holderBound_add (L16Aux.holderBound_add h1 h2) h3
  convert! hh using 1
  ring

theorem chuTimeHessianCommutator_holderBound {n : ℕ} {O : Set (Space n)} {l r gamma E1 E2 C D : ℝ}
    {phi : Space n → ℝ} (hSupport : tsupport phi ⊆ O) {u : Point n → ℝ} {theta : ℝ → ℝ}
    (hD : HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ phi p.1) E1)
    (hDD : HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ phi) p.1) E2)
    (hLow : HolderBound gamma (cylinder O l r) (fun p => (u p,spatialD u p)) C)
    (htheta : HolderBound gamma (cylinder Set.univ l r) (fun p : Point n => theta p.2) D) :
    HolderBound gamma (cylinder Set.univ l r) (fun p => theta p.2 • chuSpatialHessianCommutator phi u p)
      (2*D*((4*E1+2*E2)*C)) := by
  have hcomm := chuSpatialHessianCommutator_holderBound hSupport hD hDD hLow
  have hh := L16Aux.holderBound_smul_refined htheta hcomm htheta.1 hcomm.1
    (fun p hp => by simpa only [Real.norm_eq_abs] using htheta.2.1 p hp) hcomm.2.1
  convert! hh using 1
  ring

end Yau.LeafProofs.L05Aux
