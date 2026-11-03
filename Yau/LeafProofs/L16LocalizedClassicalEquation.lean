import Yau.LeafProofs.L16HolderExtension
import Yau.LeafProofs.L16TemporalCutoff

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def spatialCutoffCommutator {n : ℕ} (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (φ : Space n → ℝ)
    (u : Point n → ℝ) (p : Point n) : ℝ :=
  (∑ i, ∑ j, a p i j*
    (fderiv ℝ φ p.1 (Yau.realVec i)*spatialD u p (Yau.realVec j)+
      fderiv ℝ φ p.1 (Yau.realVec j)*spatialD u p (Yau.realVec i)+
      u p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))+
  u p*(∑ i, b p i*fderiv ℝ φ p.1 (Yau.realVec i))

theorem spatial_cutoff_jets_zero_of_notMem_tsupport {n : ℕ}
    (Q : Set (Point n)) (φ : Space n → ℝ) (u : Point n → ℝ)
    {p : Point n} (hp : p.1 ∉ tsupport φ) :
    (fun q => φ q.1*u q) p = 0 ∧
      spatialD (fun q => φ q.1*u q) p = 0 ∧
      spatialDD (fun q => φ q.1*u q) p = 0 ∧
      timeD Q (fun q => φ q.1*u q) p = 0 := by
  have hφ0 : φ p.1 = 0 := image_eq_zero_of_notMem_tsupport hp
  have hSlice : (fun x : Space n => φ x*u (x,p.2)) =ᶠ[𝓝 p.1] (fun _ => 0) := by
    have h := notMem_tsupport_iff_eventuallyEq.mp hp
    filter_upwards [h] with x hx
    simp only [Pi.zero_apply] at hx
    rw [hx,zero_mul]
  refine ⟨by change φ p.1*u p = 0; rw [hφ0,zero_mul],?_,?_,?_⟩
  · simpa only [spatialD,fderiv_fun_const,Pi.zero_apply] using hSlice.fderiv_eq (𝕜 := ℝ)
  · simpa only [spatialDD,fderiv_fun_const,fderiv_zero,Pi.zero_apply] using
      (hSlice.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  · rw [timeD_spatial_mul,hφ0,zero_mul]

theorem linearOp_spatial_cutoff_extension {n : ℕ} {l r : ℝ}
    {O : Set (Space n)} {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hSupport : tsupport φ ⊆ O) {u f : Point n → ℝ}
    (hu : C2 (cylinder O l r) u)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hPDE : ∀ p ∈ cylinder O l r, linearOp (cylinder O l r) a b u p = f p)
    {p : Point n} (hp : p ∈ cylinder Set.univ l r) :
    linearOp (cylinder Set.univ l r) a b (fun q => φ q.1*u q) p =
      φ p.1*f p-spatialCutoffCommutator a b φ u p := by
  by_cases hpO : p.1 ∈ O
  · have hpLocal : p ∈ cylinder O l r := ⟨hpO,hp.2⟩
    have hBase : linearOp (cylinder Set.univ l r) a b u p = f p := by
      rw [show linearOp (cylinder Set.univ l r) a b u p = linearOp (cylinder O l r) a b u p by
        simp only [linearOp,timeD_cylinder_change_space u (Set.mem_univ p.1) hpO]]
      exact hPDE p hpLocal
    have h := linearOp_spatial_mul (Q := cylinder Set.univ l r) (a := a) (b := b)
      hφ.contDiffAt (hu.2.2.2.2.1 p hpLocal)
    rw [hBase] at h
    convert h using 1
    dsimp only [spatialCutoffCommutator]
    ring
  · have hpSupport : p.1 ∉ tsupport φ := fun h => hpO (hSupport h)
    have hZeros := spatial_cutoff_jets_zero_of_notMem_tsupport
      (cylinder Set.univ l r) φ u hpSupport
    have hφ0 := image_eq_zero_of_notMem_tsupport hpSupport
    have hDφ := fderiv_of_notMem_tsupport (𝕜 := ℝ) hpSupport
    have hDDφ := fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (show p.1 ∉ tsupport (fderiv ℝ φ) from fun h => hpSupport (tsupport_fderiv_subset ℝ h))
    simp only [linearOp,hZeros.2.1,hZeros.2.2.1,hZeros.2.2.2,hφ0,
      spatialCutoffCommutator,hDφ,hDDφ,zero_apply,zero_mul,mul_zero,
      Finset.sum_const_zero,add_zero,sub_zero]

theorem localized_classical_cutoff_equation {n : ℕ} {l r : ℝ}
    (hlr : l < r) {O : Set (Space n)} (hO : IsOpen O)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 2 φ) (hSupport : tsupport φ ⊆ O)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    {u f : Point n → ℝ} (hu : C2 (cylinder O l r) u)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hPDE : ∀ p ∈ cylinder O l r, linearOp (cylinder O l r) a b u p = f p) :
    C2 (cylinder Set.univ l r) (fun p => θ p.2*(φ p.1*u p)) ∧
    ∀ p ∈ cylinder Set.univ l r,
      linearOp (cylinder Set.univ l r) a b (fun q => θ q.2*(φ q.1*u q)) p =
        θ p.2*(φ p.1*f p-spatialCutoffCommutator a b φ u p)+
          deriv θ p.2*(φ p.1*u p) := by
  have hCut : C2 (cylinder Set.univ l r) (fun p => φ p.1*u p) :=
    c2_spatial_cutoff_extension hO hφ hSupport hu
  refine ⟨c2_time_mul hlr hCut hθ,?_⟩
  intro p hp
  rw [linearOp_time_mul hlr hCut (hθ.differentiable (by norm_num)) a b hp,
    linearOp_spatial_cutoff_extension hφ hSupport hu a b hPDE hp]

def spatialCutoffCommutatorBudget (n : ℕ) (M E1 E2 : ℝ) : ℝ :=
  (Fintype.card (Yau.RIdx n) : ℝ)^2*(8*M*E1+4*M*E2)+
    4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E1

theorem spatialCutoffCommutator_holderBound_local {n : ℕ} {α M E1 E2 L l r : ℝ}
    {O : Set (Space n)} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {φ : Space n → ℝ} {u : Point n → ℝ}
    (ha : HolderBound α (cylinder Set.univ l r) a M)
    (hb : ∀ i, HolderBound α (cylinder Set.univ l r) (fun p => b p i) M)
    (hφD : HolderBound α (cylinder Set.univ l r) (fun p => fderiv ℝ φ p.1) E1)
    (hφDD : HolderBound α (cylinder Set.univ l r)
      (fun p => fderiv ℝ (fderiv ℝ φ) p.1) E2)
    (hSupport : tsupport φ ⊆ O)
    (hLow : HolderBound α (cylinder O l r) (fun p => (u p,spatialD u p)) L) :
    HolderBound α (cylinder Set.univ l r) (spatialCutoffCommutator a b φ u)
      (spatialCutoffCommutatorBudget n M E1 E2*L) := by
  let Q : Set (Point n) := cylinder Set.univ l r
  let U : Set (Point n) := O ×ˢ Set.univ
  have hLow' : HolderBound α (U ∩ Q) (fun p => (u p,spatialD u p)) L :=
    holderBound_mono hLow (fun p hp => ⟨hp.1.1,hp.2.2⟩)
  have hValue := holderBound_fst hLow'
  have hGrad (i : Yau.RIdx n) := holderBound_gradient_component (holderBound_snd hLow') i
  have hZeroD (i : Yau.RIdx n) (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) :
      fderiv ℝ φ p.1 (Yau.realVec i) = 0 := by
    have hNot : p.1 ∉ tsupport φ := fun h => hpU ⟨hSupport h,Set.mem_univ _⟩
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hNot,zero_apply]
  have hZeroDD (i j : Yau.RIdx n) (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) :
      fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j) = 0 := by
    have hNot : p.1 ∉ tsupport (fderiv ℝ φ) := fun h =>
      hpU ⟨hSupport (tsupport_fderiv_subset ℝ h),Set.mem_univ _⟩
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hNot,zero_apply,zero_apply]
  have hDG (i j : Yau.RIdx n) : HolderBound α Q
      (fun p => fderiv ℝ φ p.1 (Yau.realVec i)*spatialD u p (Yau.realVec j)) (2*E1*L) := by
    simpa only [smul_eq_mul] using holderBound_smul_cutoff_extension
      (holderBound_gradient_component hφD i) (hGrad j) (hZeroD i)
  have hHV (i j : Yau.RIdx n) : HolderBound α Q
      (fun p => u p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)) (2*E2*L) := by
    simpa only [smul_eq_mul,mul_comm] using holderBound_smul_cutoff_extension
      (holderBound_hessian_component hφDD i j) hValue (hZeroDD i j)
  have hDV (i : Yau.RIdx n) : HolderBound α Q
      (fun p => fderiv ℝ φ p.1 (Yau.realVec i)*u p) (2*E1*L) := by
    simpa only [smul_eq_mul] using holderBound_smul_cutoff_extension
      (holderBound_gradient_component hφD i) hValue (hZeroD i)
  have hMatrix (i j : Yau.RIdx n) : HolderBound α Q
      (fun p => a p i j*
        (fderiv ℝ φ p.1 (Yau.realVec i)*spatialD u p (Yau.realVec j)+
          fderiv ℝ φ p.1 (Yau.realVec j)*spatialD u p (Yau.realVec i)+
          u p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))
      ((8*M*E1+4*M*E2)*L) := by
    have h := holderBound_mul (holderBound_matrix_entry ha i j)
      (holderBound_add (holderBound_add (hDG i j) (hDG j i)) (hHV i j))
    convert h using 1; ring
  have hRow (i : Yau.RIdx n) := holderBound_finset_sum Finset.univ (fun j _ => hMatrix i j)
  have hMatrixSum := holderBound_finset_sum Finset.univ (fun i _ => hRow i)
  have hDrift (i : Yau.RIdx n) : HolderBound α Q
      (fun p => b p i*(fderiv ℝ φ p.1 (Yau.realVec i)*u p)) (4*M*E1*L) := by
    have h := holderBound_mul (hb i) (hDV i)
    convert h using 1; ring
  have hDriftSum := holderBound_finset_sum Finset.univ (fun i _ => hDrift i)
  have hSum := holderBound_add hMatrixSum hDriftSum
  have hAlgebra (p : Point n) :
      (∑ i : Yau.RIdx n, b p i*(fderiv ℝ φ p.1 (Yau.realVec i)*u p)) =
        u p*(∑ i : Yau.RIdx n, b p i*fderiv ℝ φ p.1 (Yau.realVec i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  apply holderBound_congr_on _ (show Set.EqOn
    (fun p => (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, a p i j*
      (fderiv ℝ φ p.1 (Yau.realVec i)*spatialD u p (Yau.realVec j)+
        fderiv ℝ φ p.1 (Yau.realVec j)*spatialD u p (Yau.realVec i)+
        u p*fderiv ℝ (fderiv ℝ φ) p.1 (Yau.realVec i) (Yau.realVec j)))+
      ∑ i : Yau.RIdx n, b p i*(fderiv ℝ φ p.1 (Yau.realVec i)*u p))
    (spatialCutoffCommutator a b φ u) Q from by
      intro p hp
      dsimp only
      rw [hAlgebra p]
      rfl)
  convert hSum using 1
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  dsimp only [spatialCutoffCommutatorBudget]
  ring

theorem localized_classical_source_holderBound {n : ℕ} {α M E0 E1 E2 H0 H1 F L l r : ℝ}
    {O : Set (Space n)} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {φ : Space n → ℝ} {θ : ℝ → ℝ} {u f : Point n → ℝ}
    (ha : HolderBound α (cylinder Set.univ l r) a M)
    (hb : ∀ i, HolderBound α (cylinder Set.univ l r) (fun p => b p i) M)
    (hφ : HolderBound α (cylinder Set.univ l r) (fun p => φ p.1) E0)
    (hφD : HolderBound α (cylinder Set.univ l r) (fun p => fderiv ℝ φ p.1) E1)
    (hφDD : HolderBound α (cylinder Set.univ l r)
      (fun p => fderiv ℝ (fderiv ℝ φ) p.1) E2)
    (hSupport : tsupport φ ⊆ O)
    (hLow : HolderBound α (cylinder O l r) (fun p => (u p,spatialD u p)) L)
    (hf : HolderBound α (cylinder O l r) f F)
    (hθ : HolderBound α (cylinder (n := n) Set.univ l r) (fun p => θ p.2) H0)
    (hθD : HolderBound α (cylinder (n := n) Set.univ l r) (fun p => deriv θ p.2) H1) :
    HolderBound α (cylinder Set.univ l r)
      (fun p => θ p.2*(φ p.1*f p-spatialCutoffCommutator a b φ u p)+
        deriv θ p.2*(φ p.1*u p))
      (4*H0*E0*F+(2*H0*spatialCutoffCommutatorBudget n M E1 E2+4*H1*E0)*L) := by
  let Q : Set (Point n) := cylinder Set.univ l r
  let U : Set (Point n) := O ×ˢ Set.univ
  have hSub : U ∩ Q ⊆ cylinder O l r := fun p hp => ⟨hp.1.1,hp.2.2⟩
  have hZero (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) : φ p.1 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hpU ⟨hSupport h,Set.mem_univ _⟩)
  have hProductF : HolderBound α Q (fun p => φ p.1*f p) (2*E0*F) := by
    simpa only [smul_eq_mul] using
      holderBound_smul_cutoff_extension hφ (holderBound_mono hf hSub) hZero
  have hProductU : HolderBound α Q (fun p => φ p.1*u p) (2*E0*L) := by
    simpa only [smul_eq_mul] using holderBound_smul_cutoff_extension hφ
      (holderBound_fst (holderBound_mono hLow hSub)) hZero
  have hCommutator := spatialCutoffCommutator_holderBound_local ha hb hφD hφDD hSupport hLow
  have hMain := holderBound_mul hθ (holderBound_sub hProductF hCommutator)
  have hDerivative := holderBound_mul hθD hProductU
  have hAll := holderBound_add hMain hDerivative
  convert hAll using 1; ring

end Yau.LeafProofs.L16Aux
