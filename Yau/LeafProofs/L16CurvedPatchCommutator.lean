import Yau.LeafProofs.L16LocalizedClassicalEquation
import Yau.LeafProofs.L16ChartJetHolder

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Physical-domain coefficients suffice: only the lower solution pair is
localized to the support buffer, and its own small bound is preserved. -/
theorem spatialCutoffCommutator_holderBound_on {n : ℕ} {α M E1 E2 L : ℝ} {Q : Set (Point n)}
    {S : Set (Space n)} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {φ : Space n → ℝ} {u : Point n → ℝ}
    (ha : HolderBound α Q a M)
    (hb : ∀ i, HolderBound α Q (fun p => b p i) M)
    (hφD : HolderBound α Q (fun p => fderiv ℝ φ p.1) E1)
    (hφDD : HolderBound α Q
      (fun p => fderiv ℝ (fderiv ℝ φ) p.1) E2)
    (hSupport : tsupport φ ⊆ S)
    (hLow : HolderBound α ((S ×ˢ Set.univ) ∩ Q) (fun p => (u p,spatialD u p)) L) :
    HolderBound α Q (spatialCutoffCommutator a b φ u)
      (spatialCutoffCommutatorBudget n M E1 E2*L) := by
  let U : Set (Point n) := S ×ˢ Set.univ
  have hLow' : HolderBound α (U ∩ Q) (fun p => (u p,spatialD u p)) L :=
    hLow
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


/-- The cutoff commutator budget is linear in the coefficient budget. -/
theorem spatialCutoffCommutatorBudget_coeff_factor (n : ℕ) (M E1 E2 : ℝ) :
    spatialCutoffCommutatorBudget n M E1 E2 =
      spatialCutoffCommutatorBudget n 1 E1 E2*M := by
  dsimp only [spatialCutoffCommutatorBudget]
  ring

/-- The genuine cutoff support lies strictly inside the four-radius chart
buffer used by the physical boundary construction. -/
theorem outerPatchBump_tsupport_subset_four {n : ℕ} {r : ℝ} (hr : 0 < r)
    (z : Space n) : tsupport (outerPatchBump r hr z : Space n → ℝ) ⊆ Metric.closedBall z (4*r) := by
  rw [(outerPatchBump r hr z).tsupport_eq]
  apply Metric.closedBall_subset_closedBall
  change 2*r ≤ 4*r
  linarith

/-- Actual local chart geometry controls the physical commutator by the
small lower-pair input. Its constant precedes time, coefficients and the
model function, and is independent of the highest Schauder budget. -/
theorem outerPatchBump_chart_commutator_holder_budget {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z : Space n) {V : Set (Space n)} (hV : IsOpen V)
    (hBuffer : Metric.closedBall z (4*r) ⊆ V)
    {ψ : Space n → Space n} (hψ : ContDiffOn ℝ 3 ψ V) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ (O : Set (Space n)) (T M K L : ℝ)
        (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (v : Point n → ℝ),
        HolderBound α (cylinder (closure O) 0 T) a M →
        (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
        SchauderBound α (cylinder univ 0 T) v K →
        HolderBound α (cylinder univ 0 T) (fun p => (v p,spatialD v p)) L →
        HolderBound α (cylinder (closure O) 0 T)
          (spatialCutoffCommutator a b (outerPatchBump r hr z) (chartSpaceTimePullback ψ v))
          (Cgeom*M*L) := by
  obtain ⟨Cφ,hCφ,hCutoff⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨Cchart,hCchart,hChart⟩ := compact_chart_pullback_full_jet_budget hα hα1 hV
    (isCompact_closedBall z (4*r)) (convex_closedBall z (4*r)) hBuffer hψ
  let E1 : ℝ := 2*((r⁻¹)^2*Cφ)*r^(1-α)
  let E2 : ℝ := 2*((r⁻¹)^3*Cφ)*r^(1-α)
  let B : ℝ := spatialCutoffCommutatorBudget n 1 E1 E2
  have hE1 : 0 ≤ E1 := by dsimp only [E1]; positivity
  have hE2 : 0 ≤ E2 := by dsimp only [E2]; positivity
  have hB : 0 ≤ B := by dsimp only [B,spatialCutoffCommutatorBudget]; positivity
  refine ⟨1+B*Cchart,by positivity,?_⟩
  intro O T M K L a b v ha hb hv hvLow
  obtain ⟨hC2,hValue,hGrad,hHess,hTime,hLow⟩ :=
    hChart (Metric.closedBall z (4*r)) T K L v (Subset.refl _) hv hvLow
  have hφ := hCutoff r hr hr1 T z (outerPatchBump r hr z) (Or.inr rfl)
  have hSub : cylinder (closure O) 0 T ⊆ cylinder univ 0 T := fun p hp => ⟨mem_univ _,hp.2⟩
  have hLowLocal : HolderBound α
      (((Metric.closedBall z (4*r)) ×ˢ univ) ∩ cylinder (closure O) 0 T)
      (fun p => (chartSpaceTimePullback ψ v p,spatialD (chartSpaceTimePullback ψ v) p))
      (Cchart*L) := holderBound_mono hLow (fun p hp => ⟨hp.1.1,hp.2.2⟩)
  have hError := spatialCutoffCommutator_holderBound_on ha hb
    (holderBound_mono hφ.2.1 hSub) (holderBound_mono hφ.2.2 hSub)
    (outerPatchBump_tsupport_subset_four hr z) hLowLocal
  apply holderBound_mono_const hError
  rw [spatialCutoffCommutatorBudget_coeff_factor]
  change B*M*(Cchart*L) ≤ (1+B*Cchart)*M*L
  calc
    B*M*(Cchart*L) = (B*Cchart)*M*L := by ring
    _ ≤ (1+B*Cchart)*M*L := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) ha.1) hvLow.1

/-- Interior patches require only the ambient lower pair; no highest jet
budget enters their physical cutoff error. -/
theorem outerPatchBump_commutator_holder_budget {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (z : Space n) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ (O : Set (Space n)) (T M L : ℝ)
        (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ),
        HolderBound α (cylinder (closure O) 0 T) a M →
        (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
        HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p)) L →
        HolderBound α (cylinder (closure O) 0 T)
          (spatialCutoffCommutator a b (outerPatchBump r hr z) u) (Cgeom*M*L) := by
  obtain ⟨Cφ,hCφ,hCutoff⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  let E1 : ℝ := 2*((r⁻¹)^2*Cφ)*r^(1-α)
  let E2 : ℝ := 2*((r⁻¹)^3*Cφ)*r^(1-α)
  let B : ℝ := spatialCutoffCommutatorBudget n 1 E1 E2
  have hE1 : 0 ≤ E1 := by dsimp only [E1]; positivity
  have hE2 : 0 ≤ E2 := by dsimp only [E2]; positivity
  have hB : 0 ≤ B := by dsimp only [B,spatialCutoffCommutatorBudget]; positivity
  refine ⟨1+B,by positivity,?_⟩
  intro O T M L a b u ha hb hu
  have hφ := hCutoff r hr hr1 T z (outerPatchBump r hr z) (Or.inr rfl)
  have hSub : cylinder (closure O) 0 T ⊆ cylinder univ 0 T := fun p hp => ⟨mem_univ _,hp.2⟩
  have hLow : HolderBound α ((univ ×ˢ univ) ∩ cylinder (closure O) 0 T)
      (fun p => (u p,spatialD u p)) L := holderBound_mono hu (fun p hp => ⟨mem_univ _,hp.2.2⟩)
  have hError := spatialCutoffCommutator_holderBound_on ha hb
    (holderBound_mono hφ.2.1 hSub) (holderBound_mono hφ.2.2 hSub) (subset_univ _) hLow
  apply holderBound_mono_const hError
  rw [spatialCutoffCommutatorBudget_coeff_factor]
  change B*M*L ≤ (1+B)*M*L
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ha.1) hu.1

/-- A genuinely zero entire spatial slice has zero spatial gradient, so
its actual cutoff commutator vanishes without any PDE or jet assumption. -/
theorem spatialCutoffCommutator_zero_on_time_slice {n : ℕ}
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (φ : Space n → ℝ)
    {u : Point n → ℝ} {τ : ℝ} (hzero : ∀ x, u (x,τ) = 0) (x : Space n) :
    spatialCutoffCommutator a b φ u (x,τ) = 0 := by
  have hSlice : (fun y => u (y,τ)) = (fun _ => 0) := funext hzero
  have hD : spatialD u (x,τ) = 0 := by
    dsimp only [spatialD]
    rw [hSlice]
    simp
  simp only [spatialCutoffCommutator,hzero,hD,zero_apply,mul_zero,zero_mul,
    add_zero,Finset.sum_const_zero]

theorem spatialCutoffCommutator_initial_zero {n : ℕ}
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (φ : Space n → ℝ)
    {u : Point n → ℝ} (hzero : ∀ x, u (x,0) = 0) (x : Space n) :
    spatialCutoffCommutator a b φ u (x,0) = 0 :=
  spatialCutoffCommutator_zero_on_time_slice a b φ hzero x

theorem chart_spatialCutoffCommutator_initial_zero {n : ℕ}
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (φ : Space n → ℝ)
    (ψ : Space n → Space n) {v : Point n → ℝ} (hzero : ∀ x, v (x,0) = 0) (x : Space n) :
    spatialCutoffCommutator a b φ (chartSpaceTimePullback ψ v) (x,0) = 0 := by
  apply spatialCutoffCommutator_initial_zero a b φ _ x
  intro y
  exact hzero (ψ y)

end Yau.LeafProofs.L16Aux
