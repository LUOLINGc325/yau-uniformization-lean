import Yau.LeafProofs.L16HolderExtension
import Yau.LeafProofs.L16RelativeCutoffExtension
import Yau.LeafProofs.L16ParametrixRegularity

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance cutoffFull_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance cutoffFull_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance cutoffFull_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance cutoffFull_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- A bilinear cutoff field extends local Holder data across its zero region. -/
theorem holderBound_bilinear_cutoff_extension {n : ℕ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    {α P K : ℝ} {U Q : Set (Point n)} {a : Point n → E} {v : Point n → F}
    (B : E → F → G)
    (hSubLeft : ∀ x y z, B (x-y) z = B x z-B y z)
    (hSubRight : ∀ x y z, B x (y-z) = B x y-B x z)
    (hZero : ∀ z, B 0 z = 0)
    (hNorm : ∀ x y, ‖B x y‖ ≤ ‖x‖*‖y‖)
    (ha : HolderBound α Q a P) (hv : HolderBound α (U∩Q) v K)
    (haZero : ∀ p ∈ Q, p ∉ U → a p = 0) :
    HolderBound α Q (fun p => B (a p) (v p)) (2*P*K) := by
  have hP := ha.1
  have hK := hv.1
  have hW (p q : Point n) : 0 ≤ holderWeight α p q := by
    dsimp [holderWeight]; positivity
  have hInside (p q : Point n) (hp : p ∈ U∩Q) (hq : q ∈ U∩Q) :
      ‖B (a p) (v p)-B (a q) (v q)‖ ≤ 2*P*K*holderWeight α p q := by
    have heq : B (a p) (v p)-B (a q) (v q) =
        B (a p) (v p-v q)+B (a p-a q) (v q) := by
      rw [hSubRight,hSubLeft]; abel
    rw [heq]
    calc
      _ ≤ ‖B (a p) (v p-v q)‖+‖B (a p-a q) (v q)‖ := norm_add_le _ _
      _ ≤ ‖a p‖*‖v p-v q‖+‖a p-a q‖*‖v q‖ := add_le_add (hNorm _ _) (hNorm _ _)
      _ ≤ P*(K*holderWeight α p q)+(P*holderWeight α p q)*K :=
        add_le_add
          (mul_le_mul (ha.2.1 p hp.2) (hv.2.2 p hp q hq) (norm_nonneg _) hP)
          (mul_le_mul (ha.2.2 p hp.2 q hq.2) (hv.2.1 q hq) (norm_nonneg _)
            (mul_nonneg hP (hW p q)))
      _ = _ := by ring
  have hCross (p q : Point n) (hp : p ∈ U∩Q) (hq : q ∈ Q) (hqU : q ∉ U) :
      ‖B (a p) (v p)-B (a q) (v q)‖ ≤ 2*P*K*holderWeight α p q := by
    have hq0 := haZero q hq hqU
    have hd : ‖a p‖ ≤ P*holderWeight α p q := by
      simpa only [hq0,sub_zero] using ha.2.2 p hp.2 q hq
    rw [hq0,hZero,sub_zero]
    calc
      _ ≤ ‖a p‖*‖v p‖ := hNorm _ _
      _ ≤ (P*holderWeight α p q)*K :=
        mul_le_mul hd (hv.2.1 p hp) (norm_nonneg _) (mul_nonneg hP (hW p q))
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hP hK) (hW p q)]
  refine ⟨by positivity,?_,?_⟩
  · intro p hp
    by_cases hpU : p ∈ U
    · exact (hNorm _ _).trans ((mul_le_mul (ha.2.1 p hp) (hv.2.1 p ⟨hpU,hp⟩)
        (norm_nonneg _) hP).trans (by nlinarith [mul_nonneg hP hK]))
    · simp only [haZero p hp hpU,hZero,norm_zero]
      positivity
  · intro p hp q hq
    by_cases hpU : p ∈ U
    · by_cases hqU : q ∈ U
      · exact hInside p q ⟨hpU,hp⟩ ⟨hqU,hq⟩
      · exact hCross p q ⟨hpU,hp⟩ hq hqU
    · by_cases hqU : q ∈ U
      · simpa only [norm_sub_rev,holderWeight,abs_sub_comm] using hCross q p ⟨hqU,hq⟩ hp hpU
      · simp only [haZero p hp hpU,haZero q hq hqU,hZero,sub_self,norm_zero]
        exact mul_nonneg (by positivity) (hW p q)

theorem holderBound_clm_cutoff_extension {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α P K : ℝ} {U Q : Set (Point n)} {a : Point n → E →L[ℝ] F} {v : Point n → E}
    (ha : HolderBound α Q a P) (hv : HolderBound α (U∩Q) v K)
    (haZero : ∀ p ∈ Q, p ∉ U → a p = 0) :
    HolderBound α Q (fun p => a p (v p)) (2*P*K) := by
  apply holderBound_bilinear_cutoff_extension (fun a v => a v)
    (fun x y z => sub_apply x y z)
    (fun x y z => x.map_sub y z) (fun z => rfl)
    (fun a v => a.le_opNorm v) ha hv haZero

theorem holderBound_tensor_cutoff_extension {n : ℕ} {α P K : ℝ}
    {U Q : Set (Point n)} {a v : Point n → Space n →L[ℝ] ℝ}
    (ha : HolderBound α Q a P) (hv : HolderBound α (U∩Q) v K)
    (haZero : ∀ p ∈ Q, p ∉ U → a p = 0) :
    HolderBound α Q (fun p => (a p).smulRight (v p)) (2*P*K) := by
  apply holderBound_bilinear_cutoff_extension
    (fun (a v : Space n →L[ℝ] ℝ) => a.smulRight v)
  · intro x y z; ext s t
    simp only [sub_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
    ring
  · intro x y z; ext s t
    simp only [sub_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
    ring
  · intro z; ext s t
    simp [ContinuousLinearMap.smulRight_apply]
  · intro a v
    exact (ContinuousLinearMap.norm_smulRight_apply a v).le
  · exact ha
  · exact hv
  · exact haZero

theorem holderBound_tensor_flip_cutoff_extension {n : ℕ} {α P K : ℝ}
    {U Q : Set (Point n)} {a v : Point n → Space n →L[ℝ] ℝ}
    (ha : HolderBound α Q a P) (hv : HolderBound α (U∩Q) v K)
    (haZero : ∀ p ∈ Q, p ∉ U → a p = 0) :
    HolderBound α Q (fun p => (v p).smulRight (a p)) (2*P*K) := by
  apply holderBound_bilinear_cutoff_extension
    (fun (a v : Space n →L[ℝ] ℝ) => v.smulRight a)
  · intro x y z; ext s t
    simp only [sub_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
    ring
  · intro x y z; ext s t
    simp only [sub_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
    ring
  · intro z; ext s t
    simp [ContinuousLinearMap.smulRight_apply]
  · intro a v
    rw [ContinuousLinearMap.norm_smulRight_apply,mul_comm]
  · exact ha
  · exact hv
  · exact haZero

/-- Low-jet smallness is preserved without a Hessian Holder input. -/
theorem cutoff_low_pair_holder_extension {n : ℕ} {α E K l r : ℝ}
    {V : Set (Space n)} (hV : IsOpen V) {φ : Space n → ℝ} {u : Point n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hSupport : tsupport φ ⊆ V)
    (hu : C2 (cylinder V l r) u)
    (hφ0 : HolderBound α (cylinder Set.univ l r) (fun p => φ p.1) E)
    (hφ1 : HolderBound α (cylinder Set.univ l r) (fun p => fderiv ℝ φ p.1) E)
    (hu0 : HolderBound α (cylinder V l r) u K)
    (hu1 : HolderBound α (cylinder V l r) (spatialD u) K) :
    C2 (cylinder Set.univ l r) (fun p => φ p.1*u p) ∧
    HolderBound α (cylinder Set.univ l r) (fun p => φ p.1*u p) (4*E*K) ∧
    HolderBound α (cylinder Set.univ l r) (spatialD (fun p => φ p.1*u p)) (4*E*K) := by
  let Q := cylinder (Set.univ : Set (Space n)) l r
  let U := V ×ˢ (Set.univ : Set ℝ)
  have hU : U∩Q = cylinder V l r := by ext p; simp [U,Q,Parabolic.cylinder]
  have hφZero (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) : φ p.1 = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hpU ⟨hSupport h,Set.mem_univ _⟩
  have hφDZero (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) : fderiv ℝ φ p.1 = 0 := by
    apply fderiv_of_notMem_tsupport
    intro h
    exact hpU ⟨hSupport h,Set.mem_univ _⟩
  have hu0' : HolderBound α (U∩Q) u K := by simpa only [hU] using hu0
  have hu1' : HolderBound α (U∩Q) (spatialD u) K := by simpa only [hU] using hu1
  have h0 := holderBound_smul_cutoff_extension hφ0 hu0' hφZero
  have h10 := holderBound_smul_cutoff_extension hφ0 hu1' hφZero
  have h11 := holderBound_bilinear_cutoff_extension (fun a v => v • a)
    (fun x y z => smul_sub z x y) (fun x y z => sub_smul y z x)
    (fun z => smul_zero z)
    (fun a v => by rw [norm_smul,Real.norm_eq_abs,mul_comm]) hφ1 hu0' hφDZero
  have hGrad := holderBound_add h10 h11
  have hw : C2 Q (fun p => φ p.1*u p) := by
    apply c2_spatial_cutoff_relative_extension hV hφ hSupport
    simpa only [Set.univ_inter] using hu
  refine ⟨hw,?_,?_⟩
  · simpa only [smul_eq_mul] using holderBound_mono_const h0 (by nlinarith [mul_nonneg hφ0.1 hu0.1])
  · apply holderBound_congr_on (holderBound_mono_const hGrad (by ring_nf; rfl))
    intro p hp
    by_cases hpV : p.1 ∈ V
    · exact (fderiv_fun_mul (hφ.differentiable (by norm_num) p.1)
        ((hu.2.2.2.2.1 p ⟨hpV,hp.2⟩).differentiableAt (by norm_num))).symm
    · have hpSupport : p.1 ∉ tsupport φ := fun h => hpV (hSupport h)
      have hz := (spatial_cutoff_jets_zero_of_notMem_tsupport Q φ u hpSupport).2.1
      change φ p.1 • spatialD u p + u p • fderiv ℝ φ p.1 = spatialD (fun p => φ p.1*u p) p
      rw [hz,hφZero p hp (by simpa [U] using hpV),hφDZero p hp (by simpa [U] using hpV)]
      simp

theorem cutoff_full_jet_holder_extension {n : ℕ} {α E K l r : ℝ}
    {V : Set (Space n)} (hV : IsOpen V) {φ : Space n → ℝ} {u : Point n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hSupport : tsupport φ ⊆ V)
    (hu : C2 (cylinder V l r) u)
    (hφ0 : HolderBound α (cylinder Set.univ l r) (fun p => φ p.1) E)
    (hφ1 : HolderBound α (cylinder Set.univ l r) (fun p => fderiv ℝ φ p.1) E)
    (hφ2 : HolderBound α (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ φ) p.1) E)
    (hu0 : HolderBound α (cylinder V l r) u K)
    (hu1 : HolderBound α (cylinder V l r) (spatialD u) K)
    (hu2 : HolderBound α (cylinder V l r) (spatialDD u) K)
    (hut : HolderBound α (cylinder V l r) (timeD (cylinder V l r) u) K) :
    C2 (cylinder Set.univ l r) (fun p => φ p.1*u p) ∧
    HolderBound α (cylinder Set.univ l r) (fun p => φ p.1*u p) (8*E*K) ∧
    HolderBound α (cylinder Set.univ l r) (spatialD (fun p => φ p.1*u p)) (8*E*K) ∧
    HolderBound α (cylinder Set.univ l r) (spatialDD (fun p => φ p.1*u p)) (8*E*K) ∧
    HolderBound α (cylinder Set.univ l r) (timeD (cylinder Set.univ l r) (fun p => φ p.1*u p))
      (8*E*K) := by
  let Q := cylinder (Set.univ : Set (Space n)) l r
  let U := V ×ˢ (Set.univ : Set ℝ)
  have hU : U∩Q = cylinder V l r := by ext p; simp [U,Q,Parabolic.cylinder]
  have hOutside {p : Point n} (hpU : p ∉ U) : p.1 ∉ tsupport φ :=
    fun h => hpU ⟨hSupport h,Set.mem_univ _⟩
  have hφZero (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) : φ p.1 = 0 :=
    image_eq_zero_of_notMem_tsupport (hOutside hpU)
  have hφDZero (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) : fderiv ℝ φ p.1 = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) (hOutside hpU)
  have hφDDZero (p : Point n) (hp : p ∈ Q) (hpU : p ∉ U) :
      fderiv ℝ (fderiv ℝ φ) p.1 = 0 := by
    apply fderiv_of_notMem_tsupport
    intro h
    exact hOutside hpU (tsupport_fderiv_subset ℝ h)
  have hu0' : HolderBound α (U∩Q) u K := by simpa only [hU] using hu0
  have hu1' : HolderBound α (U∩Q) (spatialD u) K := by simpa only [hU] using hu1
  have hu2' : HolderBound α (U∩Q) (spatialDD u) K := by simpa only [hU] using hu2
  have hut' : HolderBound α (U∩Q) (timeD (cylinder V l r) u) K := by simpa only [hU] using hut
  have hLow := cutoff_low_pair_holder_extension hV hφ hSupport hu hφ0 hφ1 hu0 hu1
  have h20 := holderBound_smul_cutoff_extension hφ0 hu2' hφZero
  have h21 := holderBound_tensor_cutoff_extension hφ1 hu1' hφDZero
  have h22 := holderBound_tensor_flip_cutoff_extension hφ1 hu1' hφDZero
  have h23 := holderBound_bilinear_cutoff_extension
    (fun (a : Space n →L[ℝ] Space n →L[ℝ] ℝ) (v : ℝ) => v • a)
    (fun x y z => smul_sub z x y) (fun x y z => sub_smul y z x)
    (fun z => smul_zero z)
    (fun a v => by rw [norm_smul,Real.norm_eq_abs,mul_comm]) hφ2 hu0' hφDDZero
  have hH := holderBound_add (holderBound_add (holderBound_add h20 h21) h22) h23
  have ht := holderBound_smul_cutoff_extension hφ0 hut' hφZero
  refine ⟨hLow.1,holderBound_mono_const hLow.2.1 (by nlinarith [mul_nonneg hφ0.1 hu0.1]),
    holderBound_mono_const hLow.2.2 (by nlinarith [mul_nonneg hφ0.1 hu0.1]),?_,?_⟩
  · apply holderBound_congr_on (holderBound_mono_const hH (by ring_nf; rfl))
    intro p hp
    by_cases hpV : p.1 ∈ V
    · exact (secondFDeriv_mul hφ.contDiffAt (hu.2.2.2.2.1 p ⟨hpV,hp.2⟩)).symm
    · have hpU : p ∉ U := by simpa [U] using hpV
      have hz := (spatial_cutoff_jets_zero_of_notMem_tsupport Q φ u (hOutside hpU)).2.2.1
      change φ p.1 • spatialDD u p + (fderiv ℝ φ p.1).smulRight (spatialD u p) +
        (spatialD u p).smulRight (fderiv ℝ φ p.1) + u p • fderiv ℝ (fderiv ℝ φ) p.1 =
        spatialDD (fun p => φ p.1*u p) p
      rw [hz,hφZero p hp hpU,hφDZero p hp hpU,hφDDZero p hp hpU]
      simp
  · apply holderBound_congr_on (holderBound_mono_const ht (by nlinarith [mul_nonneg hφ0.1 hu0.1]))
    intro p hp
    by_cases hpV : p.1 ∈ V
    · rw [timeD_spatial_mul]
      rw [timeD_cylinder_change_space u (Set.mem_univ p.1) hpV]
      rfl
    · have hpU : p ∉ U := by simpa [U] using hpV
      have hz := (spatial_cutoff_jets_zero_of_notMem_tsupport Q φ u (hOutside hpU)).2.2.2
      change φ p.1 • timeD (cylinder V l r) u p = timeD Q (fun p => φ p.1*u p) p
      rw [hz,hφZero p hp hpU]
      simp

end Yau.LeafProofs.L16Aux
