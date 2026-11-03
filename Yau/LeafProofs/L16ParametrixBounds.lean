import Yau.LeafProofs.L16ResidualEstimates

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem constantHeatNormFactor_pos {n : ℕ} (α : ℝ) (B : Space n ≃L[ℝ] Space n) :
    0 < constantHeatNormFactor α B := by
  dsimp only [constantHeatNormFactor]
  positivity

theorem constantHeatNormFactor_le {n : ℕ} {α R S : ℝ} (hα : 0 ≤ α)
    (B : Space n ≃L[ℝ] Space n) (hB : ‖(B : Space n →L[ℝ] Space n)‖ ≤ R)
    (hBI : ‖(B.symm : Space n →L[ℝ] Space n)‖ ≤ S) :
    constantHeatNormFactor α B ≤ (1+R^α)*(1+S)^2*(1+S^α) := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hB
  have hS : 0 ≤ S := (norm_nonneg _).trans hBI
  have hBP := Real.rpow_le_rpow (norm_nonneg _) hB hα
  have hBIP := Real.rpow_le_rpow (norm_nonneg _) hBI hα
  have hBISq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖(B.symm : Space n →L[ℝ] Space n)‖)
    (add_le_add le_rfl hBI) 2
  exact mul_le_mul
    (mul_le_mul (add_le_add le_rfl hBP) hBISq (sq_nonneg _) (by positivity))
    (add_le_add le_rfl hBIP) (by positivity) (by positivity)

theorem schauderBound_mono_const {n : ℕ} {α C D : ℝ} {Q : Set (Point n)}
    {u : Point n → ℝ} (hu : SchauderBound α Q u C) (hCD : C ≤ D) :
    SchauderBound α Q u D :=
  ⟨hu.1,hu.2.1.trans hCD,
    fun p hp => ⟨(hu.2.2.1 p hp).1.trans hCD,(hu.2.2.1 p hp).2.trans hCD⟩,
    holderBound_mono_const hu.2.2.2.1 hCD,holderBound_mono_const hu.2.2.2.2 hCD⟩

theorem constantHeatDuhamel_controlled_bounds {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ) (B : Space n ≃L[ℝ] Space n),
      constantHeatNormFactor α B ≤ N → ∀ T F : ℝ, 0 < T → T ≤ 1 →
      ∀ f : Point n → ℝ, HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (constantHeatDuhamel B f) (C*F*N) ∧
      (∀ p ∈ cylinder Set.univ 0 T, ‖spatialDD (constantHeatDuhamel B f) p‖ ≤ C*F*N*T^(α/2)) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (constantHeatDuhamel B f p,spatialD (constantHeatDuhamel B f) p))
        (C*F*N*(T^(1/2:ℝ)+T^((1-α)/2))) := by
  obtain ⟨CS,hCS,hS⟩ := constantHeatDuhamel_schauderBound (n := n) hα hα1
  obtain ⟨CD,hCD,hD⟩ := constantHeatDuhamel_small_jet_bounds (n := n) hα
  obtain ⟨CJ,hCJ,hJ⟩ := constantHeatDuhamel_first_jet_holderBound (n := n) hα hα1
  let C : ℝ := 1+CS+CD+CJ
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCSC : CS ≤ C := by dsimp only [C]; linarith
  have hCDC : CD ≤ C := by dsimp only [C]; linarith
  have hCJC : CJ ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro N B hN T F hT hT1 f hf
  have hNF : 0 ≤ constantHeatNormFactor α B := (constantHeatNormFactor_pos α B).le
  have hN0 : 0 ≤ N := hNF.trans hN
  have hCFN : 0 ≤ C*F*N := mul_nonneg (mul_nonneg hC.le hf.1) hN0
  have hBudget {A : ℝ} (hAC : A ≤ C) : A*F*constantHeatNormFactor α B ≤ C*F*N :=
    mul_le_mul (mul_le_mul_of_nonneg_right hAC hf.1) hN hNF (mul_nonneg hC.le hf.1)
  have hSRaw := hS B T F hT hT1 f hf
  have hScale : CS*F*(1+‖(B : Space n →L[ℝ] Space n)‖^α)*
      (1+‖(B.symm : Space n →L[ℝ] Space n)‖)^2*
      (1+‖(B.symm : Space n →L[ℝ] Space n)‖^α) = CS*F*constantHeatNormFactor α B := by
    dsimp only [constantHeatNormFactor]
    ring
  rw [hScale] at hSRaw
  refine ⟨schauderBound_mono_const hSRaw (hBudget hCSC),?_,?_⟩
  · intro p hp
    have hSmall := (hD B T F hT.le f hf p hp).2.2
    have hPow : p.2^(α/2) ≤ T^(α/2) :=
      Real.rpow_le_rpow hp.2.1 hp.2.2 (by positivity)
    exact (hSmall.trans (mul_le_mul_of_nonneg_right (hBudget hCDC)
      (Real.rpow_nonneg hp.2.1 _))).trans (mul_le_mul_of_nonneg_left hPow hCFN)
  · apply holderBound_mono_const (hJ B T F hT hT1 f hf)
    exact mul_le_mul_of_nonneg_right (hBudget hCJC) (by positivity)

theorem source_cutoffs_uniform_holderBound {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ P : ℝ, 0 < P ∧ ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) → ∀ T : ℝ,
      (∀ c : Space n, HolderBound α (cylinder Set.univ 0 T)
        (fun p => normalizedPatchCutoff s r hr c p.1) (P*r⁻¹*r^(1-α))) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => exteriorSourceCutoff s r hr p.1) (P*r⁻¹*r^(1-α)) := by
  obtain ⟨PI,hPI,hInterior⟩ := normalizedPatchCutoff_uniform_holderBound (n := n) hα hα1
  obtain ⟨PE,hPE,hExterior⟩ := exteriorSourceCutoff_uniform_holderBound (n := n) hα hα1
  let P : ℝ := PI+PE
  have hP : 0 < P := add_pos hPI hPE
  refine ⟨P,hP,?_⟩
  intro s r hr hr1 hSep T
  have hMono {A : ℝ} (hAP : A ≤ P) : A*r⁻¹*r^(1-α) ≤ P*r⁻¹*r^(1-α) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAP (inv_nonneg.mpr hr.le))
      (Real.rpow_nonneg hr.le _)
  constructor
  · intro c
    exact holderBound_mono_const (hInterior s r hr hr1 hSep T c) (hMono (by dsimp only [P]; linarith))
  · exact holderBound_mono_const (hExterior s r hr hr1 hSep T) (hMono (by dsimp only [P]; linarith))

def cutoffJetBudget (α C r : ℝ) (k : ℕ) : ℝ :=
  2*((r⁻¹)^(k+1)*C)*r^(1-α)

def lowerCutoffBudget (n : ℕ) (M E0 E1 E2 : ℝ) : ℝ :=
  4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E0+
  8*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*E1+
  4*(Fintype.card (Yau.RIdx n) : ℝ)^2*M*E2+
  4*(Fintype.card (Yau.RIdx n) : ℝ)*M*E1

def interiorResidualRate (n : ℕ) (α P Cφ CH M L N r T : ℝ) : ℝ :=
  let E0 := cutoffJetBudget α Cφ r 0
  let E1 := cutoffJetBudget α Cφ r 1
  let E2 := cutoffJetBudget α Cφ r 2
  let G := CH*(2*(P*r⁻¹*r^(1-α)))*N
  (Fintype.card (Yau.RIdx n) : ℝ)^2*
      (L*(2*r+T)*G+(4*E0*M)*(G*T^(α/2)))+
    lowerCutoffBudget n M E0 E1 E2*(G*(T^(1/2:ℝ)+T^((1-α)/2)))

/-- The actual frozen heat error has an explicit rate linear in the
source budget. All constants are chosen before the finite localization. -/
theorem interiorHeatResidual_uniform_bound {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ P Cφ CH : ℝ, 0 < P ∧ 0 < Cφ ∧ 0 < CH ∧
      ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) →
      ∀ (T F M L N : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (B : Space n ≃L[ℝ] Space n) (c : Space n) (f : Point n → ℝ),
      0 < T → T ≤ 1 → 0 ≤ L → constantHeatNormFactor α B ≤ N →
      HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T, ‖a p-a q‖ ≤ L*‖p-q‖) →
      HolderBound α (cylinder Set.univ 0 T) f F →
      HolderBound α (cylinder Set.univ 0 T)
        (frozenPatchResidual (cylinder Set.univ 0 T) a b (a (c,0)) (outerPatchBump r hr c)
          (constantHeatDuhamel B (fun p => normalizedPatchCutoff s r hr c p.1*f p)))
        (interiorResidualRate n α P Cφ CH M L N r T*F) := by
  obtain ⟨P,hP,hSource⟩ := source_cutoffs_uniform_holderBound (n := n) hα hα1
  obtain ⟨Cφ,hCφ,hCutoff⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨CH,hCH,hHeat⟩ := constantHeatDuhamel_controlled_bounds (n := n) hα hα1
  refine ⟨P,Cφ,CH,hP,hCφ,hCH,?_⟩
  intro s r hr hr1 hSep T F M L N a b B c f hT hT1 hL hN ha hb hLip hf
  let E0 := cutoffJetBudget α Cφ r 0
  let E1 := cutoffJetBudget α Cφ r 1
  let E2 := cutoffJetBudget α Cφ r 2
  let W : ℝ := 2*(P*r⁻¹*r^(1-α))
  let G : ℝ := CH*W*N
  let w : Point n → ℝ := fun p => normalizedPatchCutoff s r hr c p.1*f p
  let u : Point n → ℝ := constantHeatDuhamel B w
  have hWeighted : HolderBound α (cylinder Set.univ 0 T) w (W*F) :=
    holderBound_mul ((hSource s r hr hr1 hSep T).1 c) hf
  have hHeatBounds := hHeat N B hN T (W*F) hT hT1 w hWeighted
  have hHeatScale : CH*(W*F)*N = G*F := by dsimp only [G]; ring
  rw [hHeatScale] at hHeatBounds
  have hCut := hCutoff r hr hr1 T c _ (Or.inr rfl)
  have hφ : HolderBound α (cylinder Set.univ 0 T) (fun p => outerPatchBump r hr c p.1) E0 := by
    simpa only [E0,cutoffJetBudget,Nat.zero_add,pow_one] using hCut.1
  have hφD : HolderBound α (cylinder Set.univ 0 T)
      (fun p => fderiv ℝ (outerPatchBump r hr c) p.1) E1 := by
    simpa only [E1,cutoffJetBudget] using hCut.2.1
  have hφDD : HolderBound α (cylinder Set.univ 0 T)
      (fun p => fderiv ℝ (fderiv ℝ (outerPatchBump r hr c)) p.1) E2 := by
    simpa only [E2,cutoffJetBudget] using hCut.2.2
  have hOrigin : (c,(0 : ℝ)) ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,le_rfl,hT.le⟩
  have hA0 : 0 ≤ L*(2*r+T) := mul_nonneg hL (by positivity)
  have hD0 : 0 ≤ G*F*T^(α/2) :=
    mul_nonneg hHeatBounds.1.2.1 (Real.rpow_nonneg hT.le _)
  have hCoeff (i j : Yau.RIdx n) := frozen_patch_coefficient_holderBound ha hφ c 0 hOrigin i j
  have hCoeffSup (i j : Yau.RIdx n) (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) :
      |outerPatchBump r hr c p.1*(a (c,0) i j-a p i j)| ≤ L*(2*r+T) := by
    apply frozen_patch_coefficient_sup_bound hL hr hLip c hOrigin hp
    simpa only [sub_zero,abs_of_nonneg hp.2.1] using hp.2.2
  have hBound := frozenPatchResidual_holderBound hA0 hD0 ha hb hφ
    (fun i => holderBound_gradient_component hφD i)
    (fun i j => holderBound_hessian_component hφDD i j)
    hHeatBounds.2.2 hHeatBounds.1.2.2.2.1 hHeatBounds.2.1 hCoeff hCoeffSup
  change HolderBound α (cylinder Set.univ 0 T)
    (frozenPatchResidual (cylinder Set.univ 0 T) a b (a (c,0)) (outerPatchBump r hr c) u) _
  convert hBound using 1
  dsimp only [interiorResidualRate,lowerCutoffBudget,E0,E1,E2,G,W]
  ring

def exteriorResidualRate (n : ℕ) (α P CH M N r T E0 E1 E2 : ℝ) : ℝ :=
  lowerCutoffBudget n M E0 E1 E2*
    ((CH*(2*(P*r⁻¹*r^(1-α)))*N)*(T^(1/2:ℝ)+T^((1-α)/2)))

theorem exteriorHeatResidual_uniform_bound {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ P CH : ℝ, 0 < P ∧ 0 < CH ∧
      ∀ (s : Finset (Space n)) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) →
      ∃ E0 E1 E2 : ℝ, 0 < E0 ∧ 0 < E1 ∧ 0 < E2 ∧
      ∀ (K : Set (Space n)) (T F M N : ℝ) (a : Point n → Mat n)
        (b : Point n → Yau.RIdx n → ℝ) (B : Space n ≃L[ℝ] Space n) (f : Point n → ℝ),
      0 < T → T ≤ 1 → constantHeatNormFactor α B ≤ N →
      (∀ x ∈ K, 1 ≤ patchSum s r hr x) →
      HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      HolderBound α (cylinder Set.univ 0 T) f F →
      HolderBound α (cylinder Set.univ 0 T)
        (frozenPatchResidual (cylinder Set.univ 0 T) a b 1 (exteriorCutoff s r hr)
          (constantHeatDuhamel B (fun p => exteriorSourceCutoff s r hr p.1*f p)))
        (exteriorResidualRate n α P CH M N r T E0 E1 E2*F) := by
  obtain ⟨P,hP,hSource⟩ := source_cutoffs_uniform_holderBound (n := n) hα hα1
  obtain ⟨CH,hCH,hHeat⟩ := constantHeatDuhamel_controlled_bounds (n := n) hα hα1
  refine ⟨P,CH,hP,hCH,?_⟩
  intro s r hr hr1 hSep
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hφ0,hφD0,hφDD0⟩ := exteriorCutoff_holder_jets hα hα1 s hr
  refine ⟨E0,E1,E2,hE0,hE1,hE2,?_⟩
  intro K T F M N a b B f hT hT1 hN hCover ha hb hExterior hf
  let W : ℝ := 2*(P*r⁻¹*r^(1-α))
  let G : ℝ := CH*W*N
  let w : Point n → ℝ := fun p => exteriorSourceCutoff s r hr p.1*f p
  let u : Point n → ℝ := constantHeatDuhamel B w
  have hWeighted : HolderBound α (cylinder Set.univ 0 T) w (W*F) :=
    holderBound_mul (hSource s r hr hr1 hSep T).2 hf
  have hHeatBounds := hHeat N B hN T (W*F) hT hT1 w hWeighted
  have hHeatScale : CH*(W*F)*N = G*F := by dsimp only [G]; ring
  rw [hHeatScale] at hHeatBounds
  have hφ := holderBound_mono hφ0 (cylinder_mono_time hT1)
  have hφD := holderBound_mono hφD0 (cylinder_mono_time hT1)
  have hφDD := holderBound_mono hφDD0 (cylinder_mono_time hT1)
  have hLower := lowerPatchResidual_holderBound ha hb hφ
    (fun i => holderBound_gradient_component hφD i)
    (fun i j => holderBound_hessian_component hφDD i j) hHeatBounds.2.2
  have hResidual := holderBound_congr_on (holderBound_neg hLower) (show
      Set.EqOn (fun p => -lowerPatchResidual a b (exteriorCutoff s r hr) u p)
        (frozenPatchResidual (cylinder Set.univ 0 T) a b 1 (exteriorCutoff s r hr) u)
        (cylinder Set.univ 0 T) from by
    intro p hp
    exact (exterior_frozenPatchResidual_eq_neg_lower b s hr hCover hExterior u hp).symm)
  change HolderBound α (cylinder Set.univ 0 T)
    (frozenPatchResidual (cylinder Set.univ 0 T) a b 1 (exteriorCutoff s r hr) u) _
  convert hResidual using 1
  dsimp only [exteriorResidualRate,lowerCutoffBudget,G,W]
  ring

theorem interiorResidualRate_nonneg (n : ℕ) {α P Cφ CH M L N r T : ℝ}
    (hP : 0 ≤ P) (hCφ : 0 ≤ Cφ) (hCH : 0 ≤ CH) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (hN : 0 ≤ N) (hr : 0 ≤ r) (hT : 0 ≤ T) :
    0 ≤ interiorResidualRate n α P Cφ CH M L N r T := by
  dsimp only [interiorResidualRate,lowerCutoffBudget,cutoffJetBudget]
  positivity

theorem exteriorResidualRate_nonneg (n : ℕ) {α P CH M N r T E0 E1 E2 : ℝ}
    (hP : 0 ≤ P) (hCH : 0 ≤ CH) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hr : 0 ≤ r) (hT : 0 ≤ T) (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) :
    0 ≤ exteriorResidualRate n α P CH M N r T E0 E1 E2 := by
  dsimp only [exteriorResidualRate,lowerCutoffBudget]
  positivity

theorem interiorResidualRate_zero (n : ℕ) {α r : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hr : r ≠ 0) (P Cφ CH M L N : ℝ) :
    interiorResidualRate n α P Cφ CH M L N r 0 =
      4*(Fintype.card (Yau.RIdx n) : ℝ)^2*L*CH*P*N*r^(1-α) := by
  have hα2 : α/2 ≠ 0 := ne_of_gt (by positivity)
  have hHalf : (1/2 : ℝ) ≠ 0 := by norm_num
  have hRest : (1-α)/2 ≠ 0 := ne_of_gt (by linarith)
  simp only [interiorResidualRate,Real.zero_rpow hα2,Real.zero_rpow hHalf,
    Real.zero_rpow hRest,mul_zero,add_zero]
  field_simp
  ring

theorem exteriorResidualRate_zero (n : ℕ) {α : ℝ} (hα1 : α < 1)
    (P CH M N r E0 E1 E2 : ℝ) :
    exteriorResidualRate n α P CH M N r 0 E0 E1 E2 = 0 := by
  have hHalf : (1/2 : ℝ) ≠ 0 := by norm_num
  have hRest : (1-α)/2 ≠ 0 := ne_of_gt (by linarith)
  simp only [exteriorResidualRate,Real.zero_rpow hHalf,Real.zero_rpow hRest,
    zero_add,mul_zero]

theorem interiorResidualRate_continuous (n : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (P Cφ CH M L N r : ℝ) :
    Continuous (fun T => interiorResidualRate n α P Cφ CH M L N r T) := by
  have hA : Continuous (fun T : ℝ => T^(α/2)) := Real.continuous_rpow_const (by positivity)
  have hB : Continuous (fun T : ℝ => T^(1/2 : ℝ)) := Real.continuous_rpow_const (by positivity)
  have hC : Continuous (fun T : ℝ => T^((1-α)/2)) := Real.continuous_rpow_const (by linarith)
  dsimp only [interiorResidualRate]
  fun_prop

theorem exteriorResidualRate_continuous (n : ℕ) {α : ℝ} (hα1 : α ≤ 1)
    (P CH M N r E0 E1 E2 : ℝ) :
    Continuous (fun T => exteriorResidualRate n α P CH M N r T E0 E1 E2) := by
  have hB : Continuous (fun T : ℝ => T^(1/2 : ℝ)) := Real.continuous_rpow_const (by positivity)
  have hC : Continuous (fun T : ℝ => T^((1-α)/2)) := Real.continuous_rpow_const (by linarith)
  dsimp only [exteriorResidualRate]
  fun_prop

def totalResidualRate (n : ℕ) (α PI Cφ CHI PE CHE M L N r T E0 E1 E2 : ℝ) : ℝ :=
  2*((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)*
      interiorResidualRate n α PI Cφ CHI M L N r T+
    exteriorResidualRate n α PE CHE M N r T E0 E1 E2

theorem totalResidualRate_zero (n : ℕ) {α r : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hr : r ≠ 0) (PI Cφ CHI PE CHE M L N E0 E1 E2 : ℝ) :
    totalResidualRate n α PI Cφ CHI PE CHE M L N r 0 E0 E1 E2 =
      (8*((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)*
        (Fintype.card (Yau.RIdx n) : ℝ)^2*L*CHI*PI*N)*r^(1-α) := by
  rw [totalResidualRate,interiorResidualRate_zero n hα hα1 hr,
    exteriorResidualRate_zero n hα1]
  ring

theorem totalResidualRate_continuous (n : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (PI Cφ CHI PE CHE M L N r E0 E1 E2 : ℝ) :
    Continuous (fun T => totalResidualRate n α PI Cφ CHI PE CHE M L N r T E0 E1 E2) := by
  exact (continuous_const.mul
    (interiorResidualRate_continuous n hα hα1 PI Cφ CHI M L N r)).add
    (exteriorResidualRate_continuous n hα1 PE CHE M N r E0 E1 E2)

/-- A closed positive time interval can be chosen inside any strict
continuous bound at zero. -/
theorem exists_small_positive_interval {f : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousAt f 0) (hc : f 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 0 ≤ t → t ≤ δ → f t < c := by
  have hE : ∀ᶠ t in 𝓝 (0 : ℝ), f t < c := hf.eventually (Iio_mem_nhds hc)
  obtain ⟨ε,hε,hBall⟩ := Metric.eventually_nhds_iff.mp hE
  let δ : ℝ := min ε 1 / 2
  have hδ : 0 < δ := div_pos (lt_min hε (by norm_num)) (by norm_num)
  have hδε : δ < ε := by
    dsimp only [δ]
    have := min_le_left ε (1 : ℝ)
    linarith [lt_min hε (by norm_num : (0 : ℝ) < 1)]
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    linarith [min_le_right ε (1 : ℝ)]
  refine ⟨δ,hδ,hδ1,?_⟩
  intro t ht htδ
  apply hBall
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ht] using htδ.trans_lt hδε

/-- The radius is selected before the exterior-cutoff constants. Only
after those constants are fixed is the small time interval chosen. -/
theorem exists_localization_contraction_scales (n : ℕ) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (PI Cφ CHI PE CHE M L N : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ E0 E1 E2 : ℝ,
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ T : ℝ, 0 ≤ T → T ≤ δ →
        totalResidualRate n α PI Cφ CHI PE CHE M L N r T E0 E1 E2 ≤ 1/2 := by
  let A : ℝ := 8*((5^(Module.finrank ℝ (Space n)) : ℕ) : ℝ)*
    (Fintype.card (Yau.RIdx n) : ℝ)^2*L*CHI*PI*N
  have hLead : ContinuousAt (fun r : ℝ => A*r^(1-α)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 (1-α) (Or.inr (by linarith)))
  have hLead0 : A*(0 : ℝ)^(1-α) < (1/4 : ℝ) := by
    rw [Real.zero_rpow (by linarith : 1-α ≠ 0),mul_zero]
    norm_num
  obtain ⟨ρ,hρ,hρ1,hSmall⟩ := exists_small_positive_interval hLead hLead0
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro E0 E1 E2
  have hZero : totalResidualRate n α PI Cφ CHI PE CHE M L N ρ 0 E0 E1 E2 < 1/2 := by
    rw [totalResidualRate_zero n hα hα1 hρ.ne']
    exact (hSmall ρ hρ.le le_rfl).trans (by norm_num)
  obtain ⟨δ,hδ,hδ1,hTime⟩ := exists_small_positive_interval
    (totalResidualRate_continuous n hα.le hα1.le PI Cφ CHI PE CHE M L N ρ E0 E1 E2).continuousAt hZero
  exact ⟨δ,hδ,hδ1,fun T hT hTδ => (hTime T hT hTδ).le⟩

def localizedHeatResidual {n : ℕ} (T : ℝ) (s : Finset (Space n))
    (r : ℝ) (hr : 0 < r) (B : Space n → Space n ≃L[ℝ] Space n)
    (Bext : Space n ≃L[ℝ] Space n) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ) (p : Point n) : ℝ :=
  (∑ c ∈ s, frozenPatchResidual (cylinder Set.univ 0 T) a b (a (c,0))
    (outerPatchBump r hr c)
    (constantHeatDuhamel (B c) (fun q => normalizedPatchCutoff s r hr c q.1*f q)) p)+
  frozenPatchResidual (cylinder Set.univ 0 T) a b 1 (exteriorCutoff s r hr)
    (constantHeatDuhamel Bext (fun q => exteriorSourceCutoff s r hr q.1*f q)) p

/-- The error of the genuine finite frozen-coefficient parametrix has
operator budget one half on a sufficiently short slab. The radius and
cover are selected before the time length, and no compact support of
the right-hand side is required. -/
theorem exists_localizedHeatResidual_half_bound {n : ℕ} {α M L N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hL : 0 ≤ L)
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ (r : ℝ) (hr : 0 < r) (s : Finset (Space n)), r ≤ 1 ∧
      (∀ c ∈ s, c ∈ K) ∧ (∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖) ∧
      (∀ x ∈ K, 1 ≤ patchSum s r hr x) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (B : Space n → Space n ≃L[ℝ] Space n)
        (Bext : Space n ≃L[ℝ] Space n) (f : Point n → ℝ) (F : ℝ),
      0 < T → T ≤ δ →
      HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
        ‖a p-a q‖ ≤ L*‖p-q‖) →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      (∀ c, constantHeatNormFactor α (B c) ≤ N) →
      constantHeatNormFactor α Bext ≤ N → HolderBound α (cylinder Set.univ 0 T) f F →
      HolderBound α (cylinder Set.univ 0 T)
        (localizedHeatResidual T s r hr B Bext a b f) (F/2) := by
  obtain ⟨PI,Cφ,CHI,hPI,hCφ,hCHI,hInterior⟩ := interiorHeatResidual_uniform_bound (n := n) hα hα1
  obtain ⟨PE,CHE,hPE,hCHE,hExteriorBound⟩ := exteriorHeatResidual_uniform_bound (n := n) hα hα1
  obtain ⟨r,hr,hr1,hScale⟩ :=
    exists_localization_contraction_scales n hα hα1 PI Cφ CHI PE CHE M L N
  obtain ⟨s,hsK,hSep,hCover,_,_⟩ := compact_separated_patch_partition hK hr
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hExt⟩ := hExteriorBound s r hr hr1 hSep
  obtain ⟨δ,hδ,hδ1,hRate⟩ := hScale E0 E1 E2
  refine ⟨r,hr,s,hr1,hsK,hSep,hCover,δ,hδ,hδ1,?_⟩
  intro T a b B Bext f F hT hTδ ha hb hLip hExterior hB hBext hf
  have hT1 : T ≤ 1 := hTδ.trans hδ1
  have hNT : 0 ≤ N := (constantHeatNormFactor_pos α Bext).le.trans hBext
  have hIntRate : 0 ≤ interiorResidualRate n α PI Cφ CHI M L N r T :=
    interiorResidualRate_nonneg n hPI.le hCφ.le hCHI.le ha.1 hL hNT hr.le hT.le
  have hInt := frozenPatchResidual_outer_sum_holderBound a b (fun c => a (c,0))
    (fun c => constantHeatDuhamel (B c) (fun q => normalizedPatchCutoff s r hr c q.1*f q))
    hr s hSep (mul_nonneg hIntRate hf.1) (fun c _ =>
      hInterior s r hr hr1 hSep T F M L N a b (B c) c f hT hT1 hL (hB c)
        ha hb hLip hf)
  have hExtBound := hExt K T F M N a b Bext f hT hT1 hBext hCover ha hb hExterior hf
  have hTotal := holderBound_add hInt hExtBound
  change HolderBound α (cylinder Set.univ 0 T) (localizedHeatResidual T s r hr B Bext a b f) _ at hTotal
  apply holderBound_mono_const hTotal
  have hFinal := mul_le_mul_of_nonneg_right (hRate T hT.le hTδ) hf.1
  convert hFinal using 1 <;> (try dsimp only [totalResidualRate]) <;> ring

end Yau.LeafProofs.L16Aux
