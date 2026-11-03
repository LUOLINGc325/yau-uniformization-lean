import Yau.LeafProofs.L16LocalizedParametrix
import Yau.LeafProofs.L16ParametrixRegularity

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem localizedHeatParametrix_full_regularity {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n) :
    ∃ C : ℝ, 0 < C ∧ ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (localizedHeatParametrix s hr B Bext f) (C*F) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (localizedHeatParametrix s hr B Bext f p,
          spatialD (localizedHeatParametrix s hr B Bext f) p)) (C*F) := by
  obtain ⟨Cφ,hCφ,hCut⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hExt0,hExt1,hExt2⟩ := exteriorCutoff_holder_jets hα hα1 s hr
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  let I0 := cutoffJetBudget α Cφ r 0
  let I1 := cutoffJetBudget α Cφ r 1
  let I2 := cutoffJetBudget α Cφ r 2
  have hI0 : 0 ≤ I0 := by dsimp only [I0,cutoffJetBudget]; positivity
  have hI1 : 0 ≤ I1 := by dsimp only [I1,cutoffJetBudget]; positivity
  have hI2 : 0 ≤ I2 := by dsimp only [I2,cutoffJetBudget]; positivity
  let E : ℝ := 1+I0+I1+I2+E0+E1+E2
  have hE : 0 < E := by dsimp only [E]; linarith
  have hIE0 : I0 ≤ E := by dsimp only [E]; linarith
  have hIE1 : I1 ≤ E := by dsimp only [E]; linarith
  have hIE2 : I2 ≤ E := by dsimp only [E]; linarith
  have hEE0 : E0 ≤ E := by dsimp only [E]; linarith
  have hEE1 : E1 ≤ E := by dsimp only [E]; linarith
  have hEE2 : E2 ≤ E := by dsimp only [E]; linarith
  have hφ0 (i : Option (Space n)) : HolderBound α (cylinder Set.univ 0 1)
      (fun p => localizationOuter s hr i p.1) E := by
    cases i with
    | none => exact holderBound_mono_const hExt0 hEE0
    | some c =>
      have h := (hCut r hr hr1 1 c _ (Or.inr rfl)).1
      apply holderBound_mono_const h
      simpa only [I0,cutoffJetBudget,Nat.zero_add,pow_one] using hIE0
  have hφ1 (i : Option (Space n)) : HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (localizationOuter s hr i) p.1) E := by
    cases i with
    | none => exact holderBound_mono_const hExt1 hEE1
    | some c =>
      exact holderBound_mono_const (hCut r hr hr1 1 c _ (Or.inr rfl)).2.1 hIE1
  have hφ2 (i : Option (Space n)) : HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (fderiv ℝ (localizationOuter s hr i)) p.1) E := by
    cases i with
    | none => exact holderBound_mono_const hExt2 hEE2
    | some c =>
      exact holderBound_mono_const (hCut r hr hr1 1 c _ (Or.inr rfl)).2.2 hIE2
  have hPS : 0 < P*r⁻¹*r^(1-α) := by positivity
  exact finiteHeatParametrix_full_regularity hα hα1 (localizationIndices s)
    (localizationEquiv B Bext) (localizationOuter s hr) (localizationSource s hr) hE hPS
    (fun i _ => localizationOuter_contDiff s hr i) (fun i _ => hφ0 i)
    (fun i _ => hφ1 i) (fun i _ => hφ2 i) (fun i _ => hSource s r hr hr1 hSep 1 i)

def ellipticHeatNormBudget (α lam upper : ℝ) : ℝ :=
  (1+(max (Real.sqrt upper) 1)^α)*(1+max (Real.sqrt lam)⁻¹ 1)^2*
    (1+(max (Real.sqrt lam)⁻¹ 1)^α)

def localizationGramIdentity {n : ℕ} (s : Finset (Space n))
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (a : Point n → Mat n) : Prop :=
  ∀ i ∈ localizationIndices s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
    (∑ k : Yau.RIdx n, H (localizationEquiv B Bext i (Yau.realVec k))
      (localizationEquiv B Bext i (Yau.realVec k))) =
      ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n,
        localizationFrozenMatrix a i j k*H (Yau.realVec j) (Yau.realVec k)

theorem elliptic_localization_equivs {n : ℕ} {α T lam upper : ℝ}
    (hα : 0 ≤ α) (hT : 0 ≤ T) (a : Point n → Mat n)
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper) (s : Finset (Space n)) :
    ∃ B : Space n → Space n ≃L[ℝ] Space n,
      (∀ c, constantHeatNormFactor α (B c) ≤ ellipticHeatNormBudget α lam upper) ∧
      constantHeatNormFactor α (ContinuousLinearEquiv.refl ℝ (Space n)) ≤
        ellipticHeatNormBudget α lam upper ∧
      localizationGramIdentity s B (ContinuousLinearEquiv.refl ℝ (Space n)) a := by
  have hOrigin (c : Space n) : (c,(0 : ℝ)) ∈ cylinder Set.univ 0 T :=
    ⟨Set.mem_univ _,le_rfl,hT⟩
  have hEquiv (c : Space n) := elliptic_matrix_space_equiv (a (c,0)) hEll.1 hEll.2.1
    (hEll.2.2 (c,0) (hOrigin c)).1 (hEll.2.2 (c,0) (hOrigin c)).2
  choose B hBN hBI hGram using hEquiv
  have hRefl : ‖(ContinuousLinearEquiv.refl ℝ (Space n) : Space n →L[ℝ] Space n)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  refine ⟨B,?_,?_,?_⟩
  · intro c
    exact constantHeatNormFactor_le hα (B c)
      ((hBN c).trans (le_max_left _ _)) ((hBI c).trans (le_max_left _ _))
  · exact constantHeatNormFactor_le hα (ContinuousLinearEquiv.refl ℝ (Space n))
      (hRefl.trans (le_max_right _ _)) (hRefl.trans (le_max_right _ _))
  · intro i hi H
    cases i with
    | none =>
      simp [localizationEquiv,localizationFrozenMatrix,Matrix.one_apply]
    | some c => exact hGram c H

theorem localizedHeatParametrix_inverse {n : ℕ} {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hGram : localizationGramIdentity s B Bext a)
    (hHalf : ∀ (f : Point n → ℝ) (F : ℝ), HolderBound α (cylinder Set.univ 0 T) f F →
      HolderBound α (cylinder Set.univ 0 T) (localizedHeatResidual T s r hr B Bext a b f) (F/2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Point n → ℝ) (F : ℝ),
      HolderBound α (cylinder Set.univ 0 T) f F → ∃ u : Point n → ℝ,
      SchauderBound α (cylinder Set.univ 0 T) u (C*F) ∧
      HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) (C*F) ∧
      (∀ x, u (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 T,
        linearOp (cylinder Set.univ 0 T) a b u p = f p := by
  let Q : Set (Point n) := cylinder Set.univ 0 T
  letI : NormedAddCommGroup (holderGraph α Q) := inferInstance
  letI : NormedSpace ℝ (holderGraph α Q) := inferInstance
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  have hφ : ∀ i ∈ localizationIndices s, ContDiff ℝ 2 (localizationOuter s hr i) :=
    fun i _ => localizationOuter_contDiff s hr i
  have hψ : ∀ i ∈ localizationIndices s,
      HolderBound α Q (fun p => localizationSource s hr i p.1) (P*r⁻¹*r^(1-α)) :=
    fun i _ => hSource s r hr hr1 hSep T i
  let D : holderGraph α Q → Point n → ℝ := fun x =>
    finiteHeatResidual T (localizationIndices s) (localizationEquiv B Bext)
      (localizationOuter s hr) (localizationSource s hr) a b (holderGraphFun x)
  have hResidualEq {f : Point n → ℝ} {F : ℝ} (hf : HolderBound α Q f F)
      {p : Point n} (hp : p ∈ Q) :
      finiteHeatResidual T (localizationIndices s) (localizationEquiv B Bext)
        (localizationOuter s hr) (localizationSource s hr) a b f p =
        localizedHeatResidual T s r hr B Bext a b f p := by
    unfold finiteHeatResidual
    change linearOp Q a b (localizedHeatParametrix s hr B Bext f) p-f p = _
    rw [localizedHeatParametrix_linearOp hα hα1 hT hT1 s hr hr1 hSep B Bext a b hGram hf hp]
    ring
  have hBound (x : holderGraph α Q) : HolderBound α Q (D x) ((1/2 : ℝ)*‖x‖) := by
    have h := holderBound_congr_on (hHalf (holderGraphFun x) ‖x‖ (holderGraphFun_holderBound x))
      (fun p hp => (hResidualEq (holderGraphFun_holderBound x) hp).symm)
    convert h using 1 <;> ring
  have hAdd (x y : holderGraph α Q) (p : Point n) (hp : p ∈ Q) :
      D (x+y) p = D x p+D y p := by
    dsimp only [D]
    rw [holderGraphFun_add]
    exact finiteHeatResidual_add _ _ _ _ a b hα hα1 hT hT1 hφ hψ
      (holderGraphFun_holderBound x) (holderGraphFun_holderBound y) hp
  have hSmul (c : ℝ) (x : holderGraph α Q) (p : Point n) (hp : p ∈ Q) :
      D (c • x) p = c*D x p := by
    dsimp only [D]
    rw [holderGraphFun_smul]
    exact finiteHeatResidual_smul _ _ _ _ a b hα hα1 hT hT1 hφ hψ
      (holderGraphFun_holderBound x) c hp
  let R : holderGraph α Q →L[ℝ] holderGraph α Q := holderGraphLift hα D hBound hAdd hSmul
  have hR : ‖R‖ ≤ (1/2 : ℝ) :=
    ContinuousLinearMap.opNorm_le_bound R (by norm_num)
      (fun x => holderGraphLift_norm_le hα D hBound hAdd hSmul x)
  obtain ⟨CP,hCP,hParametrix⟩ := localizedHeatParametrix_full_regularity hα hα1 s hr hr1 hSep B Bext
  refine ⟨2*CP,by positivity,?_⟩
  intro f F hf
  let fH : holderGraph α Q := holderGraphOfBound hα hf
  obtain ⟨g,hCorrect,hg⟩ := holderGraph_residual_correction R hR fH
  let u : Point n → ℝ := localizedHeatParametrix s hr B Bext (holderGraphFun g)
  have hBudget : CP*‖g‖ ≤ (2*CP)*F := by
    have hgf : ‖g‖ ≤ 2*F := hg.trans (mul_le_mul_of_nonneg_left (holderGraphOfBound_norm_le hα hf) (by norm_num))
    nlinarith
  have hU := hParametrix T ‖g‖ hT hT1 (holderGraphFun g) (holderGraphFun_holderBound g)
  refine ⟨u,schauderBound_mono_const hU.1 hBudget,
    holderBound_mono_const hU.2 hBudget,localizedHeatParametrix_initial s hr B Bext (holderGraphFun g),?_⟩
  intro p hp
  have hEval := congrArg (fun x : holderGraph α Q => x.val.1 ⟨p,hp⟩) hCorrect
  have hPoint : holderGraphFun g p+D g p = f p := by
    rw [holderGraphFun_apply g ⟨p,hp⟩]
    change g.val.1 ⟨p,hp⟩+(R g).val.1 ⟨p,hp⟩ = f p
    exact hEval
  change linearOp Q a b (localizedHeatParametrix s hr B Bext (holderGraphFun g)) p = f p
  rw [localizedHeatParametrix_linearOp hα hα1 hT hT1 s hr hr1 hSep B Bext a b hGram
    (holderGraphFun_holderBound g) hp]
  rw [← hResidualEq (holderGraphFun_holderBound g) hp]
  exact hPoint

/-- A single short time scale works for every coefficient family with
the fixed Hölder, Lipschitz, ellipticity and exterior bounds. -/
theorem exists_uniform_short_schauder_inverse {n : ℕ} {α M L lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hL : 0 ≤ L)
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      0 < T → T ≤ δ → HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      (∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T,
        ‖a p-a q‖ ≤ L*‖p-q‖) →
      Elliptic (cylinder Set.univ 0 T) a lam upper →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      ∃ C : ℝ, 0 < C ∧ ∀ (f : Point n → ℝ) (F : ℝ),
        HolderBound α (cylinder Set.univ 0 T) f F → ∃ u : Point n → ℝ,
        SchauderBound α (cylinder Set.univ 0 T) u (C*F) ∧
        HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) (C*F) ∧
        (∀ x, u (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 T,
          linearOp (cylinder Set.univ 0 T) a b u p = f p := by
  let N : ℝ := ellipticHeatNormBudget α lam upper
  obtain ⟨r,hr,s,hr1,hsK,hSep,hCover,δ,hδ,hδ1,hHalf⟩ :=
    exists_localizedHeatResidual_half_bound (n := n) (M := M) (N := N) hα hα1 hL hK
  refine ⟨δ,hδ,hδ1,?_⟩
  intro T a b hT hTδ ha hb hLip hEll hExterior
  obtain ⟨B,hBN,hNid,hGram⟩ := elliptic_localization_equivs hα.le hT.le a hEll s
  exact localizedHeatParametrix_inverse hα hα1 hT (hTδ.trans hδ1) s hr hr1 hSep
    B (ContinuousLinearEquiv.refl ℝ (Space n)) a b hGram
    (fun f F hf => hHalf T a b B (ContinuousLinearEquiv.refl ℝ (Space n)) f F hT hTδ
      ha hb hLip hExterior hBN hNid hf)

end Yau.LeafProofs.L16Aux
