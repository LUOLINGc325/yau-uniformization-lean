import Yau.LeafProofs.L16HalfSpaceControlled
import Yau.LeafProofs.L16ParametrixRegularity

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

local instance halfSpaceFinite_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceFinite_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceFinite_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceFinite_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The actual finite cutoff sum of the normalized half-space heat kernels. -/
def halfSpaceFiniteParametrix {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (e : Space n) (T : ℝ)
    (φ ψ : ι → Space n → ℝ) (f : Point n → ℝ) : Point n → ℝ :=
  finiteParametrix s φ (fun i => halfSpaceConstantPullbackDuhamel (B i) e T (fun p => ψ i p.1*f p))

/-- The residual is the literal variable-coefficient operator minus the source
on the original closed half-space cylinder. -/
def halfSpaceFiniteResidual {n : ℕ} {ι : Type*} (T : ℝ) (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (e : Space n) (φ ψ : ι → Space n → ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ) : Point n → ℝ :=
  fun p => linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b
    (halfSpaceFiniteParametrix s B e T φ ψ f) p-f p

/-- Each backend has actual ambient regularity, both zero faces and the exact
closed-half-space equation, under only first corner compatibility. -/
theorem halfSpaceFiniteParametrix_kernel_data {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (A : ι → Mat n) {e : Space n} (he : ‖e‖ = 1)
    (ψ : ι → Space n → ℝ) {α T P F : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hψ : ∀ i ∈ s, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hCorner : ∀ x, inner ℝ e x = 0 → f (x,0) = 0)
    (hB : ∀ i ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B i (Yau.realVec k)) (B i (Yau.realVec k))) =
        ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n, A i j k*H (Yau.realVec j) (Yau.realVec k)) :
    ∀ i ∈ s,
      let v := halfSpaceConstantPullbackDuhamel (B i) e T (fun p => ψ i p.1*f p)
      C2 (cylinder univ 0 T) v ∧ (∀ x, v (x,0) = 0) ∧
      (∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, v (x,t) = 0) ∧
      ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
        linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun _ => A i) (fun _ _ => 0) v p = ψ i p.1*f p := by
  obtain ⟨C,hC,hSolve⟩ := halfSpace_constantPullback_schauder_solution (n := n) hα hα1
  intro i hi
  have hSource := holderBound_mul (hψ i hi) hf
  have hSourceCorner : ∀ x, inner ℝ e x = 0 → ψ i x*f (x,0) = 0 := by
    intro x hx
    rw [hCorner x hx,mul_zero]
  obtain ⟨hV,hV0,hVB,hPDE⟩ := hSolve (B i) (A i) (hB i hi) e he T (2*P*F) hT hT1 _ hSource hSourceCorner
  exact ⟨hV.1,hV0,hVB,hPDE⟩

/-- Ambient regularity and the two actual homogeneous data faces for the
finite sum. No all-initial source vanishing premise is imposed. -/
theorem halfSpaceFiniteParametrix_data {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (A : ι → Mat n) {e : Space n} (he : ‖e‖ = 1)
    (φ ψ : ι → Space n → ℝ) {α T P F : ℝ} {f : Point n → ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hCorner : ∀ x, inner ℝ e x = 0 → f (x,0) = 0)
    (hB : ∀ i ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B i (Yau.realVec k)) (B i (Yau.realVec k))) =
        ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n, A i j k*H (Yau.realVec j) (Yau.realVec k)) :
    C2 (cylinder univ 0 T) (halfSpaceFiniteParametrix s B e T φ ψ f) ∧
    (∀ x, halfSpaceFiniteParametrix s B e T φ ψ f (x,0) = 0) ∧
    (∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, halfSpaceFiniteParametrix s B e T φ ψ f (x,t) = 0) := by
  classical
  have hK := halfSpaceFiniteParametrix_kernel_data s B A he ψ hα hα1 hT hT1 hψ hf hCorner hB
  refine ⟨finiteParametrix_C2 s hφ (fun i hi => (hK i hi).1),?_,?_⟩
  · intro x
    apply Finset.sum_eq_zero
    intro i hi
    dsimp only
    rw [(hK i hi).2.1 x,mul_zero]
  · intro x hx t ht
    apply Finset.sum_eq_zero
    intro i hi
    dsimp only
    rw [(hK i hi).2.2.1 x hx t ht,mul_zero]

/-- Scalar multiplication is an actual global identity for the finite backend. -/
theorem halfSpaceFiniteParametrix_smul {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (e : Space n) (T c : ℝ) (φ ψ : ι → Space n → ℝ)
    (f : Point n → ℝ) (p : Point n) :
    halfSpaceFiniteParametrix s B e T φ ψ (c • f) p = c*halfSpaceFiniteParametrix s B e T φ ψ f p := by
  classical
  have hSource (i : ι) : (fun q : Point n => ψ i q.1*(c • f) q) = c • (fun q => ψ i q.1*f q) := by
    funext q
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  unfold halfSpaceFiniteParametrix finiteParametrix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [hSource i,halfSpaceConstantPullbackDuhamel_smul]
  ring

/-- Addition holds on the whole ambient closed slab, using source Holder data
only on the true half-space. -/
theorem halfSpaceFiniteParametrix_add {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) {e : Space n} (he : ‖e‖ = 1) (φ ψ : ι → Space n → ℝ)
    {α T P F G : ℝ} {f g : Point n → ℝ} (hα : 0 < α) (hT : 0 ≤ T)
    (hψ : ∀ i ∈ s, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hg : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) g G)
    {p : Point n} (hpT : p.2 ∈ Icc 0 T) :
    halfSpaceFiniteParametrix s B e T φ ψ (f+g) p =
      halfSpaceFiniteParametrix s B e T φ ψ f p+halfSpaceFiniteParametrix s B e T φ ψ g p := by
  classical
  have hSource (i : ι) : (fun q : Point n => ψ i q.1*(f+g) q) =
      (fun q => ψ i q.1*f q)+(fun q => ψ i q.1*g q) := by
    funext q
    simp only [Pi.add_apply]
    ring
  have hAdd (i : ι) (hi : i ∈ s) :
      halfSpaceConstantPullbackDuhamel (B i) e T (fun q => ψ i q.1*(f+g) q) p =
      halfSpaceConstantPullbackDuhamel (B i) e T (fun q => ψ i q.1*f q) p+
      halfSpaceConstantPullbackDuhamel (B i) e T (fun q => ψ i q.1*g q) p := by
    rw [hSource i]
    exact halfSpaceConstantPullbackDuhamel_add hα hT (B i) he
      (holderBound_mul (hψ i hi) hf) (holderBound_mul (hψ i hi) hg) hpT
  unfold halfSpaceFiniteParametrix finiteParametrix
  calc
    _ = ∑ i ∈ s, (φ i p.1*halfSpaceConstantPullbackDuhamel (B i) e T (fun q => ψ i q.1*f q) p+
        φ i p.1*halfSpaceConstantPullbackDuhamel (B i) e T (fun q => ψ i q.1*g q) p) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only
      rw [hAdd i hi]
      ring
    _ = _ := Finset.sum_add_distrib


/-- Uniform full ambient regularity for the actual finite backend. The
constant is chosen before the frozen matrices, unit normal, time and forcing;
source cutoffs are controlled only on the corresponding true half-space. -/
theorem halfSpaceFiniteParametrix_uniform_full_regularity {n : ℕ} {ι : Type*} {α N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hN : 0 ≤ N) (s : Finset ι)
    (φ ψ : ι → Space n → ℝ) {E P : ℝ} (hE : 0 < E) (hP : 0 < P)
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hφ0 : ∀ i ∈ s, HolderBound α (cylinder univ 0 1) (fun p => φ i p.1) E)
    (hφ1 : ∀ i ∈ s, HolderBound α (cylinder univ 0 1) (fun p => fderiv ℝ (φ i) p.1) E)
    (hφ2 : ∀ i ∈ s, HolderBound α (cylinder univ 0 1) (fun p => fderiv ℝ (fderiv ℝ (φ i)) p.1) E) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ι → Space n ≃L[ℝ] Space n,
      (∀ i ∈ s, constantHeatNormFactor α (B i) ≤ N) → ∀ A : ι → Mat n,
      (∀ i ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (B i (Yau.realVec k)) (B i (Yau.realVec k))) =
          ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n, A i j k*H (Yau.realVec j) (Yau.realVec k)) →
      ∀ e : Space n, ‖e‖ = 1 →
      (∀ i ∈ s, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 1) (fun p => ψ i p.1) P) →
      ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) →
      SchauderBound α (cylinder univ 0 T) (halfSpaceFiniteParametrix s B e T φ ψ f) (C*F) ∧
      HolderBound α (cylinder univ 0 T)
        (fun p => (halfSpaceFiniteParametrix s B e T φ ψ f p,
          spatialD (halfSpaceFiniteParametrix s B e T φ ψ f) p)) (C*F) := by
  classical
  obtain ⟨CH,hCH,hHeat⟩ := halfSpaceConstantPullbackDuhamel_controlled_bounds (n := n) hα hα1
  let L : ℝ := 2*CH*(2*P)*N
  let W : ℝ := 8*E*L
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hSumW : 0 ≤ ∑ _i ∈ s, W := Finset.sum_nonneg (fun i _ => hW)
  refine ⟨1+∑ _i ∈ s, W,by linarith only [hSumW],?_⟩
  intro B hBN A hB e he hψ T F hT hT1 f hf hCorner
  let Q := cylinder (n := n) univ 0 T
  let v : ι → Point n → ℝ := fun i => halfSpaceConstantPullbackDuhamel (B i) e T (fun p => ψ i p.1*f p)
  have hSub : Q ⊆ cylinder univ 0 1 := cylinder_mono_time hT1
  have hSubH : cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T ⊆ cylinder {x | 0 ≤ inner ℝ e x} 0 1 := cylinder_mono_time hT1
  have hv (i : ι) (hi : i ∈ s) : C2 Q (v i) ∧
      HolderBound α Q (v i) (L*F) ∧ HolderBound α Q (spatialD (v i)) (L*F) ∧
      HolderBound α Q (spatialDD (v i)) (L*F) ∧ HolderBound α Q (timeD Q (v i)) (L*F) := by
    have hSource := holderBound_mul (holderBound_mono (hψ i hi) hSubH) hf
    have hSourceCorner : ∀ x, inner ℝ e x = 0 → ψ i x*f (x,0) = 0 := by
      intro x hx
      rw [hCorner x hx,mul_zero]
    have hHeatI := hHeat N (B i) (hBN i hi) (A i) (hB i hi) e he T (2*P*F) hT hT1 _ hSource hSourceCorner
    have hB0 : 0 ≤ CH*(2*P*F)*N := hHeatI.1.2.1
    have hMain : CH*(2*P*F)*N ≤ L*F := by dsimp only [L]; nlinarith only [hB0]
    have hPow1 : T^(1/2:ℝ) ≤ 1 := Real.rpow_le_one hT.le hT1 (by norm_num)
    have hPow2 : T^((1-α)/2) ≤ 1 := Real.rpow_le_one hT.le hT1 (by linarith only [hα1])
    have hLowBound : CH*(2*P*F)*N*(T^(1/2:ℝ)+T^((1-α)/2)) ≤ L*F := by
      calc
        _ ≤ CH*(2*P*F)*N*2 := mul_le_mul_of_nonneg_left (by linarith only [hPow1,hPow2]) hB0
        _ = _ := by dsimp only [L]; ring
    have hLow := holderBound_mono_const hHeatI.2.2 hLowBound
    exact ⟨hHeatI.1.1,holderBound_fst hLow,holderBound_snd hLow,
      holderBound_mono_const hHeatI.1.2.2.2.1 hMain,holderBound_mono_const hHeatI.1.2.2.2.2 hMain⟩
  have hPatch (i : ι) (hi : i ∈ s) : C2 Q (fun p => φ i p.1*v i p) ∧
      HolderBound α Q (fun p => φ i p.1*v i p) (W*F) ∧
      HolderBound α Q (spatialD (fun p => φ i p.1*v i p)) (W*F) ∧
      HolderBound α Q (spatialDD (fun p => φ i p.1*v i p)) (W*F) ∧
      HolderBound α Q (timeD Q (fun p => φ i p.1*v i p)) (W*F) := by
    have hV := hv i hi
    have hh := cutoff_full_jet_holderBound (hφ i hi) hV.1
      (holderBound_mono (hφ0 i hi) hSub) (holderBound_mono (hφ1 i hi) hSub)
      (holderBound_mono (hφ2 i hi) hSub) hV.2.1 hV.2.2.1 hV.2.2.2.1 hV.2.2.2.2
    simpa only [W,mul_assoc] using hh
  have hSum := full_jet_finset_sum s hPatch
  have hBudget : (∑ _i ∈ s, W*F) ≤ (1+∑ _i ∈ s, W)*F := by
    rw [←Finset.sum_mul]
    nlinarith only [hf.1]
  have h0 := holderBound_mono_const hSum.2.1 hBudget
  have h1 := holderBound_mono_const hSum.2.2.1 hBudget
  have h2 := holderBound_mono_const hSum.2.2.2.1 hBudget
  have ht := holderBound_mono_const hSum.2.2.2.2 hBudget
  change SchauderBound α Q (fun p => ∑ i ∈ s, φ i p.1*v i p) _ ∧ _
  refine ⟨⟨hSum.1,h0.1,?_,h2,ht⟩,?_⟩
  · intro p hp
    exact ⟨by simpa only [Real.norm_eq_abs] using h0.2.1 p hp,h1.2.1 p hp⟩
  · exact ⟨h0.1,fun p hp => max_le (h0.2.1 p hp) (h1.2.1 p hp),
      fun p hp q hq => max_le (h0.2.2 p hp q hq) (h1.2.2 p hp q hq)⟩


/-- Literal frozen-residual identity for the actual finite kernels. The
partition factor is retained, so no covering identity is presumed. -/
theorem halfSpaceFiniteParametrix_linearOp {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (A : ι → Mat n) {e : Space n} (he : ‖e‖ = 1)
    (φ ψ : ι → Space n → ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {α T P F : ℝ} {f : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hCorner : ∀ x, inner ℝ e x = 0 → f (x,0) = 0)
    (hB : ∀ i ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B i (Yau.realVec k)) (B i (Yau.realVec k))) =
        ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n, A i j k*H (Yau.realVec j) (Yau.realVec k))
    {p : Point n} (hp : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T) :
    linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b (halfSpaceFiniteParametrix s B e T φ ψ f) p =
      (∑ i ∈ s, φ i p.1*ψ i p.1)*f p+
      ∑ i ∈ s, frozenPatchResidual (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b (A i) (φ i)
        (halfSpaceConstantPullbackDuhamel (B i) e T (fun q => ψ i q.1*f q)) p := by
  classical
  let Q := cylinder {x : Space n | 0 ≤ inner ℝ e x} 0 T
  let v := fun i => halfSpaceConstantPullbackDuhamel (B i) e T (fun q => ψ i q.1*f q)
  have hK := halfSpaceFiniteParametrix_kernel_data s B A he ψ hα hα1 hT hT1 hψ hf hCorner hB
  have hv (i : ι) (hi : i ∈ s) : C2 Q (v i) := c2_cylinder_restrict_space (hK i hi).1
  change linearOp Q a b (fun q => ∑ i ∈ s, φ i q.1*v i q) p =
    (∑ i ∈ s, φ i p.1*ψ i p.1)*f p+∑ i ∈ s, frozenPatchResidual Q a b (A i) (φ i) (v i) p
  rw [linearOp_sum s (fun i hi => c2_spatial_mul (hφ i hi) (hv i hi)) hp]
  calc
    _ = ∑ i ∈ s, (φ i p.1*(ψ i p.1*f p)+frozenPatchResidual Q a b (A i) (φ i) (v i) p) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [linearOp_frozen_patch (hφ i hi).contDiffAt ((hv i hi).2.2.2.2.1 p hp),(hK i hi).2.2.2 p hp]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [←mul_assoc,←Finset.sum_mul]

/-- Exact residual expression, including the uncovered source contribution. -/
theorem halfSpaceFiniteResidual_eq {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (A : ι → Mat n) {e : Space n} (he : ‖e‖ = 1)
    (φ ψ : ι → Space n → ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {α T P F : ℝ} {f : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hCorner : ∀ x, inner ℝ e x = 0 → f (x,0) = 0)
    (hB : ∀ i ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B i (Yau.realVec k)) (B i (Yau.realVec k))) =
        ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n, A i j k*H (Yau.realVec j) (Yau.realVec k))
    {p : Point n} (hp : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T) :
    halfSpaceFiniteResidual T s B e φ ψ a b f p = ((∑ i ∈ s, φ i p.1*ψ i p.1)-1)*f p+
      ∑ i ∈ s, frozenPatchResidual (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b (A i) (φ i)
        (halfSpaceConstantPullbackDuhamel (B i) e T (fun q => ψ i q.1*f q)) p := by
  unfold halfSpaceFiniteResidual
  rw [halfSpaceFiniteParametrix_linearOp s B A he φ ψ a b hα hα1 hT hT1 hφ hψ hf hCorner hB hp]
  ring

/-- A genuine zero initial trace forces all spatial terms of the actual frozen
residual to vanish, without a claim about the forcing away from the face. -/
theorem halfSpaceFinite_frozen_initial_zero {n : ℕ} {u : Point n → ℝ}
    (hInitial : ∀ x, u (x,0) = 0) (Q : Set (Point n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (A : Mat n) (φ : Space n → ℝ) (x : Space n) :
    frozenPatchResidual Q a b A φ u (x,0) = 0 := by
  simp only [frozenPatchResidual,hInitial x,spatialD_initial_zero hInitial x,spatialDD_initial_zero hInitial x,
    zero_apply,zero_mul,mul_zero,add_zero,Finset.sum_const_zero,sub_zero]

/-- The actual operator residual preserves precisely the first lateral/initial
corner compatibility. This follows from the proved PDE identity and true
initial spatial jets, for arbitrary variable coefficients a,b. -/
theorem halfSpaceFiniteResidual_corner {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (A : ι → Mat n) {e : Space n} (he : ‖e‖ = 1)
    (φ ψ : ι → Space n → ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {α T P F : ℝ} {f : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hCorner : ∀ x, inner ℝ e x = 0 → f (x,0) = 0)
    (hB : ∀ i ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B i (Yau.realVec k)) (B i (Yau.realVec k))) =
        ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n, A i j k*H (Yau.realVec j) (Yau.realVec k)) :
    ∀ x, inner ℝ e x = 0 → halfSpaceFiniteResidual T s B e φ ψ a b f (x,0) = 0 := by
  classical
  have hK := halfSpaceFiniteParametrix_kernel_data s B A he ψ hα hα1 hT hT1 hψ hf hCorner hB
  intro x hx
  have hp : (x,0) ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T :=
    ⟨by change 0 ≤ inner ℝ e x; rw [hx],le_rfl,hT.le⟩
  rw [halfSpaceFiniteResidual_eq s B A he φ ψ a b hα hα1 hT hT1 hφ hψ hf hCorner hB hp,hCorner x hx,mul_zero,zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  exact halfSpaceFinite_frozen_initial_zero (hK i hi).2.1 _ a b (A i) (φ i) x


/-- Residual addition follows from actual backend addition on whole spatial
slices and genuine within-time derivative congruence on the closed slab. -/
theorem halfSpaceFiniteResidual_add {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (A : ι → Mat n) {e : Space n} (he : ‖e‖ = 1)
    (φ ψ : ι → Space n → ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {α T P F G : ℝ} {f g : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hg : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) g G)
    (hCornerf : ∀ x, inner ℝ e x = 0 → f (x,0) = 0)
    (hCornerg : ∀ x, inner ℝ e x = 0 → g (x,0) = 0)
    (hB : ∀ i ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B i (Yau.realVec k)) (B i (Yau.realVec k))) =
        ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n, A i j k*H (Yau.realVec j) (Yau.realVec k))
    {p : Point n} (hp : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T) :
    halfSpaceFiniteResidual T s B e φ ψ a b (f+g) p =
      halfSpaceFiniteResidual T s B e φ ψ a b f p+halfSpaceFiniteResidual T s B e φ ψ a b g p := by
  have hKf := (halfSpaceFiniteParametrix_data s B A he φ ψ hα hα1 hT hT1 hφ hψ hf hCornerf hB).1
  have hKg := (halfSpaceFiniteParametrix_data s B A he φ ψ hα hα1 hT hT1 hφ hψ hg hCornerg hB).1
  have hAdd : EqOn (halfSpaceFiniteParametrix s B e T φ ψ (f+g))
      (fun q => halfSpaceFiniteParametrix s B e T φ ψ f q+halfSpaceFiniteParametrix s B e T φ ψ g q)
      (cylinder univ 0 T) := by
    intro q hq
    exact halfSpaceFiniteParametrix_add s B he φ ψ hα hT.le hψ hf hg hq.2
  have hpAmbient : p ∈ cylinder univ 0 T := ⟨mem_univ _,hp.2⟩
  unfold halfSpaceFiniteResidual
  simp only [linearOp_cylinder_restrict_space a b _ hp]
  rw [linearOp_congr_cylinder_univ hAdd a b hpAmbient,
    linearOp_add (a := a) (b := b) hKf hKg hpAmbient]
  simp only [Pi.add_apply]
  ring

/-- Scalar residual linearity is derived from the actual global scalar kernel
identity, with no additional source compatibility premise for the scalar. -/
theorem halfSpaceFiniteResidual_smul {n : ℕ} {ι : Type*} (s : Finset ι)
    (B : ι → Space n ≃L[ℝ] Space n) (A : ι → Mat n) {e : Space n} (he : ‖e‖ = 1)
    (φ ψ : ι → Space n → ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {α T P F : ℝ} {f : Point n → ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hψ : ∀ i ∈ s, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun p => ψ i p.1) P)
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hCorner : ∀ x, inner ℝ e x = 0 → f (x,0) = 0)
    (hB : ∀ i ∈ s, ∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
      (∑ k : Yau.RIdx n, H (B i (Yau.realVec k)) (B i (Yau.realVec k))) =
        ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n, A i j k*H (Yau.realVec j) (Yau.realVec k))
    (c : ℝ) {p : Point n} (hp : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T) :
    halfSpaceFiniteResidual T s B e φ ψ a b (c • f) p = c*halfSpaceFiniteResidual T s B e φ ψ a b f p := by
  have hKf := (halfSpaceFiniteParametrix_data s B A he φ ψ hα hα1 hT hT1 hφ hψ hf hCorner hB).1
  have hScale : halfSpaceFiniteParametrix s B e T φ ψ (c • f) = c • halfSpaceFiniteParametrix s B e T φ ψ f := by
    funext q
    exact halfSpaceFiniteParametrix_smul s B e T c φ ψ f q
  unfold halfSpaceFiniteResidual
  rw [hScale,linearOp_const_smul (a := a) (b := b) (c2_cylinder_restrict_space hKf) c hp]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

end Yau.LeafProofs.L16Aux
