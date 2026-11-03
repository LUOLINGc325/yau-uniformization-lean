import Yau.Proofs.F05HolderUniform
import Yau.Proofs.F05PhysicalOpenExponential
import Yau.Proofs.F05ExponentialC2
import Yau.Proofs.F05ExponentialRange
import Yau.Proofs.F05PostHolderCoefficients
import Yau.Proofs.F05PostHolderLogarithm

/-! On the actual original flow the classical value barriers discharge the
positive exponential range. One uniform value Holder budget then controls
w, exp(w), and the actual principal scalar exp(-w). Positive-time qualitative
regularity remains explicit until the separate bootstrap is proved. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {X : KahlerManifold n}

theorem F05_flow_value_holder_uniform (hn : 0 < n)
    {O : Set (Pt X)} {A : AtlasData X.manifold} (hA : GenuineAtlas O A)
    {χ : Fin A.count → Pt X → ℝ} (hχ : F05Partition O A χ)
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (p : STF X) {S a : ℝ} (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S)) :
    ∃ γ M : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < M ∧ ∀ (T : ℝ), 0 < T → T ≤ S →
      ∀ w : STF X,
      (∀ i, C2 (F05Q A i T) (pull A i w)) →
      (∀ i, ContDiffOn ℝ ∞ (pull A i w)
        ((F05ModelOpen A i ∩ Metric.ball 0 3) ×ˢ Ioc 0 T)) →
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 T, 0 ≤ w x t ∧ w x t ≤ ρ x t+2*a) →
      (∀ x ∈ closure O, w x 0 = p x 0) →
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = p x t) →
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
        derivWithin (w x) (Icc 0 T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
          (1-Real.exp (-w x t))*scalarCurvature (h t) x) →
      ∀ i,
        HolderBound γ (F05Q A i T) (pull A i (fun x t => Real.exp (w x t))) M ∧
        HolderBound γ (F05Q A i T) (pull A i w) M ∧
        HolderBound γ (F05Q A i T) (pull A i (fun x t => Real.exp (-w x t))) M := by
  have hh : MetricFamilySmooth h (Icc 0 S) := fun x j k =>
    (hloc.1.2.1 x j k).mono (fun q hq => ⟨hq.1,hq.2.1⟩)
  have hpExp : SmoothSpaceTime (fun x t => Real.exp (p x t)) (Icc 0 S) :=
    fun x => (hp x).exp
  obtain ⟨B,hB,hRange⟩ := F05_exp_barrier_uniform hA o h U P ρ hloc S a
  obtain ⟨γ,C,hγ,hγ1,hC,hHolder⟩ := F05_exp_boundary_holder_uniform hn hA hχ h
    (fun x t => scalarCurvature (h t) x) (fun x t => Real.exp (p x t))
    hS zero_lt_one hB hh (F05_flow_scalar_smooth o h U P ρ hloc hS) hpExp
  let M := 1+C+(4+16*C)
  have hM : 0 < M := by dsimp [M]; positivity
  have hCM : C ≤ M := by dsimp [M]; linarith
  have hInvM : 4+16*C ≤ M := by dsimp [M]; linarith
  refine ⟨γ,M,hγ,hγ1,hM,?_⟩
  intro T hT hTS w hW hSmooth hBarrier hi hl hEquation i
  have hhT : MetricFamilySmooth h (Icc 0 T) := fun x j k =>
    (hh x j k).mono (fun z hz => ⟨hz.1,hz.2.1,hz.2.2.trans hTS⟩)
  have hQHolder := hHolder T hT hTS (fun x t => Real.exp (w x t))
    (fun j => F05_c2_exp hT (hW j)) (fun j => (hSmooth j).exp)
    (hRange T hTS w hBarrier)
    (fun x hx => congrArg Real.exp (hi x hx))
    (fun x hx t htm => congrArg Real.exp (hl x hx t htm))
    (fun j => F05_physical_exp_equation_open hA h
      (fun x t => scalarCurvature (h t) x) w hT hhT hSmooth hEquation j)
  have hNonneg : ∀ z ∈ F05Q A i T, 0 ≤ pull A i w z := fun z hz =>
    (hBarrier (lift A i z.1) (F05D_lift_mem_closure hA hz.1) z.2 hz.2).1
  exact ⟨holderBound_mono_const (hQHolder i) hCM,
    holderBound_mono_const (F05_nonnegative_log_value_holder (hQHolder i) hNonneg) hCM,
    holderBound_mono_const (F05_nonnegative_exp_inverse_holder (hQHolder i) hNonneg) hInvM⟩

end Yau.Proofs.F05Aux
