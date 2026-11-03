import Yau.Proofs.V02FlowUniformLimit
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Sequences

/-! The closed Banach subspace used for joint holomorphic Picard iteration. -/

open scoped Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof

variable {P F V : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def compactExtension {K : Set P} (u : C(K, F)) (p : P) : F := by
  classical
  exact if hp : p ∈ K then u ⟨p, hp⟩ else 0

omit [NormedSpace ℂ P] [NormedSpace ℂ F] [CompleteSpace F] in
@[simp] theorem compactExtension_of_mem {K : Set P} (u : C(K, F))
    {p : P} (hp : p ∈ K) : compactExtension u p = u ⟨p, hp⟩ := by
  classical
  simp only [compactExtension, dite_eq_left hp]

theorem isClosed_holomorphic_extensions {O K : Set P} [CompactSpace K]
    (hO : IsOpen O) (hOK : O ⊆ K) :
    IsClosed {u : C(K, F) | DifferentiableOn ℂ (compactExtension u) O} := by
  apply IsSeqClosed.isClosed
  intro useq u hu hlim
  apply differentiableOn_of_uniform_holomorphic_limit hO hOK hu
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hlim ε hε] with m hm p hp
  simp only [compactExtension_of_mem _ hp]
  calc
    dist (u ⟨p, hp⟩) (useq m ⟨p, hp⟩) ≤ dist u (useq m) := by
      simpa only [dist_eq_norm, ContinuousMap.sub_apply] using
        (u - useq m).norm_coe_le_norm ⟨p, hp⟩
    _ < ε := by simpa only [dist_comm] using hm

variable [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

def picardClosedDomain (a : V) (d R : ℝ) : Set (ℂ × V) :=
  closedBall 0 R ×ˢ closedBall a d

def picardOpenDomain (a : V) (d R : ℝ) : Set (ℂ × V) :=
  ball 0 R ×ˢ ball a d

instance picardDomainCompactSpace (a : V) (d R : ℝ) :
    CompactSpace (picardClosedDomain a d R) := by
  let := FiniteDimensional.proper ℂ V
  exact isCompact_iff_compactSpace.mp ((isCompact_closedBall (0 : ℂ) R).prod
    (isCompact_closedBall a d))

theorem picardOpenDomain_isOpen (a : V) (d R : ℝ) :
    IsOpen (picardOpenDomain a d R) := isOpen_ball.prod isOpen_ball

theorem picardOpenDomain_subset_closedDomain (a : V) (d R : ℝ) :
    picardOpenDomain a d R ⊆ picardClosedDomain a d R :=
  Set.prod_mono ball_subset_closedBall ball_subset_closedBall

def picardProjection (a : V) (d R : ℝ) : C(picardClosedDomain a d R, V) :=
  ⟨fun p => p.1.2, continuous_snd.comp continuous_subtype_val⟩

def picardHolomorphicBall (a : V) (d R : ℝ) :
    Set C(picardClosedDomain a d R, V) :=
  {u | DifferentiableOn ℂ (compactExtension u) (picardOpenDomain a d R)} ∩
    closedBall (picardProjection a d R) d

theorem picardHolomorphicBall_isClosed (a : V) (d R : ℝ) [CompleteSpace V] :
    IsClosed (picardHolomorphicBall a d R) :=
  (isClosed_holomorphic_extensions (picardOpenDomain_isOpen a d R)
    (picardOpenDomain_subset_closedDomain a d R)).inter isClosed_closedBall

theorem picardProjection_mem_holomorphicBall (a : V) {d R : ℝ} (hd : 0 ≤ d) :
    picardProjection a d R ∈ picardHolomorphicBall a d R := by
  refine ⟨?_, by simpa using hd⟩
  intro p hp
  have heq : compactExtension (picardProjection a d R) =ᶠ[𝓝 p] Prod.snd := by
    filter_upwards [(picardOpenDomain_isOpen a d R).mem_nhds hp] with q hq
    rw [compactExtension_of_mem _ (picardOpenDomain_subset_closedDomain a d R hq)]
    rfl
  exact (differentiableAt_snd.congr_of_eventuallyEq heq).differentiableWithinAt

theorem picardHolomorphicBall_image (a : V) {d R : ℝ}
    {u : C(picardClosedDomain a d R, V)} (hu : u ∈ picardHolomorphicBall a d R)
    (p : picardClosedDomain a d R) : u p ∈ closedBall a (2 * d) := by
  have hdist : dist (u p) p.1.2 ≤ d := by
    calc
      dist (u p) p.1.2 ≤ dist u (picardProjection a d R) := by
        simpa only [dist_eq_norm, ContinuousMap.sub_apply, picardProjection,
          ContinuousMap.coe_mk] using (u - picardProjection a d R).norm_coe_le_norm p
      _ ≤ d := hu.2
  exact mem_closedBall.mpr ((dist_triangle (u p) p.1.2 a).trans
    (by have hp := mem_closedBall.mp p.2.2; linarith))

end Yau.Blueprint.V02FlowProof
