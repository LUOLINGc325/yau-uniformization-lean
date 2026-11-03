import Yau.Proofs.F01AQuantitativeJetRecursion
import Yau.Proofs.F01FiniteTaylorComposition

/-! Continuous linear currying identifies actual spatial Fréchet tensors
with the nested spatial state used by the quantitative clock recursion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Yau.NodeProofs.F01Aux
open Yau.LeafProofs.L17BootstrapClosedSlabAux
open Yau.LeafProofs.L17BootstrapEvolutionJetsAux
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spatialTensorToNestedJet : (k : ℕ) →
    (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) →L[ℝ] Jet E ℝ k
  | 0 => (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  | k + 1 =>
      ((ContinuousLinearMap.compL ℝ E
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (Jet E ℝ k))
          (spatialTensorToNestedJet k)).comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

/-- This tower is computed from the actual spatial Fréchet derivatives. -/
def nativeSpatialJet (f : E × ℝ → ℝ) (k : ℕ) (p : E × ℝ) : Jet E ℝ k :=
  spatialTensorToNestedJet k (iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1)

@[simp] theorem nativeSpatialJet_zero (f : E × ℝ → ℝ) (p : E × ℝ) :
    nativeSpatialJet f 0 p = f p := by
  change (continuousMultilinearCurryFin0 ℝ E ℝ)
    (iteratedFDeriv ℝ 0 (fun z => f (z, p.2)) p.1) = _
  rw [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]

theorem nativeSpatialJet_hasFDerivAt (f : E × ℝ → ℝ) (k : ℕ) (p : E × ℝ)
    (hf : ContDiffAt ℝ ∞ (fun z => f (z, p.2)) p.1) :
    HasFDerivAt (fun z => nativeSpatialJet f k (z, p.2)) (nativeSpatialJet f (k + 1) p) p.1 := by
  have hDiff := (hf.differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).hasFDerivAt
  rw [fderiv_iteratedFDeriv] at hDiff
  convert! (spatialTensorToNestedJet (E := E) k).hasFDerivAt.comp p.1 hDiff using 1

theorem nativeSpatialJet_contDiffOn {f : E × ℝ → ℝ} {W : Set (E × ℝ)} (k : ℕ)
    (hf : ContDiffOn ℝ ∞
      (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) W) :
    ContDiffOn ℝ ∞ (nativeSpatialJet f k) W :=
  (spatialTensorToNestedJet (E := E) k).contDiff.comp_contDiffOn hf

theorem nativeSpatialJet_two (f : E × ℝ → ℝ) (p : E × ℝ) :
    nativeSpatialJet f 2 p = fderiv ℝ (fderiv ℝ (fun z => f (z, p.2))) p.1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  dsimp [nativeSpatialJet, spatialTensorToNestedJet, ContinuousLinearMap.compL,
    ContinuousLinearMap.compSL]
  change iteratedFDeriv ℝ 2 (fun z => f (z, p.2)) p.1 (Fin.cons v (Fin.cons w 0)) = _
  rw [iteratedFDeriv_two_apply]
  rfl

theorem nativeSpatialJet_hasDerivWithinAt_of_tensor_clock
    (f P : E × ℝ → ℝ) (k : ℕ) {I : Set ℝ} (p : E × ℝ)
    (hClock : HasDerivWithinAt
      (fun t => iteratedFDeriv ℝ k (fun z => f (z, t)) p.1)
      (iteratedFDeriv ℝ k (fun z => P (z, p.2)) p.1) I p.2) :
    HasDerivWithinAt (fun t => nativeSpatialJet f k (p.1, t))
      (nativeSpatialJet P k p) I p.2 :=
  (spatialTensorToNestedJet k).hasFDerivAt.comp_hasDerivWithinAt p.2 hClock

/-- A genuine compact range of actual multilinear spatial jets transports
continuously to the nested finite state. -/
def nativeFiniteSpatialStateCLM (k : ℕ) :
    ((E × ℝ) × FiniteTaylorJet E ℝ (k + 2)) →L[ℝ] State E k :=
  (ContinuousLinearMap.id ℝ (E × ℝ)).prodMap
    (ContinuousLinearMap.pi (fun j =>
      (spatialTensorToNestedJet j.val).comp (ContinuousLinearMap.proj j)))

@[simp] theorem nativeFiniteSpatialStateCLM_actual
    (f : E × ℝ → ℝ) (k : ℕ) (p : E × ℝ) :
    nativeFiniteSpatialStateCLM k
      (p, fun j => iteratedFDeriv ℝ j.val (fun z => f (z, p.2)) p.1) =
      stateJ (nativeSpatialJet f) k p := rfl

end Yau.NodeProofs.F01Aux
