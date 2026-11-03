import Yau.LeafProofs.L17SchauderSpaceLocal
import Yau.LeafProofs.L17SchauderSpaceIntegral
import Yau.LeafProofs.L17SchauderSpaceFTC
import Mathlib.Topology.Order.ProjIcc

open Set Metric MeasureTheory
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

abbrev D1 (n : ℕ) := ComplexVector n →L[ℝ] ℝ
abbrev D2 (n : ℕ) := ComplexVector n →L[ℝ] D1 n

instance schauderSpaceD1_normedAddCommGroup (n : ℕ) : NormedAddCommGroup (D1 n) :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n →L[ℝ] ℝ))
instance schauderSpaceD1_normedSpace (n : ℕ) : NormedSpace ℝ (D1 n) :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n →L[ℝ] ℝ))
instance schauderSpaceD1_completeSpace (n : ℕ) : CompleteSpace (D1 n) :=
  inferInstanceAs (CompleteSpace (ComplexVector n →L[ℝ] ℝ))
instance schauderSpaceD2_normedAddCommGroup (n : ℕ) : NormedAddCommGroup (D2 n) :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n →L[ℝ] (ComplexVector n →L[ℝ] ℝ)))
instance schauderSpaceD2_normedSpace (n : ℕ) : NormedSpace ℝ (D2 n) :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n →L[ℝ] (ComplexVector n →L[ℝ] ℝ)))
instance schauderSpaceD2_completeSpace (n : ℕ) : CompleteSpace (D2 n) :=
  inferInstanceAs (CompleteSpace (ComplexVector n →L[ℝ] (ComplexVector n →L[ℝ] ℝ)))

/-- The four stored jets are rho^-2 u, rho^-1 Du, D2u, and ut. -/
abbrev SchauderAmbient (P : UniformChartPartition g) (T gamma : ℝ) :=
  (HolderSpace P T gamma × LocalHolderSpace (D1 n) P T gamma) ×
    (LocalHolderSpace (D2 n) P T gamma × HolderSpace P T gamma)

def rawZeroCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] HolderSpace P T gamma :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)
def rawOneCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] LocalHolderSpace (D1 n) P T gamma :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)
def rawTwoCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] LocalHolderSpace (D2 n) P T gamma :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
def rawTimeCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] HolderSpace P T gamma :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def ambientFunctionHolderCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] HolderSpace P T gamma := P.radius^2 • rawZeroCLM P T gamma
def ambientGradientHolderCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] LocalHolderSpace (D1 n) P T gamma := P.radius • rawOneCLM P T gamma

def ambientValueCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] BoundedContinuousFunction (Cylinder M T) ℝ :=
  (valueCLM P T gamma).comp (ambientFunctionHolderCLM P T gamma)
def ambientGradientCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] BoundedContinuousFunction (LocalCylinder P T) (D1 n) :=
  (localValueCLM (D1 n) P T gamma).comp (ambientGradientHolderCLM P T gamma)
def ambientHessianCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] BoundedContinuousFunction (LocalCylinder P T) (D2 n) :=
  (localValueCLM (D2 n) P T gamma).comp (rawTwoCLM P T gamma)
def ambientTimeCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    SchauderAmbient P T gamma →L[ℝ] BoundedContinuousFunction (Cylinder M T) ℝ :=
  (valueCLM P T gamma).comp (rawTimeCLM P T gamma)

def ambientEvalCLM (P : UniformChartPartition g) (T gamma : ℝ) (q : Cylinder M T) :
    SchauderAmbient P T gamma →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp (ambientValueCLM P T gamma)
def ambientGradientEvalCLM (P : UniformChartPartition g) (T gamma : ℝ) (q : LocalCylinder P T) :
    SchauderAmbient P T gamma →L[ℝ] D1 n :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp (ambientGradientCLM P T gamma)
def ambientHessianEvalCLM (P : UniformChartPartition g) (T gamma : ℝ) (q : LocalCylinder P T) :
    SchauderAmbient P T gamma →L[ℝ] D2 n :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp (ambientHessianCLM P T gamma)
def ambientTimeEvalCLM (P : UniformChartPartition g) (T gamma : ℝ) (q : Cylinder M T) :
    SchauderAmbient P T gamma →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp (ambientTimeCLM P T gamma)

/-- Clamping makes the entire real parameter path genuinely continuous. -/
def chartSegment (P : UniformChartPartition g)
    (z z' : ↥(ball (0 : ComplexVector n) P.radius)) (theta : ℝ) :
    ↥(ball (0 : ComplexVector n) P.radius) :=
  ⟨AffineMap.lineMap (z : ComplexVector n) (z' : ComplexVector n)
    (projIcc (0 : ℝ) 1 zero_le_one theta : ℝ),
    (convex_ball (0 : ComplexVector n) P.radius).lineMap_mem z.property z'.property
      (projIcc (0 : ℝ) 1 zero_le_one theta).property⟩

theorem chartSegment_continuous (P : UniformChartPartition g)
    (z z' : ↥(ball (0 : ComplexVector n) P.radius)) : Continuous (chartSegment P z z') := by
  apply Continuous.subtype_mk
  simp only [AffineMap.lineMap_apply_module']
  exact ((continuous_subtype_val.comp continuous_projIcc).smul continuous_const).add continuous_const

theorem chartSegment_of_mem (P : UniformChartPartition g)
    (z z' : ↥(ball (0 : ComplexVector n) P.radius)) {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) 1) :
    (chartSegment P z z' theta : ComplexVector n) = AffineMap.lineMap (z : ComplexVector n) (z' : ComplexVector n) theta := by
  simp only [chartSegment,projIcc_of_mem,htheta]

def localSegmentPath (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (z z' : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) (theta : ℝ) : LocalCylinder P T :=
  ⟨p,(chartSegment P z z' theta,t)⟩

theorem localSegmentPath_continuous (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (z z' : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    Continuous (localSegmentPath P T p z z' t) :=
  continuous_sigmaMk.comp ((chartSegment_continuous P z z').prodMk continuous_const)

def closedTimePath (T : ℝ) (hT : 0 < T) (x : M.Carrier) (tau : ℝ) : Cylinder M T :=
  (x,projIcc (0 : ℝ) T hT.le tau)

theorem closedTimePath_continuous (T : ℝ) (hT : 0 < T) (x : M.Carrier) :
    Continuous (closedTimePath T hT x) := continuous_const.prodMk continuous_projIcc

def spatialFTCDefect (P : UniformChartPartition g) (T gamma : ℝ) (p : P.centers)
    (z z' : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    SchauderAmbient P T gamma →L[ℝ] ℝ :=
  ambientEvalCLM P T gamma (chartPoint P T p (z',t))-
    ambientEvalCLM P T gamma (chartPoint P T p (z,t))-
    (pathIntegralCLM (localSegmentPath P T p z z' t) (localSegmentPath_continuous P T p z z' t)
      (ContinuousLinearMap.apply ℝ ℝ ((z' : ComplexVector n)-z)) 0 1).comp (ambientGradientCLM P T gamma)

def gradientFTCDefect (P : UniformChartPartition g) (T gamma : ℝ) (p : P.centers)
    (z z' : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    SchauderAmbient P T gamma →L[ℝ] D1 n :=
  ambientGradientEvalCLM P T gamma ⟨p,(z',t)⟩-ambientGradientEvalCLM P T gamma ⟨p,(z,t)⟩-
    (pathIntegralCLM (localSegmentPath P T p z z' t) (localSegmentPath_continuous P T p z z' t)
      (ContinuousLinearMap.apply ℝ (D1 n) ((z' : ComplexVector n)-z)) 0 1).comp (ambientHessianCLM P T gamma)

def timeFTCDefect (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T)
    (x : M.Carrier) (s t : Time T) : SchauderAmbient P T gamma →L[ℝ] ℝ :=
  ambientEvalCLM P T gamma (x,t)-ambientEvalCLM P T gamma (x,s)-
    (pathIntegralCLM (closedTimePath T hT x) (closedTimePath_continuous T hT x)
      (ContinuousLinearMap.id ℝ ℝ) s t).comp (ambientTimeCLM P T gamma)

def initialFTCDefect (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T) (x : M.Carrier) :
    SchauderAmbient P T gamma →L[ℝ] ℝ := ambientEvalCLM P T gamma (x,⟨0,⟨le_rfl,hT.le⟩⟩)

/-- Literal FTC kernels in the product of the four genuinely scaled jets. -/
def SchauderSpace (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T) :
    Submodule ℝ (SchauderAmbient P T gamma) where
  carrier := {a | (∀ p z z' t, spatialFTCDefect P T gamma p z z' t a = 0 ∧
      gradientFTCDefect P T gamma p z z' t a = 0) ∧
    (∀ x s t, timeFTCDefect P T gamma hT x s t a = 0) ∧
    ∀ x, initialFTCDefect P T gamma hT x a = 0}
  zero_mem' := ⟨fun p z z' t => ⟨(spatialFTCDefect P T gamma p z z' t).map_zero,
    (gradientFTCDefect P T gamma p z z' t).map_zero⟩,
    fun x s t => (timeFTCDefect P T gamma hT x s t).map_zero,
    fun x => (initialFTCDefect P T gamma hT x).map_zero⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨?_,?_,?_⟩
    · intro p z z' t
      simp only [map_add,(ha.1 p z z' t).1,(hb.1 p z z' t).1,
        (ha.1 p z z' t).2,(hb.1 p z z' t).2,add_zero,and_self]
    · intro x s t
      simp only [map_add,ha.2.1 x s t,hb.2.1 x s t,add_zero]
    · intro x
      simp only [map_add,ha.2.2 x,hb.2.2 x,add_zero]
  smul_mem' := by
    intro c a ha
    refine ⟨?_,?_,?_⟩
    · intro p z z' t
      simp only [map_smul,(ha.1 p z z' t).1,(ha.1 p z z' t).2,smul_zero,and_self]
    · intro x s t
      simp only [map_smul,ha.2.1 x s t,smul_zero]
    · intro x
      simp only [map_smul,ha.2.2 x,smul_zero]

theorem schauderSpace_isClosed (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T) :
    IsClosed (SchauderSpace P T gamma hT : Set (SchauderAmbient P T gamma)) := by
  change IsClosed {a : SchauderAmbient P T gamma |
    (∀ p z z' t, spatialFTCDefect P T gamma p z z' t a = 0 ∧ gradientFTCDefect P T gamma p z z' t a = 0) ∧
    (∀ x s t, timeFTCDefect P T gamma hT x s t a = 0) ∧ ∀ x, initialFTCDefect P T gamma hT x a = 0}
  simp only [Set.ofPred_and,Set.ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro p
    apply isClosed_iInter
    intro z
    apply isClosed_iInter
    intro z'
    apply isClosed_iInter
    intro t
    exact (isClosed_eq (spatialFTCDefect P T gamma _ _ _ _).continuous continuous_const).inter
      (isClosed_eq (gradientFTCDefect P T gamma _ _ _ _).continuous continuous_const)
  · apply IsClosed.inter
    · apply isClosed_iInter
      intro x
      apply isClosed_iInter
      intro s
      apply isClosed_iInter
      intro t
      exact isClosed_eq (timeFTCDefect P T gamma hT _ _ _).continuous continuous_const
    · apply isClosed_iInter
      intro x
      exact isClosed_eq (initialFTCDefect P T gamma hT x).continuous continuous_const

instance schauderSpace_normedAddCommGroup (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T) :
    NormedAddCommGroup (SchauderSpace P T gamma hT) := inferInstance
instance schauderSpace_normedSpace (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T) :
    NormedSpace ℝ (SchauderSpace P T gamma hT) := inferInstance
instance schauderSpace_completeSpace (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T) :
    CompleteSpace (SchauderSpace P T gamma hT) := (schauderSpace_isClosed P T gamma hT).completeSpace_coe

end Yau.LeafProofs.L17SchauderAux
