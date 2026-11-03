import Yau.LeafProofs.L14CutoffNorm
import Yau.LeafProofs.L03

noncomputable section
open scoped Topology ContDiff Matrix
open MeasureTheory Filter Module

namespace Yau.LeafProofs.L14Aux

def complexCoordinateCLM (q : Fin 2) : ℂ →L[ℝ] ℝ :=
  (Complex.basisOneI.coord q).toContinuousLinearMap

def complexMultiplicationEntryCLM (q d : Fin 2) : ℂ →L[ℝ] ℝ :=
  (complexCoordinateCLM q).comp (ContinuousLinearMap.mul ℝ ℂ (Complex.basisOneI d))

theorem complexCoordinate_mul (q : Fin 2) (c z : ℂ) :
    complexCoordinateCLM q (c * z) =
      ∑ d, complexMultiplicationEntryCLM q d c * complexCoordinateCLM d z := by
  have he : (∑ d, complexCoordinateCLM d z • Complex.basisOneI d) = z :=
    Complex.basisOneI.sum_repr z
  conv_lhs => rw [← he]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [mul_smul_comm, map_smul]
  change complexCoordinateCLM d z * complexCoordinateCLM q (c * Complex.basisOneI d) = _
  change _ = complexCoordinateCLM q (Complex.basisOneI d * c) * complexCoordinateCLM d z
  rw [mul_comm c, mul_comm]

theorem complexMultiplicationEntry_mul_ofReal (q d : Fin 2) (c : ℂ) (t : ℝ) :
    complexMultiplicationEntryCLM q d (c * (t : ℂ)) =
      complexMultiplicationEntryCLM q d c * t := by
  have he : c * (t : ℂ) = t • c := by simp only [Complex.real_smul]; ring
  rw [he, map_smul, smul_eq_mul, mul_comm]

theorem complexFormalRow_realification {α ι : Type*} [Fintype α] [Fintype ι]
    (q : Fin 2) (a da : α → ι → ℂ) (b u : α → ℂ) (ψ : ℝ) (Dψ : ι → ℝ) :
    (∑ c, complexCoordinateCLM q (u c *
      (-(∑ i, (a c i * (Dψ i : ℂ) + da c i * (ψ : ℂ))) + b c * (ψ : ℂ)))) =
      ∑ p : α × Fin 2, complexCoordinateCLM p.2 (u p.1) *
        (-(∑ i, (complexMultiplicationEntryCLM q p.2 (a p.1 i) * Dψ i +
          complexMultiplicationEntryCLM q p.2 (da p.1 i) * ψ)) +
          complexMultiplicationEntryCLM q p.2 (b p.1) * ψ) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [mul_comm (u c), complexCoordinate_mul]
  apply Finset.sum_congr rfl
  intro d _
  simp only [map_add, map_neg, map_sum, complexMultiplicationEntry_mul_ofReal]
  ring

theorem complexMultiplicationEntry_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q d : Fin 2) (a : X → ℂ) (x v : X) (ha : DifferentiableAt ℝ a x) :
    fderiv ℝ (fun y => complexMultiplicationEntryCLM q d (a y)) x v =
      complexMultiplicationEntryCLM q d (fderiv ℝ a x v) := by
  have he := ((complexMultiplicationEntryCLM q d).hasFDerivAt.comp x ha.hasFDerivAt).fderiv
  exact congrArg (fun L : X →L[ℝ] ℝ => L v) he

def realifiedFirstOrderDerivative {X α β ι : Type*}
    (a : β → α → ι → X → ℂ) : (β × Fin 2) → (α × Fin 2) → ι → X → ℝ :=
  fun r c i x => complexMultiplicationEntryCLM r.2 c.2 (a r.1 c.1 i x)

def realifiedFirstOrderValue {X α β : Type*}
    (b : β → α → X → ℂ) : (β × Fin 2) → (α × Fin 2) → X → ℝ :=
  fun r c x => complexMultiplicationEntryCLM r.2 c.2 (b r.1 c.1 x)

def realifiedField {X α : Type*} (u : X → α → ℂ) : X → (α × Fin 2) → ℝ :=
  fun x c => complexCoordinateCLM c.2 (u x c.1)

theorem firstOrderSystemWeakEquation_of_complex_rows {X α β ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [Fintype α] [Fintype ι]
    (ν : Measure X) [IsLocallyFiniteMeasure ν] (v : ι → X)
    (a : β → α → ι → X → ℂ) (b : β → α → X → ℂ)
    (ha : ∀ r c i, ContDiff ℝ 1 (a r c i)) (hb : ∀ r c, Continuous (b r c))
    (u : X → α → ℂ) (w : X → β → ℂ)
    (hu : ∀ c : α × Fin 2, MemLp (fun z => realifiedField u z c) 2 ν)
    (hrow : ∀ r q (ψ : X → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, ψ z * complexCoordinateCLM q (w z r) ∂ν) =
        ∫ z, ∑ c, complexCoordinateCLM q (u z c *
          (-(∑ i, (a r c i z * (fderiv ℝ ψ z (v i) : ℂ) +
            fderiv ℝ (a r c i) z (v i) * (ψ z : ℂ))) + b r c z * (ψ z : ℂ))) ∂ν) :
    Yau.LeafProofs.L03.firstOrderSystemWeakEquation ν v
      (realifiedFirstOrderDerivative a) (realifiedFirstOrderValue b)
      (realifiedField u) (realifiedField w) := by
  apply Yau.LeafProofs.L03.firstOrderSystemWeakEquation_of_row_integral ν v
    (realifiedFirstOrderDerivative a) (realifiedFirstOrderValue b)
    (fun r c i => (complexMultiplicationEntryCLM r.2 c.2).contDiff.comp (ha r.1 c.1 i))
    (fun r c => (complexMultiplicationEntryCLM r.2 c.2).continuous.comp (hb r.1 c.1))
    (realifiedField u) (realifiedField w) hu
  rintro ⟨r, q⟩ ψ hψ hcψ
  simp only [realifiedField]
  rw [hrow r q ψ hψ hcψ]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only [realifiedFirstOrderDerivative, realifiedFirstOrderValue, realifiedField]
  have hder (c : α × Fin 2) (i : ι) :
      fderiv ℝ (realifiedFirstOrderDerivative a (r, q) c i) z (v i) =
      complexMultiplicationEntryCLM q c.2 (fderiv ℝ (a r c.1 i) z (v i)) := by
    change fderiv ℝ (fun y => complexMultiplicationEntryCLM q c.2 (a r c.1 i y)) z (v i) = _
    exact complexMultiplicationEntry_fderiv q c.2 _ z (v i) ((ha r c.1 i).differentiable one_ne_zero z)
  simp_rw [hder]
  exact complexFormalRow_realification q (fun c i => a r c i z)
    (fun c i => fderiv ℝ (a r c i) z (v i)) (b r · z) (u z) (ψ z) (fun i => fderiv ℝ ψ z (v i))

def complexFirstOrderSystemApply {X α β ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype α] [Fintype ι]
    (v : ι → X) (a : β → α → ι → X → ℂ) (b : β → α → X → ℂ)
    (u : X → α → ℂ) : X → β → ℂ :=
  fun x r => ∑ c, ((∑ i, a r c i x * fderiv ℝ (fun y => u y c) x (v i)) + b r c x * u x c)

theorem complexCoordinate_fderiv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : Fin 2) (u : X → ℂ) (x v : X) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => complexCoordinateCLM q (u y)) x v =
      complexCoordinateCLM q (fderiv ℝ u x v) := by
  have he := ((complexCoordinateCLM q).hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  exact congrArg (fun L : X →L[ℝ] ℝ => L v) he

theorem firstOrderSystemApply_realification {X α β ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype α] [Fintype ι]
    (v : ι → X) (a : β → α → ι → X → ℂ) (b : β → α → X → ℂ)
    (u : X → α → ℂ) (x : X) (hu : ∀ c, DifferentiableAt ℝ (fun y => u y c) x)
    (r : β) (q : Fin 2) :
    complexCoordinateCLM q (complexFirstOrderSystemApply v a b u x r) =
      Yau.LeafProofs.L03.firstOrderSystemApply v (realifiedFirstOrderDerivative a)
        (realifiedFirstOrderValue b) (realifiedField u) x (r, q) := by
  have hder (c : α × Fin 2) (i : ι) :
      fderiv ℝ (fun y => realifiedField u y c) x (v i) =
      complexCoordinateCLM c.2 (fderiv ℝ (fun y => u y c.1) x (v i)) :=
    complexCoordinate_fderiv c.2 _ x (v i) (hu c.1)
  simp only [complexFirstOrderSystemApply, Yau.LeafProofs.L03.firstOrderSystemApply,
    map_sum, map_add, complexCoordinate_mul, Fintype.sum_prod_type]
  simp_rw [hder]
  dsimp only [realifiedFirstOrderDerivative, realifiedFirstOrderValue, realifiedField]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_add_distrib, Finset.sum_comm]

def complexifyField {X α : Type*} (u : X → (α × Fin 2) → ℝ) : X → α → ℂ :=
  fun x c => Complex.basisOneI.equivFun.symm (fun d => u x (c, d))

theorem complexCoordinate_complexifyField {X α : Type*}
    (u : X → (α × Fin 2) → ℝ) (x : X) (c : α) (q : Fin 2) :
    complexCoordinateCLM q (complexifyField u x c) = u x (c, q) := by
  exact congrArg (fun f : Fin 2 → ℝ => f q) (Complex.basisOneI.equivFun.apply_symm_apply (fun d => u x (c, d)))

theorem realified_complexifyField {X α : Type*} (u : X → (α × Fin 2) → ℝ) :
    realifiedField (complexifyField u) = u := by
  funext x p
  exact complexCoordinate_complexifyField u x p.1 p.2

theorem complexifyField_contDiff {X α : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u : X → (α × Fin 2) → ℝ) (hu : ∀ p, ContDiff ℝ ∞ (fun x => u x p)) (c : α) :
    ContDiff ℝ ∞ (fun x => complexifyField u x c) :=
  Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm.contDiff.comp
    (contDiff_pi.mpr (fun d => hu (c, d)))

theorem hasCompactSupport_finPi {X ι : Type*} [TopologicalSpace X] [T2Space X] [Fintype ι]
    (u : X → ι → ℝ) (hu : ∀ i, HasCompactSupport (fun x => u x i)) : HasCompactSupport u := by
  have hK : IsCompact (⋃ i, tsupport (fun x => u x i)) := isCompact_iUnion hu
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  apply hx
  funext i
  exact image_eq_zero_of_notMem_tsupport (f := fun y => u y i)
    (fun hi => hn (Set.mem_iUnion.mpr ⟨i, hi⟩))

theorem complexifyField_compact {X α : Type*} [TopologicalSpace X] [T2Space X]
    (u : X → (α × Fin 2) → ℝ) (hu : ∀ p, HasCompactSupport (fun x => u x p)) (c : α) :
    HasCompactSupport (fun x => complexifyField u x c) := by
  exact (hasCompactSupport_finPi (fun x d => u x (c, d)) (fun d => hu (c, d))).comp_left
    (show Complex.basisOneI.equivFun.symm (0 : Fin 2 → ℝ) = 0 from map_zero _)

open scoped Convolution in
theorem complex_firstOrder_mollifier_graph_tendsto_of_rows {X α β ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] [Fintype α] [Fintype ι]
    (ν : Measure X) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]
    (v : ι → X) (a : β → α → ι → X → ℂ) (b : β → α → X → ℂ)
    (ha : ∀ r c i, ContDiff ℝ ∞ (a r c i)) (hca : ∀ r c i, HasCompactSupport (a r c i))
    (hb : ∀ r c, Continuous (b r c)) (hcb : ∀ r c, HasCompactSupport (b r c))
    (u : X → α → ℂ) (w : X → β → ℂ)
    (hu : ∀ c : α × Fin 2, MemLp (fun z => realifiedField u z c) 2 ν)
    (hcu : ∀ c : α × Fin 2, HasCompactSupport (fun z => realifiedField u z c))
    (hw : ∀ r : β × Fin 2, MemLp (fun z => realifiedField w z r) 2 ν)
    (hcw : ∀ r : β × Fin 2, HasCompactSupport (fun z => realifiedField w z r))
    (hrow : ∀ r q (ψ : X → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, ψ z * complexCoordinateCLM q (w z r) ∂ν) =
        ∫ z, ∑ c, complexCoordinateCLM q (u z c *
          (-(∑ i, (a r c i z * (fderiv ℝ ψ z (v i) : ℂ) +
            fderiv ℝ (a r c i) z (v i) * (ψ z : ℂ))) + b r c z * (ψ z : ℂ))) ∂ν)
    (ρ : X → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1) (ht : Tendsto ε atTop (𝓝 0)) :
    let UR : ℕ → X → (α × Fin 2) → ℝ := fun j x c =>
      (Yau.LeafProofs.L03.rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
        (fun y => realifiedField u y c)) x
    let U := fun j => complexifyField (UR j)
    (∀ j c, ContDiff ℝ ∞ (fun x => U j x c) ∧ HasCompactSupport (fun x => U j x c)) ∧
      (∀ c q, Tendsto (fun j => ∫ x, ‖complexCoordinateCLM q (U j x c - u x c)‖ ^ 2 ∂ν) atTop (𝓝 0)) ∧
      ∀ r q, (∀ j, MemLp (fun x => complexCoordinateCLM q
        (complexFirstOrderSystemApply v a b (U j) x r)) 2 ν) ∧
        Tendsto (fun j => ∫ x, ‖complexCoordinateCLM q
          (complexFirstOrderSystemApply v a b (U j) x r - w x r)‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  classical
  let ar := realifiedFirstOrderDerivative a
  let br := realifiedFirstOrderValue b
  have har (r : β × Fin 2) (c : α × Fin 2) (i : ι) : ContDiff ℝ ∞ (ar r c i) :=
    (complexMultiplicationEntryCLM r.2 c.2).contDiff.comp (ha r.1 c.1 i)
  have hcar (r : β × Fin 2) (c : α × Fin 2) (i : ι) : HasCompactSupport (ar r c i) :=
    (hca r.1 c.1 i).comp_left (map_zero (complexMultiplicationEntryCLM r.2 c.2))
  choose A K hAK using fun r c i => Yau.LeafProofs.L03.compact_contDiff_coefficient_bounds
    (ar r c i) (har r c i) (hcar r c i)
  have hbr (r : β × Fin 2) (c : α × Fin 2) : Continuous (br r c) :=
    (complexMultiplicationEntryCLM r.2 c.2).continuous.comp (hb r.1 c.1)
  have hcbr (r : β × Fin 2) (c : α × Fin 2) : HasCompactSupport (br r c) :=
    (hcb r.1 c.1).comp_left (map_zero (complexMultiplicationEntryCLM r.2 c.2))
  choose B hB using fun r c => (hbr r c).bounded_above_of_compact_support (hcbr r c)
  have hweak := firstOrderSystemWeakEquation_of_complex_rows ν v a b
    (fun r c i => (ha r c i).of_le (by simp)) hb u w hu hrow
  let UR : ℕ → X → (α × Fin 2) → ℝ := fun j x c =>
    (Yau.LeafProofs.L03.rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν]
      (fun y => realifiedField u y c)) x
  let U := fun j => complexifyField (UR j)
  have hs := Yau.LeafProofs.L03.firstOrderSystemWeakEquation_mollifier_graph_tendsto ν v ar br
    (fun r c i => (har r c i).of_le (by simp)) K (fun r c i => (hAK r c i).2) A
    (fun r c i => (hAK r c i).1) hbr B hB (realifiedField u) (realifiedField w)
    hu hcu hw hcw hweak ρ hρ hcρ hρ0 hρ1 ε hε hε1 ht
  rcases hs with ⟨hUR, hUt, hWt⟩
  have hU (j : ℕ) (c : α) : ContDiff ℝ ∞ (fun x => U j x c) :=
    complexifyField_contDiff (UR j) (fun p => (hUR j p).1) c
  have hP (j : ℕ) (x : X) (r : β) (q : Fin 2) :
      complexCoordinateCLM q (complexFirstOrderSystemApply v a b (U j) x r) =
      Yau.LeafProofs.L03.firstOrderSystemApply v ar br (UR j) x (r, q) := by
    have he := firstOrderSystemApply_realification v a b (U j) x
      (fun c => (hU j c).differentiable (by simp) x) r q
    simpa only [U, realified_complexifyField] using he
  refine ⟨fun j c => ⟨hU j c, complexifyField_compact (UR j) (fun p => (hUR j p).2) c⟩, ?_, ?_⟩
  · intro c q
    simpa only [U, map_sub, complexCoordinate_complexifyField, realifiedField] using hUt (c, q)
  · intro r q
    refine ⟨?_, ?_⟩
    · intro j
      exact MemLp.ae_eq (Eventually.of_forall fun x => (hP j x r q).symm) ((hWt (r, q)).1 j)
    · change Tendsto (fun j => ∫ x, ‖complexCoordinateCLM q
        (complexFirstOrderSystemApply v a b (U j) x r - w x r)‖ ^ 2 ∂ν) atTop (𝓝 0)
      simp_rw [map_sub, hP]
      exact (hWt (r, q)).2

end Yau.LeafProofs.L14Aux
