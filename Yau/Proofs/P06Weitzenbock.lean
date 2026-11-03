import Yau.Proofs.G04CovariantTwoForm
import Yau.Proofs.G04FormCodifferential
import Yau.LeafProofs.L23RoughLapCommutator

/-! The Weitzenböck computation for arbitrary real two-forms. -/

noncomputable section
open Filter
open scoped Manifold Topology ContDiff Matrix

namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L23Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- Both derivative directions are covariant slots. -/
def secondTwo (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) (a b d e : RIdx n) : ℝ :=
  covariantD h c (covariantD h c (formComponents A c)) z
    (Fin.cons a (Fin.cons b ![d,e]))

/-- The negative metric trace of the actual second covariant derivative. -/
def roughTwoComponents (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) (I : Fin 2 → RIdx n) : ℝ :=
  -∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b *
    covariantD h c (covariantD h c (formComponents A c)) z
      (Fin.cons a (Fin.cons b I))

/-- Curvature of the original Levi-Civita connection, acting on both slots. -/
def curvatureTwoComponents (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) (I : Fin 2 → RIdx n) : ℝ :=
  ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b *
    (-(∑ p, riemannCoeff h c z a (I 0) b p * chartFormMatrix A c z p (I 1)) -
      (∑ p, riemannCoeff h c z a (I 0) (I 1) p * chartFormMatrix A c z b p) +
      (∑ p, riemannCoeff h c z a (I 1) b p * chartFormMatrix A c z p (I 0)) +
      (∑ p, riemannCoeff h c z a (I 1) (I 0) p * chartFormMatrix A c z b p))

theorem covariantD_two (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) (v : Fin 3 → RIdx n) :
    covariantD h c (formComponents A c) z v =
      covariantTwo h A c z (v 0) (v 1) (v 2) := by
  have hv : v = Fin.cons (v 0) ![v 1,v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, covariantD_form_cons]
  rfl

/-- In particular, the connection differentiates the second direction b. -/
theorem secondTwo_formula (h : HermitianField M) (A : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) (a b d e : RIdx n) :
    secondTwo h A c z a b d e =
      rDeriv (fun w => covariantTwo h A c w b d e) z a -
        (∑ p, christoffel h c z p a b * covariantTwo h A c z p d e) -
        (∑ p, christoffel h c z p a d * covariantTwo h A c z b p e) -
        (∑ p, christoffel h c z p a e * covariantTwo h A c z b d p) := by
  have hu₀ (p : RIdx n) : Function.update ![b,d,e] (0 : Fin 3) p = ![p,d,e] := by
    funext i
    fin_cases i <;> simp
  have hu₁ (p : RIdx n) : Function.update ![b,d,e] (1 : Fin 3) p = ![b,p,e] := by
    funext i
    fin_cases i <;> simp
  have hu₂ (p : RIdx n) : Function.update ![b,d,e] (2 : Fin 3) p = ![b,d,p] := by
    funext i
    fin_cases i <;> simp
  unfold secondTwo
  rw [Matrix.Fin.cons_vecCons]
  rw [covariantD_cons]
  simp [tensorConnectionAction, tensorSlotAction, L12Aux.connectionMatrix,
    Fin.sum_univ_succ, Finset.sum_empty, add_zero, Fin.cons_zero, Fin.cons_succ,
    hu₀, hu₁, hu₂, covariantD_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  ring

theorem secondTwo_commutator (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (a b d e : RIdx n) :
    secondTwo h A c z a b d e - secondTwo h A c z b a d e =
      -(∑ p, riemannCoeff h c z a b d p * chartFormMatrix A c z p e) -
        ∑ p, riemannCoeff h c z a b e p * chartFormMatrix A c z d p := by
  have he := covariantD_commutator h hs c (formComponents A c) (hA c) hz a b ![d,e]
  have hu₀ (p : RIdx n) : Function.update ![d,e] (0 : Fin 2) p = ![p,e] := by
    funext i
    fin_cases i <;> simp
  have hu₁ (p : RIdx n) : Function.update ![d,e] (1 : Fin 2) p = ![d,p] := by
    funext i
    fin_cases i <;> simp
  simpa only [secondTwo, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, hu₀, hu₁, formComponents_degree_two, neg_add_rev,
    sub_eq_add_neg, add_comm] using he

/-- The exterior derivative is the cyclic covariant derivative, without any
closedness assumption. -/
theorem exteriorTwo_eq_covariant (h : HermitianField M) (A : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) (a b d : RIdx n) :
    exteriorComponents (formComponents A c) z ![a,b,d] =
      covariantTwo h A c z a b d + covariantTwo h A c z b d a +
        covariantTwo h A c z d a b := by
  have heq : (fun w => chartFormMatrix A c w d a) =
      (fun w => -chartFormMatrix A c w a d) :=
    funext (fun w => chartFormMatrix_skew A c w a d)
  have hd : rDeriv (fun w => chartFormMatrix A c w d a) z b =
      -rDeriv (fun w => chartFormMatrix A c w a d) z b := by
    rw [heq]
    simp only [rDeriv, fderiv_fun_neg, neg_apply]
  have hc : (∑ p, christoffel h c z p a b * chartFormMatrix A c z p d) +
      (∑ p, christoffel h c z p a d * chartFormMatrix A c z b p) +
      (∑ p, christoffel h c z p b d * chartFormMatrix A c z p a) +
      (∑ p, christoffel h c z p b a * chartFormMatrix A c z d p) +
      (∑ p, christoffel h c z p d a * chartFormMatrix A c z p b) +
      (∑ p, christoffel h c z p d b * chartFormMatrix A c z a p) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p _
    rw [L12Aux.christoffel_symm_lower h c z p b a,
      L12Aux.christoffel_symm_lower h c z p d a,
      L12Aux.christoffel_symm_lower h c z p d b,
      chartFormMatrix_skew A c z p d, chartFormMatrix_skew A c z b p,
      chartFormMatrix_skew A c z p a]
    ring
  simp [exteriorComponents, Fin.sum_univ_succ, Fin.succAbove,
    formComponents_degree_two]
  rw [covariantTwo_formula, covariantTwo_formula, covariantTwo_formula, hd]
  linarith

def cycleThree : Equiv.Perm (Fin 3) :=
  (Equiv.swap 0 1).trans (Equiv.swap 0 2)

theorem comp_cycleThree {ι : Type*} (v : Fin 3 → ι) :
    v ∘ cycleThree = ![v 1,v 2,v 0] := by
  funext i
  fin_cases i <;> simp [cycleThree, Equiv.swap_apply_def]

theorem comp_cycleThree_symm {ι : Type*} (v : Fin 3 → ι) :
    v ∘ cycleThree.symm = ![v 2,v 0,v 1] := by
  funext i
  fin_cases i <;> simp [cycleThree, Equiv.swap_apply_def]

theorem exteriorTwo_tensor (h : HermitianField M) (A : RealForm M 2)
    (c : M.Carrier) :
    exteriorComponents (formComponents A c) = fun z v =>
      covariantD h c (formComponents A c) z v +
        covariantD h c (formComponents A c) z (v ∘ cycleThree) +
        covariantD h c (formComponents A c) z (v ∘ cycleThree.symm) := by
  funext z v
  have hv : v = ![v 0,v 1,v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, exteriorTwo_eq_covariant, comp_cycleThree, comp_cycleThree_symm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rfl

theorem covariant_exteriorTwo (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (a b d e : RIdx n) :
    covariantComponents h c (exteriorComponents (formComponents A c)) z a ![b,d,e] =
      secondTwo h A c z a b d e + secondTwo h A c z a d e b +
        secondTwo h A c z a e b d := by
  let U := covariantD h c (formComponents A c)
  have hU (v : Fin 3 → RIdx n) : DifferentiableAt ℝ (fun w => U w v) z :=
    ((covariantD_contDiffOn h hs c (formComponents A c) (hA c) v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hV (v : Fin 3 → RIdx n) :
      DifferentiableAt ℝ (fun w => U w (v ∘ cycleThree)) z := hU _
  have hW (v : Fin 3 → RIdx n) :
      DifferentiableAt ℝ (fun w => U w (v ∘ cycleThree.symm)) z := hU _
  change covariantD h c (exteriorComponents (formComponents A c)) z
    (Fin.cons a ![b,d,e]) = _
  rw [exteriorTwo_tensor h A c]
  have hlin := covariantD_add_at h c
    (fun w => U w + fun v => U w (v ∘ cycleThree))
    (fun w v => U w (v ∘ cycleThree.symm)) z
    (fun v => (hU v).add (hV v)) hW
  rw [covariantD_add_at h c U (fun w v => U w (v ∘ cycleThree)) z hU hV] at hlin
  have he := congrFun hlin (Fin.cons a ![b,d,e])
  simp only [Pi.add_apply] at he
  rw [covariantD_permute_cons h c U cycleThree z a ![b,d,e],
    covariantD_permute_cons h c U cycleThree.symm z a ![b,d,e],
    comp_cycleThree, comp_cycleThree_symm] at he
  have hf : (fun w => (U w + fun v => U w (v ∘ cycleThree)) +
      fun v => U w (v ∘ cycleThree.symm)) =
      (fun w v => U w v + U w (v ∘ cycleThree) + U w (v ∘ cycleThree.symm)) := by
    funext w v
    rfl
  rw [hf] at he
  simpa [secondTwo, U, Matrix.Fin.cons_vecCons, Matrix.head_cons, Matrix.tail_cons] using he

theorem covariantD_neg (h : HermitianField M) (c : M.Carrier)
    {r : ℕ} (F : FormComponents n r) (z : ComplexVector n) :
    covariantD h c (fun w => -F w) z = -covariantD h c F z := by
  funext v
  simp only [covariantD, Pi.neg_apply, rDeriv, fderiv_fun_neg,
    neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

theorem exteriorOne_eq_covariant (h : HermitianField M) (c : M.Carrier)
    (F : FormComponents n 1) (z : ComplexVector n) (a b : RIdx n) :
    exteriorComponents F z ![a,b] =
      covariantComponents h c F z a ![b] - covariantComponents h c F z b ![a] := by
  have h₀ : (fun s : Fin 1 => ![a,b] ((0 : Fin 2).succAbove s)) = ![b] := by
    funext s
    fin_cases s <;> rfl
  have h₁ : (fun s : Fin 1 => ![a,b] ((1 : Fin 2).succAbove s)) = ![a] := by
    funext s
    fin_cases s <;> rfl
  have hu (q p : RIdx n) : Function.update ![q] (0 : Fin 1) p = ![p] := by
    funext s
    fin_cases s <;> simp
  have he (p : RIdx n) : christoffel h c z p a b = christoffel h c z p b a :=
    L12Aux.christoffel_symm_lower h c z p a b
  unfold exteriorComponents
  rw [Fin.sum_univ_two, h₀, h₁]
  simp [covariantComponents, Fin.sum_univ_one, hu, he]
  ring

theorem covariant_codifferentialTwo (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (i d : RIdx n) :
    covariantComponents h c (codifferentialComponents h c (formComponents A c)) z i ![d] =
      -∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b * secondTwo h A c z i a b d := by
  have hU (v : Fin 3 → RIdx n) :
      DifferentiableAt ℝ (fun w => covariantD h c (formComponents A c) w v) z :=
    ((covariantD_contDiffOn h hs c (formComponents A c) (hA c) v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hδ : codifferentialComponents h c (formComponents A c) =
      fun w => -tensorMetricTrace (realMetricFn h c w)⁻¹
        (covariantD h c (formComponents A c) w) :=
    funext (fun w => codifferential_tensor_trace h A c w)
  change covariantD h c (codifferentialComponents h c (formComponents A c)) z
    (Fin.cons i ![d]) = _
  rw [hδ, covariantD_neg]
  simp only [Pi.neg_apply]
  rw [covariantD_tensorMetricTrace h hs c _ hz hU]
  rfl

theorem exterior_codifferentialTwo (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (d e : RIdx n) :
    exteriorComponents (codifferentialComponents h c (formComponents A c)) z ![d,e] =
      -(∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b * secondTwo h A c z d a b e) +
        ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b * secondTwo h A c z e a b d := by
  rw [exteriorOne_eq_covariant, covariant_codifferentialTwo h hs A hA c hz,
    covariant_codifferentialTwo h hs A hA c hz]
  ring

theorem secondTwo_skew (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (a b d e : RIdx n) :
    secondTwo h A c z a b e d = -secondTwo h A c z a b d e := by
  let U := covariantD h c (formComponents A c)
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hsmooth (v : Fin 3 → RIdx n) : DifferentiableAt ℝ (fun w => U w v) z :=
    ((covariantD_contDiffOn h hs c (formComponents A c) (hA c) v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have hsym : (fun w v => U w (v ∘ σ)) =ᶠ[𝓝 z] (fun w v => (-1 : ℝ) * U w v) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    funext v
    have hv : v = Fin.cons (v 0) ![v 1,v 2] := by
      funext i
      fin_cases i <;> rfl
    have hp : v ∘ σ = Fin.cons (v 0) ![v 2,v 1] := by
      funext i
      fin_cases i <;> simp [σ, Function.comp_def, Equiv.swap_apply_def]
    rw [hp, hv]
    simpa [U, covariantD_two, neg_one_mul] using
      covariantTwo_skew h A hA c hw (v 0) (v 1) (v 2)
  have hp := covariantD_signedPermutation_at h c U σ z (-1) hsmooth hsym a ![b,d,e]
  have hv : (![b,d,e] : Fin 3 → RIdx n) ∘ σ = ![b,e,d] := by
    funext i
    fin_cases i <;> simp [σ, Function.comp_def, Equiv.swap_apply_def]
  rw [hv] at hp
  simpa only [secondTwo, U, neg_one_mul, Matrix.Fin.cons_vecCons] using hp

theorem codifferential_exteriorTwo (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (d e : RIdx n) :
    codifferentialComponents h c (exteriorComponents (formComponents A c)) z ![d,e] =
      -∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b *
        (secondTwo h A c z a b d e - secondTwo h A c z a d b e +
          secondTwo h A c z a e b d) := by
  unfold codifferentialComponents
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [show Fin.cons b ![d,e] = (![b,d,e] : Fin 3 → RIdx n) from rfl,
    covariant_exteriorTwo h hs A hA c hz, secondTwo_skew h hs A hA c hz a d e b]
  ring

/-- The original computed Hodge expression before substituting curvature. -/
theorem hodgeTwo_eq_rough_add_commutators (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (d e : RIdx n) :
    hodgeComponents h c 2 (formComponents A c) z ![d,e] =
      roughTwoComponents h A c z ![d,e] +
        ∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b *
          ((secondTwo h A c z a d b e - secondTwo h A c z d a b e) -
            (secondTwo h A c z a e b d - secondTwo h A c z e a b d)) := by
  change exteriorComponents (codifferentialComponents h c (formComponents A c)) z ![d,e] +
    codifferentialComponents h c (exteriorComponents (formComponents A c)) z ![d,e] = _
  rw [exterior_codifferentialTwo h hs A hA c hz,
    codifferential_exteriorTwo h hs A hA c hz]
  simp only [roughTwoComponents, secondTwo, mul_sub, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- Weitzenböck for an arbitrary smooth real two-form: no type or closedness
hypothesis is used, and all coefficients are the frozen calculators. -/
theorem hodgeTwo_eq_rough_add_curvature (h : HermitianField M) (hs : MetricSmooth h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (I : Fin 2 → RIdx n) :
    hodgeComponents h c 2 (formComponents A c) z I =
      roughTwoComponents h A c z I + curvatureTwoComponents h A c z I := by
  have hI : I = ![I 0,I 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hI, hodgeTwo_eq_rough_add_commutators h hs A hA c hz]
  congr 1
  unfold curvatureTwoComponents
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [secondTwo_commutator h hs A hA c hz, secondTwo_commutator h hs A hA c hz]
  ring

end Yau.NodeProofs.P06Weitzenbock
