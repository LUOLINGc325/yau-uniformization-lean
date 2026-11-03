import spec.WORKPACKAGES.STATEMENTS.MASS.Statements
import spec.CHAIN.HeatScalarTargets

/-! Intrinsic scalar energy realization outputs. All spaces are fixed by the
actual scalar/exterior-derivative graph already used by the heat package. -/
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff Manifold ENNReal
noncomputable section
namespace Yau.MassTargetStatements
open Yau.Blueprint Yau.HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}

section Energy
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- A faithful completion of the SAME scalar d-graph. The one-half in the
one-form energy is the paper's actual scalar normalization. No independent
choice of gradient, norm, domain or pivot is an inlet. -/
def ScalarH10Binding (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (j : V →L[ℝ] FixedPivot μ O)
    (e : (M.Carrier → ℝ) → RealForm M 1 → V) : Prop :=
  Function.Injective j ∧
  (∀ f, ScalarTest O f → MemLp f 2 (μ.restrict O) ∧
    ∃ df, SmoothRealForm df ∧ RepresentsExterior (scalarZeroForm f) df ∧
      ScalarEnergyClosure g μ O f df) ∧
  (∀ f df v dv, ScalarEnergyClosure g μ O f df → ScalarEnergyClosure g μ O v dv →
    e (f + v) (df + dv) = e f df + e v dv) ∧
  (∀ (c : ℝ) f df, ScalarEnergyClosure g μ O f df →
    e (c • f) (c • df) = c • e f df) ∧
  (∀ u : V, ∃ f df, ScalarEnergyClosure g μ O f df ∧ e f df = u) ∧
  (∀ f df, ScalarEnergyClosure g μ O f df →
    ((j (e f df) : FixedPivot μ O) : M.Carrier → ℝ) =ᵐ[μ.restrict O] f) ∧
  (∀ f df v dv, ScalarEnergyClosure g μ O f df → ScalarEnergyClosure g μ O v dv →
    Integrable (fun x => f x * v x) (μ.restrict O) ∧
    Integrable (formInner g df dv) (μ.restrict O) ∧
    inner ℝ (e f df) (e v dv) =
      (∫ x in O, f x * v x ∂μ) + (∫ x in O, formInner g df dv x ∂μ) / 2) ∧
  (∀ f df v dv, ScalarEnergyClosure g μ O f df → ScalarEnergyClosure g μ O v dv →
    (e f df = e v dv ↔ f =ᵐ[μ.restrict O] v ∧
      ∀ᵐ x ∂μ.restrict O, df x = dv x)) ∧
  Dense {w : V | ∃ f df, ScalarTest O f ∧ SmoothRealForm df ∧
    RepresentsExterior (scalarZeroForm f) df ∧ ScalarEnergyClosure g μ O f df ∧ w = e f df}

abbrev EnergyDual (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] := V →L[ℝ] ℝ

/-- B is an OUTPUT extension of the actual nonsymmetric fixed-volume form.
The density and coefficient drift remain in Δ_ht; exactly ONE L² shift is used. -/
def IntrinsicFormBinding (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (h : ℝ → HermitianField M) (T C α shift : ℝ)
    (j : V →L[ℝ] FixedPivot μ O) (e : (M.Carrier → ℝ) → RealForm M 1 → V)
    (B : ℝ → V →L[ℝ] EnergyDual V) : Prop :=
  0 < C ∧ 0 < α ∧ 0 ≤ shift ∧
  (∀ u v : V, Measurable (fun t => B t u v)) ∧
  ∀ t ∈ Set.Icc 0 T,
    ‖B t‖ ≤ C ∧
    (∀ u : V, α * ‖u‖ ^ 2 ≤ B t u u + shift * ‖j u‖ ^ 2) ∧
    ∀ f df v dv, ScalarTest O f → ScalarTest O v →
      RepresentsExterior (scalarZeroForm f) df → RepresentsExterior (scalarZeroForm v) dv →
      ScalarEnergyClosure g μ O f df → ScalarEnergyClosure g μ O v dv →
      IntegrableOn (fun x => v x * laplacian (h t) f x) O μ ∧
      B t (e f df) (e v dv) = intrinsicTestForm μ O h t f v

/-- L²V, C([0,T];H), genuine L²V* distributional time derivative and zero
initial trace in the actual fixed pivot. The equation is tested against all V. -/
def VariationalSolution (μ : Measure M.Carrier) (O : Set M.Carrier) (T : ℝ)
    (j : V →L[ℝ] FixedPivot μ O) (B : ℝ → V →L[ℝ] EnergyDual V)
    (f : ℝ → FixedPivot μ O) (u : ℝ → V) (w : ℝ → EnergyDual V)
    (a : ℝ → FixedPivot μ O) : Prop :=
  MemLp u 2 (volume.restrict (Set.Ioo 0 T)) ∧
  MemLp w 2 (volume.restrict (Set.Ioo 0 T)) ∧ ContinuousOn a (Set.Icc 0 T) ∧
  a 0 = 0 ∧ (∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), a t = j (u t)) ∧
  (∀ v : V, ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
    tsupport η ⊆ Set.Ioo 0 T →
    (∫ t in Set.Ioo 0 T, η t * w t v) =
      -(∫ t in Set.Ioo 0 T, deriv η t * inner ℝ (a t) (j v))) ∧
  ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ v : V,
    w t v + B t (u t) v = inner ℝ (f t) (j v)

/-- Coefficient-dependent estimate and uniqueness for every L² source.
The constant precedes f; all solutions use the same actual V, j and B. -/
def VariationalEvolutionOutput (μ : Measure M.Carrier) (O : Set M.Carrier) (T E : ℝ)
    (j : V →L[ℝ] FixedPivot μ O) (B : ℝ → V →L[ℝ] EnergyDual V) : Prop :=
  0 < E ∧ ∀ f : ℝ → FixedPivot μ O, MemLp f 2 (volume.restrict (Set.Ioo 0 T)) →
    ∃ u w a, VariationalSolution μ O T j B f u w a ∧
      (∫ t in Set.Ioo 0 T, ‖u t‖ ^ 2 + ‖w t‖ ^ 2) ≤
        E * (∫ t in Set.Ioo 0 T, ‖f t‖ ^ 2) ∧
      (∀ t ∈ Set.Icc 0 T, ‖a t‖ ^ 2 ≤ E * (∫ s in Set.Ioo 0 T, ‖f s‖ ^ 2)) ∧
      ∀ v z b, VariationalSolution μ O T j B f v z b →
        (∀ t ∈ Set.Icc 0 T, a t = b t) ∧
        u =ᵐ[volume.restrict (Set.Ioo 0 T)] v
end Energy

/-- Full intrinsic-energy existence OUTPUT on the same finite actual domain.
No Hilbert space, form, weak solver or energy conclusion is a hypothesis. -/
def IntrinsicEnergyTarget (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) : Prop :=
  LocalizedFlow X o h U P ρ → ∀ μ, IsRiemannianVolume X.metric.form μ →
    ∀ O : Set (Pt X), SmoothPrecompactDomain O → ∀ T : ℝ, 0 < T →
      ∃ (V : Type) (nv : NormedAddCommGroup V),
        letI := nv
        ∃ iv : InnerProductSpace ℝ V,
          letI := iv
          ∃ cv : CompleteSpace V,
            letI := cv
            ∃ (j : V →L[ℝ] FixedPivot μ O)
              (e : (Pt X → ℝ) → RealForm X.manifold 1 → V)
              (B : ℝ → V →L[ℝ] EnergyDual V) (C α shift E : ℝ),
              ScalarH10Binding X.metric.form μ O j e ∧
              IntrinsicFormBinding X.metric.form μ O h T C α shift j e B ∧
              VariationalEvolutionOutput μ O T E j B
end Yau.MassTargetStatements
