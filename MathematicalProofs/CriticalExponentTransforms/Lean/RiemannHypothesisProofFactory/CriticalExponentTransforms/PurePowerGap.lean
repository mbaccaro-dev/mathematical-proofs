import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Real

namespace RiemannHypothesisProofFactory.CriticalExponentTransforms

abbrev PosReal := {x : ℝ // 0 < x}

noncomputable def powerMode (rho : ℝ) : PosReal → ℝ :=
  fun x => x.1 ^ rho

noncomputable def inputDilation (a : ℝ) (ha : 0 < a)
    (f : PosReal → ℝ) : PosReal → ℝ :=
  fun x => f ⟨a * x.1, mul_pos ha x.2⟩

noncomputable def outputDilation {V : Type*} (a : ℝ) (ha : 0 < a)
    (g : PosReal → V) : PosReal → V :=
  fun x => g ⟨a * x.1, mul_pos ha x.2⟩

theorem inputDilation_powerMode (a : ℝ) (ha : 0 < a) (rho : ℝ) :
    inputDilation a ha (powerMode rho) =
      fun x => (a ^ rho) * powerMode rho x := by
  funext x
  rw [inputDilation, powerMode, powerMode]
  exact Real.mul_rpow ha.le x.2.le

theorem pure_power_gap_law
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : (PosReal → ℝ) → PosReal → V)
    (q rho kappa : ℝ)
    (_hq : 0 < q)
    (hhom : ∀ (c : ℝ), 0 < c → ∀ f,
      T (fun x => c * f x) = fun x => (c ^ q) • T f x)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      T (inputDilation a ha f) =
        fun x => (a ^ kappa) • outputDilation a ha (T f) x) :
    (∀ x : PosReal,
      T (powerMode rho) x =
        (x.1 ^ (q * rho - kappa)) • T (powerMode rho) ⟨1, by positivity⟩) ∧
      (q * rho - kappa) - (q / 2 - kappa) = q * (rho - 1 / 2) := by
  constructor
  · intro x
    have hscale : 0 < x.1 ^ rho := Real.rpow_pos_of_pos x.2 rho
    have hdilate := congrFun
      (hcov x.1 x.2 (powerMode rho)) (⟨1, by positivity⟩ : PosReal)
    rw [inputDilation_powerMode] at hdilate
    rw [hhom (x.1 ^ rho) hscale (powerMode rho)] at hdilate
    simp only [outputDilation, mul_one] at hdilate
    have hkpos : 0 < x.1 ^ kappa := Real.rpow_pos_of_pos x.2 kappa
    apply smul_right_injective V (ne_of_gt hkpos)
    change (x.1 ^ kappa) • T (powerMode rho) x =
      (x.1 ^ kappa) •
        ((x.1 ^ (q * rho - kappa)) •
          T (powerMode rho) ⟨1, by positivity⟩)
    rw [← hdilate, smul_smul]
    congr 1
    rw [← Real.rpow_add x.2, ← Real.rpow_mul x.2.le]
    ring_nf
  · ring

end RiemannHypothesisProofFactory.CriticalExponentTransforms
